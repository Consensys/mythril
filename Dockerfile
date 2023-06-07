# syntax=docker/dockerfile:1
ARG PYTHON_VERSION=3.10
ARG INSTALLED_SOLC_VERSIONS


FROM python:${PYTHON_VERSION:?} AS python-wheel
WORKDIR /wheels


FROM python-wheel AS python-wheel-with-cargo
# Enable cargo sparse-registry to prevent it using large amounts of memory in
# docker builds, and speed up builds by downloading less.
# https://github.com/rust-lang/cargo/issues/10781#issuecomment-1163819998
ENV CARGO_UNSTABLE_SPARSE_REGISTRY=true

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH=/root/.cargo/bin:$PATH


# z3-solver needs to build from src on arm, and it takes a long time, so
# building it in a separate stage helps parallelise the build and helps it stay
# in the build cache.
FROM python-wheel AS python-wheel-z3-solver
RUN pip install auditwheel
RUN --mount=source=requirements.txt,target=/run/requirements.txt \
  pip wheel "$(grep z3-solver /run/requirements.txt)"
# The wheel z3-solver builds does not install in arm64 because it generates
# incorrect platform compatibility metadata for arm64 builds. (It uses the
# platform manylinux1_aarch64 but manylinux1 is only defined for x86 systems,
# not arm: https://peps.python.org/pep-0600/#legacy-manylinux-tags). To work
# around this, we use pypa's auditwheel tool to infer and apply a compatible
# platform tag.
RUN ( auditwheel addtag ./z3_solver-* \
      # replace incorrect wheel with the re-tagged one
      && rm ./z3_solver-* && mv wheelhouse/z3_solver-* . ) \
    # addtag exits with status 1 if no tags need adding, which is fine
    || true


FROM python-wheel-with-cargo AS python-wheel-blake2b
# blake2b-py doesn't publish ARM builds, and also don't publish source packages
# on PyPI (other than the old 0.1.3 version) so we need to build from from a git
# tag. They do publish binaries for linux amd64, but their binaries only support
# certain platform versions and the amd64 python image isn't supported, so we
# have to build from src for that as well.

# Try to get a binary build or a source release on PyPI first, then fall back
# to building from the git repo.
RUN pip wheel 'blake2b-py>=0.2.0,<1' \
  || pip wheel git+https://github.com/ethereum/blake2b-py.git@v0.2.0


FROM python-wheel AS mythril-wheels
# cython is needed to build some wheels, such as cytoolz
RUN pip install cython
RUN --mount=source=requirements.txt,target=/run/requirements.txt \
  # ignore blake2b and z3-solver as we've already built them
  grep -v -e blake2b -e z3-solver /run/requirements.txt > /tmp/requirements-remaining.txt
RUN pip wheel -r /tmp/requirements-remaining.txt

COPY . /mythril
RUN pip wheel --no-deps /mythril

COPY --from=python-wheel-blake2b /wheels/blake2b* /wheels
COPY --from=python-wheel-z3-solver /wheels/z3_solver* /wheels


# Solidity Compiler Version Manager. This provides cross-platform solc builds.
# It's used by foundry to provide solc. https://github.com/roynalnaruto/svm-rs
FROM python-wheel-with-cargo AS solidity-compiler-version-manager
RUN cargo install svm-rs
# put the binaries somewhere obvious for later stages to use
RUN mkdir -p /svm-rs/bin && cd ~/.cargo/bin/ && cp svm solc /svm-rs/bin/


FROM python:${PYTHON_VERSION:?}-slim AS myth
ARG PYTHON_VERSION
# Space-separated version string without leading 'v' (e.g. "0.4.21 0.4.22")
ARG INSTALLED_SOLC_VERSIONS

COPY --from=solidity-compiler-version-manager /svm-rs/bin/* /usr/local/bin/

RUN --mount=from=mythril-wheels,source=/wheels,target=/wheels \
  export PYTHONDONTWRITEBYTECODE=1 && pip install /wheels/*.whl

RUN adduser --disabled-password mythril
USER mythril
WORKDIR /home/mythril

# pre-install solc versions
RUN set -x; [ -z "${INSTALLED_SOLC_VERSIONS}" ] || svm install ${INSTALLED_SOLC_VERSIONS}

COPY --chown=mythril:mythril \
  ./mythril/support/assets/signatures.db \
  /home/mythril/.mythril/signatures.db

COPY --chown=root:root --chmod=755 ./docker/docker-entrypoint.sh /
COPY --chown=root:root --chmod=755 \
  ./docker/sync-svm-solc-versions-with-solcx.sh \
  /usr/local/bin/sync-svm-solc-versions-with-solcx
ENTRYPOINT ["/docker-entrypoint.sh"]


# Basic sanity checks to make sure the build is functional
FROM myth AS myth-smoke-test-execution
SHELL ["/bin/bash", "-euo", "pipefail", "-c"]
WORKDIR /smoke-test
COPY --chmod=755 <<"EOT" /smoke-test.sh
#!/usr/bin/env bash
set -x -euo pipefail

# Check solcx knows about svm solc versions
svm install 0.5.0
sync-svm-solc-versions-with-solcx
python -c '
import solcx
print("\n".join(str(v) for v in solcx.get_installed_solc_versions()))
' | grep -P '^0\.5\.0$' || {
  echo "solcx did not report svm-installed solc version";
  exit 1
}

# Check myth can run
myth version
myth function-to-hash 'function transfer(address _to, uint256 _value) public returns (bool success)'
myth analyze /solidity_examples/origin.sol -t 1 > origin.log || true
grep 'SWC ID: 115' origin.log || {
  error "Failed to detect SWC ID: 115 in origin.sol";
  exit 1
}

# Check that the entrypoint works
[[ $(/docker-entrypoint.sh version) == $(myth version) ]]
[[ $(/docker-entrypoint.sh echo hi) == hi ]]
[[ $(/docker-entrypoint.sh bash -c "printf '>%s<' 'foo bar'") == ">foo bar<" ]]
EOT

RUN --mount=source=./solidity_examples,target=/solidity_examples \
  /smoke-test.sh 2>&1 | tee smoke-test.log


FROM scratch as myth-smoke-test
COPY --from=myth-smoke-test-execution /smoke-test/* /
