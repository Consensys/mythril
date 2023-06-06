#!/usr/bin/env bash
set -euo pipefail

# Install extra solc versions if SOLC is set
if [[ ${SOLC:-} != "" ]]; then
    read -ra solc_versions <<<"${SOLC:?}"
    svm install "${solc_versions[@]}"
fi
# Always sync versions, as the should be at least one solc version installed
# in the base image, and we may be running as root rather than the mythril user.
sync-svm-solc-versions-with-solcx

# By default we run myth with options from arguments we received. But if the
# first argument is a valid program, we execute that instead so that people can
# run other commands without overriding the entrypoint (e.g. bash).
if command -v "${1:-}" > /dev/null; then
    exec -- "$@"
fi
exec -- myth "$@"
