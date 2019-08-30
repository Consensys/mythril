# -*- coding: utf-8 -*-
"""install mythril and deploy source-dist and wheel to pypi.python.org.

deps (requires up2date version):
    *) pip install --upgrade pip wheel setuptools twine
publish to pypi w/o having to convert Readme.md to RST:
    1) #> python setup.py sdist bdist_wheel
    2) #> twine upload dist/*   #<specify bdist_wheel version to upload>; #optional --repository <testpypi> or  --repository-url <testpypi-url>
"""
from setuptools import setup, find_packages
from setuptools.command.install import install
import sys
import os
import io

# Package meta-data.
NAME = "mythril"
DESCRIPTION = "Security analysis tool for Ethereum smart contracts"
URL = "https://github.com/ConsenSys/mythril"
AUTHOR = "ConsenSys Dilligence"
AUTHOR_MAIL = None
REQUIRES_PYTHON = ">=3.5.0"


# What packages are required for this module to be executed?
REQUIRED = [
    "coloredlogs>=10.0",
    "py_ecc==1.4.2",
    "ethereum>=2.3.2",
    "z3-solver>=4.8.5.0",
    "requests>=2.22.0",
    "py-solc",
    "plyvel",
    "eth_abi==1.3.0",
    "eth-account>=0.1.0a2,<=0.3.0",
    "eth-hash>=0.1.0",
    "eth-keyfile>=0.5.1",
    "eth-keys>=0.2.0b3,<0.3.0",
    "eth-rlp>=0.1.0",
    "eth-tester==0.1.0b32",
    "eth-typing>=2.0.0",
    "coverage",
    "jinja2>=2.9",
    "rlp>=1.0.1",
    "transaction>=2.2.1",
    "py-flags",
    "mock",
    "configparser>=3.5.0",
    "persistent>=4.2.0",
    "ethereum-input-decoder>=0.2.2",
    "matplotlib",
    "pythx",
]

TESTS_REQUIRE = ["mypy", "pytest>=3.6.0", "pytest_mock", "pytest-cov"]

# What packages are optional?
EXTRAS = {
    # 'fancy feature': ['django'],
}

# If version is set to None then it will be fetched from __version__.py
VERSION = None

here = os.path.abspath(os.path.dirname(__file__))

# Import the README and use it as the long-description.
# Note: this will only work if 'README.md' is present in your MANIFEST.in file!
try:
    with io.open(os.path.join(here, "README.md"), encoding="utf-8") as f:
        long_description = "\n" + f.read()
except FileNotFoundError:
    long_description = DESCRIPTION


# Load the package's __version__.py module as a dictionary.
about = {}
if not VERSION:
    project_slug = NAME.lower().replace("-", "_").replace(" ", "_")
    with open(os.path.join(here, project_slug, "__version__.py")) as f:
        exec(f.read(), about)
else:
    about["__version__"] = VERSION


# Package version (vX.Y.Z). It must match git tag being used for CircleCI
# deployment; otherwise the build will failed.
class VerifyVersionCommand(install):
    """Custom command to verify that the git tag matches our version."""

    description = "verify that the git tag matches our version"

    def run(self):
        """"""
        tag = os.getenv("CIRCLE_TAG")

        if tag != about["__version__"]:
            info = "Git tag: {0} does not match the version of this app: {1}".format(
                tag, about["__version__"]
            )
            sys.exit(info)


setup(
    name=NAME,
    version=about["__version__"][1:],
    description=DESCRIPTION,
    long_description=long_description,
    long_description_content_type="text/markdown",  # requires twine and recent setuptools
    url=URL,
    author=AUTHOR,
    author_mail=AUTHOR_MAIL,
    license="MIT",
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Science/Research",
        "Topic :: Software Development :: Disassemblers",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3.5",
        "Programming Language :: Python :: 3.6",
        "Programming Language :: Python :: 3.7",
    ],
    keywords="hacking disassembler security ethereum",
    packages=find_packages(exclude=["contrib", "docs", "tests"]),
    install_requires=REQUIRED,
    tests_require=TESTS_REQUIRE,
    python_requires=REQUIRES_PYTHON,
    extras_require=EXTRAS,
    package_data={"mythril.analysis.templates": ["*"], "mythril.support.assets": ["*"]},
    include_package_data=True,
    entry_points={"console_scripts": ["myth=mythril.interfaces.cli:main"]},
    cmdclass={"verify": VerifyVersionCommand},
)
