# -*- coding: utf-8 -*-
"""
install mythril and deploy source-dist and wheel to pypi.python.org

deps (requires up2date version):
    *) pip install --upgrade pip wheel setuptools twine
publish to pypi w/o having to convert Readme.md to RST:
    1) #> python setup.py sdist bdist_wheel
    2) #> twine upload dist/*   #<specify bdist_wheel version to upload>; #optional --repository <testpypi> or  --repository-url <testpypi-url>

"""
from setuptools import setup, find_packages
from setuptools.command.install import install
from pathlib import Path
import sys
import os

# To make lint checkers happy we set VERSION here, but
# it is redefined by the exec below
VERSION = None

# Package version (vX.Y.Z). It must match git tag being used for CircleCI
# deployment; otherwise the build will failed.

version_path = (Path(__file__).parent / "mythril" / "version.py").absolute()
exec(open(str(version_path), "r").read())


class VerifyVersionCommand(install):
    """Custom command to verify that the git tag matches our version"""

    description = "verify that the git tag matches our version"

    def run(self):
        tag = os.getenv("CIRCLE_TAG")

        if tag != VERSION:
            info = "Git tag: {0} does not match the version of this app: {1}".format(
                tag, VERSION
            )
            sys.exit(info)


def read_file(fname):
    """
    return file contents
    :param fname: path relative to setup.py
    :return: file contents
    """
    with open(os.path.join(os.path.dirname(__file__), fname), "r") as fd:
        return fd.read()


setup(
    name="mythril",
    version=VERSION[1:],
    description="Security analysis tool for Ethereum smart contracts",
    long_description=read_file("README.md") if os.path.isfile("README.md") else "",
    long_description_content_type="text/markdown",  # requires twine and recent setuptools
    url="https://github.com/b-mueller/mythril",
    author="Bernhard Mueller",
    author_email="bernhard.mueller11@gmail.com",
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
    install_requires=[
        "coloredlogs>=10.0",
        "ethereum>=2.3.2",
        "z3-solver>=4.8",
        "requests",
        "py-solc",
        "plyvel",
        "eth_abi>=1.0.0",
        "eth-utils>=1.0.1",
        "eth-account>=0.1.0a2",
        "eth-hash>=0.1.0",
        "eth-keyfile>=0.5.1",
        "eth-keys>=0.2.0b3",
        "eth-rlp>=0.1.0",
        "eth-tester>=0.1.0b21",
        "eth-typing>=1.3.0,<2.0.0",
        "coverage",
        "jinja2>=2.9",
        "rlp>=1.0.1",
        "transaction>=2.2.1",
        "py-flags",
        "mock",
        "configparser>=3.5.0",
        "persistent>=4.2.0",
        "ethereum-input-decoder>=0.2.2",
    ],
    tests_require=["pytest>=3.6.0", "pytest_mock", "pytest-cov"],
    python_requires=">=3.5",
    extras_require={},
    package_data={"mythril.analysis.templates": ["*"]},
    include_package_data=True,
    entry_points={"console_scripts": ["myth=mythril.interfaces.cli:main"]},
    cmdclass={"verify": VerifyVersionCommand},
)
