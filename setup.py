from setuptools import setup, find_packages
from codecs import open
from os import path

here = path.abspath(path.dirname(__file__))


try:
    import pypandoc
    long_description = pypandoc.convert('README.md', 'rst')
except(IOError, ImportError):
    long_description = open('README.md').read()


setup(
    name='mythril',

    version='0.1.0',

    description='Mythril is an assembler and disassembler for Ethereum VM bytecode',
    long_description=long_description,

    url='https://github.com/b-mueller/mythril',

    author='Bernhard Mueller',

    license='MIT',

    classifiers=[
        'Development Status :: 3 - Alpha',

        'Intended Audience :: Science/Research',
        'Topic :: Software Development :: Disassemblers',

        'License :: OSI Approved :: MIT License',

        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.3',
        'Programming Language :: Python :: 3.4',
        'Programming Language :: Python :: 3.5',
    ],

    keywords='hacking disassmbler ethereum',

    packages=find_packages(exclude=['contrib', 'docs', 'tests']),

    install_requires=[
        'ethereum==2.0.4',
    ],

    extras_require={
    },

    scripts=['mythril']
)