from setuptools import setup, find_packages
from codecs import open
import os


here = os.path.abspath(os.path.dirname(__file__))

try:
    import pypandoc

    long_description = pypandoc.convert(os.path.join(here,'README.md'), 'rst')
except(IOError, ImportError):
# Get the long description from the README file
    with open(os.path.join(here, 'README.md'), encoding='utf-8') as f:
        long_description = f.read()


setup(
    name='mythril',

    version='0.1.1',

    description='Mythril is an assembler and disassembler for Ethereum VM bytecode',
    long_description=long_description,

    url='https://github.com/b-mueller/mythril',

    author='Bernhard Mueller',
    author_email='bernhard.mueller11@gmail.com',

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
