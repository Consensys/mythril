from setuptools import setup, find_packages


long_description = '''

'''


setup(
    name='mythril',

    version='0.2.4',

    description='A bug hunting tool framework for the Ethereum blockchain',
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

    keywords='hacking disassembler security ethereum',

    packages=find_packages(exclude=['contrib', 'docs', 'tests']),

    install_requires=[
        'ethereum>=2.0.4',
        'ZODB>=5.3.0'
    ],

    python_requires='>=3.5',

    extras_require={
    },

    scripts=['mythril/mythril']
)
