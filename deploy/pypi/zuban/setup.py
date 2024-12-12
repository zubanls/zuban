#!/usr/bin/env python

from setuptools import setup, find_packages

__AUTHOR__ = 'David Halter'
__AUTHOR_EMAIL__ = 'info@zubanls.com'

readme = open('README.rst').read() + '\n\n' + open('CHANGELOG.rst').read()

setup(
    name='zuban',
    version='0.0.2',
    description='ZubanLS - The Zuban Language Server',
    author=__AUTHOR__,
    author_email=__AUTHOR_EMAIL__,
    include_package_data=True,
    maintainer=__AUTHOR__,
    maintainer_email=__AUTHOR_EMAIL__,
    url='https://github.com/zubanls/zuban',
    license='Proprietary',
    keywords='typechecking mypy static analysis autocompletion',
    long_description=readme,
    packages=find_packages(exclude=['test']),
    #package_data={'zuban': []},
    python_requires='>=3.4',
    #platforms=['any'],
    classifiers=[
        'Development Status :: 1 - Planning',
        'Environment :: Plugins',
        'Intended Audience :: Developers',
        'License :: Other/Proprietary License',
        'Programming Language :: Python :: 3',
        'Topic :: Software Development :: Libraries :: Python Modules',
        'Topic :: Text Editors :: Integrated Development Environments (IDE)',
        'Topic :: Utilities',
        'Typing :: Typed',
    ],
)
