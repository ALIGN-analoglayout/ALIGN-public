from distutils.core import setup, find_packages

setup(
    name='sub_circuit_identification',
    version='0.1',
    packages=['src',],
    author='Kishor Kunal',
    packages=find_packages(),
    author_email='kunal001@umn.edu',
    license='BSD 3',
    long_description=open('README.md').read(),
)
