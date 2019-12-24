import os

from setuptools import setup, find_packages

def get_version(pkg_path):
    with open(os.path.join(pkg_path, '__init__.py'), 'r') as fp:
        for line in fp:
            if line.startswith('__version__'):
                return line.split('"' if '"' in line else "'")[1]

setup(name='align',
      version=get_version(
            os.path.join(
                  os.path.abspath(os.path.dirname(__file__)),
                  'align')),
      description='Analog Layout Synthesis Package',
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Parijat Mukherjee',
      author_email='parijat.mukherjee@intel.com',
      license='BSD-3-Clause',
      packages=find_packages(include=['align', 'align.*']),
      install_requires=['networkx>=2.4'],
      setup_requires=['pytest-runner'],
      tests_require=['pytest'],
      python_requires='~=3.6',
      zip_safe=False)
