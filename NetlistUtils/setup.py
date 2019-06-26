from setuptools import setup, find_packages

setup(name='NetlistUtils',
      version='0.1',
      description='Netlist parser / generator utilities',
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Parijat Mukherjee',
      author_email='parijat.mukherjee@intel.com',
      license='MIT',
      packages=find_packages(),
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      zip_safe=False)
