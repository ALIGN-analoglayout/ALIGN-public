from setuptools import setup, find_packages

setup(name='Circuit',
      version='0.1',
      description='Netlist management infrastructure',
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Parijat Mukherjee',
      author_email='parijat.mukherjee@intel.com',
      license='MIT',
      packages=find_packages(),
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      zip_safe=False)
