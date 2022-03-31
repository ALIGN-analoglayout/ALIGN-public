from setuptools import setup, find_packages

setup(name='tally',
      version='0.1',
      description='Wrappers to build circuits in SAT',
      url='ALIGN-analoglayout/ALIGN.git',
      author='Steven Burns',
      author_email='steven.m.burns@intel.com',
      license='MIT',
      packages=find_packages(),
      install_requires=["python-sat"],
      setup_requires=["pytest-runner"],
      tests_require=["pytest","hypothesis"],
      zip_safe=False)
