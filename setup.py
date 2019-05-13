from setuptools import setup, find_packages

setup(name='Cell_Fabric_14nm_Mock',
      version='0.1',
      description='Fabric generators for 14nm Mock library',
      url='ALIGN-analoglayout/ALIGN.git',
      author='Steven Burns',
      author_email='steven.m.burns@intel.com',
      license='MIT',
      packages=find_packages(),
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      zip_safe=False)
