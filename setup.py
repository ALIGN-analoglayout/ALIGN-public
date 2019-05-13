from setuptools import setup, find_packages

setup(name='Cell_Fabric_Common',
      version='0.1',
      description='Fabric generator infrastructure',
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Steven Burns',
      author_email='steven.m.burns@intel.com',
      license='MIT',
      packages=find_packages(),
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      zip_safe=False)
