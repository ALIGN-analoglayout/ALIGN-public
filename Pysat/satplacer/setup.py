from setuptools import setup, find_packages

setup(name='satplacer',
      version='0.1',
      description='Simple SAT-based Placer',
      url='ALIGN-analoglayout/ALIGN.git',
      author='Steven Burns',
      author_email='steven.m.burns@intel.com',
      license='MIT',
      packages=find_packages(),
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      zip_safe=False)
