from setuptools import setup, find_packages

setup(name='flow',
      version='0.1',
      description='End to end flows for various test circuits',
      url='ALIGN-analoglayout/ALIGN.git',
      author='Steven Burns',
      author_email='steven.m.burns@intel.com',
      license='MIT',
      packages=find_packages(),
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      zip_safe=False)
