from setuptools import setup, find_packages

setup(name='primitives',
      version='0.1',
      description='Primitive Layout Generators',
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Steven Burns',
      author_email='steven.m.burns@intel.com',
      license='MIT',
      packages=find_packages(),
      entry_points={
          'console_scripts': [
              'primitives = primitives.__main__:main'
              ]
      },
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      zip_safe=False)
