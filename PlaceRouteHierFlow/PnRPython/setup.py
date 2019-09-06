from setuptools import setup, find_packages

setup(name='pnrdb',
      version='0.1',
      description='PnR database python view',
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Steven Burns',
      author_email='steven.m.burns@intel.com',
      license='MIT',
      packages=find_packages(),
      setup_requires=["pytest-runner"],
      tests_require=["pytest"],
      scripts=['gen_viewer_json.py'],
      zip_safe=False)
