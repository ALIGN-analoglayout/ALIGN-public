from setuptools import setup, find_packages

setup (name='gdsconv',
       version='0.1',
       description='GDS conversion scripts',
       url='ALIGN-analoglayout/ALIGN-public.git',
       author='Desmond A. Kirkpatrick',
       author_email='desmond.a.kirkpatrick@intel.com',
       license='MIT',
       packages=find_packages(),
       setup_requires=["pytest-runner"],
       tests_require=["pytest"],
       zip_safe=False)
