import os

from setuptools import setup, find_packages

def get_version(pkg_path):
    with open(os.path.join(pkg_path, '__init__.py'), 'r') as fp:
        for line in fp:
            if line.startswith('__version__'):
                return line.split('"' if '"' in line else "'")[1]

def get_readme_text():
    with open("README.md", "r", encoding="utf8") as fp:
        long_description = fp.read()
    return long_description

setup(name='align',
      version=get_version(
            os.path.join(
                  os.path.abspath(os.path.dirname(__file__)),
                  'align')),
      description='Analog Layout Synthesis Package',
      long_description=get_readme_text(),
      long_description_content_type="text/markdown",
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Parijat Mukherjee',
      author_email='parijat.mukherjee@intel.com',
      license='BSD-3-Clause',
      packages=find_packages(include=['align', 'align.*']),
      package_data={'align': ['config/*']},
      scripts=[
          'bin/schematic2layout.py',
          'bin/gds2png.sh'
      ],
      install_requires=[
          'networkx>=2.4',
          'python-gdsii',
          'matplotlib',
          'pyyaml',
          'pybind11',
          'pydantic',
          'typing-extensions',
          'z3-solver'
          ],
      setup_requires=['pytest-runner'],
      python_requires='~=3.6',
      classifiers=[
          'Development Status :: 2 - Pre-Alpha',
          'Environment :: Console',
          'Intended Audience :: Science/Research',
          'License :: OSI Approved :: BSD License',
          'Operating System :: OS Independent',
          'Programming Language :: Python :: 3.6',
          'Programming Language :: C++',
          'Topic :: Scientific/Engineering :: Electronic Design Automation (EDA)'
      ],
      zip_safe=False)
