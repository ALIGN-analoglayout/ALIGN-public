import sys
import os

try:
    from skbuild import setup
    from setuptools import find_packages
except ImportError:
    raise AssertionError("Use pip 10+, or install pyproject.toml requirements yourself")


def get_version(pkg_path):
    with open(os.path.join(pkg_path, '__init__.py'), 'r') as fp:
        for line in fp:
            if line.startswith('__version__'):
                return line.split('"' if '"' in line else "'")[1]


def get_readme_text():
    with open("README.md", "r", encoding="utf8") as fp:
        long_description = fp.read()
    return long_description


def align_manifest_filter(cmake_manifest):
    '''
    Pick out all generated *.so* & test_* files
    '''
    return list(filter(lambda name: 'test_' in name or '.so' in name or '.py' in name, cmake_manifest))


version = get_version(
    os.path.join(
        os.path.abspath(os.path.dirname(__file__)),
        'align'))
cmake_args = [f"-DALIGN_VERSION:string={version}"]

# Enable unit-tests for all in-place builds (pip install -e . --no-build-isolation)
devmode = 'develop' in sys.argv
if devmode:
    build_type = os.environ.get("BUILD_TYPE", None)
    if build_type: sys.argv.extend(['--build-type', build_type])
    else: sys.argv.extend(['--build-type', 'Debug'])
build_testing = os.environ.get('BUILD_TESTING', None)
if build_testing and build_testing == 'ON':
    cmake_args.append("-DBUILD_TESTING=ON")
code_coverage = os.environ.get('CODE_COVERAGE', None)
if code_coverage and code_coverage == 'ON':
    cmake_args.append("-DCODE_COVERAGE=ON")

# if devmode and not any(x.startswith('-DBUILD_TESTING') for x in sys.argv):
#     cmake_args.append('-DBUILD_TESTING=ON')

setup(name='align',
      version=version,
      description='Analog Layout Synthesis Package',
      long_description=get_readme_text(),
      long_description_content_type="text/markdown",
      url='ALIGN-analoglayout/ALIGN-public.git',
      author='Parijat Mukherjee',
      author_email='parijat.mukherjee@intel.com',
      license='BSD-3-Clause',
      packages=find_packages(include=['align', 'align.*'])
      + (['tests'] if devmode else []),
      package_data={
          'align': [
              'config/*',
              'pdk/finfet/*.json',
              'pdk/finfet/*.sp'
          ]
      },
      cmake_args=cmake_args,
      cmake_process_manifest_hook=align_manifest_filter,
      scripts=[
          'bin/schematic2layout.py',
          'bin/gds2png.sh',
          'bin/analyze_regression.py',
          'bin/convert_lef_to_layout_json.py',
          'bin/gen_gds_from_json.py',
          'bin/gen_lef_with_obs.py',
          'bin/gen_primitive_from_gds.py'
      ],
      install_requires=[
          'networkx>=2.4',
          'python-gdsii',
          'gdspy',
          'pyyaml',
          'pybind11',
          'pydantic>=1.9.2,<=1.20',
          'z3-solver',
          'mip',
          'more-itertools',
          'colorlog',
          'plotly',
          'numpy',
          'pandas',
          'werkzeug',
          'dash',
          'typing_extensions; python_version<"3.8"',
          'memory_profiler',
          'flatdict',
          'mip'
      ],
      extras_require={
          'test': [
              'pytest',
              'pytest-cov',
              'pytest-xdist',
              'pytest-timeout',
              'pytest-rerunfailures',
              'pytest-cpp'
          ]
      },
      python_requires='>=3.7',
      classifiers=[
          'Development Status :: 2 - Pre-Alpha',
          'Environment :: Console',
          'Intended Audience :: Science/Research',
          'License :: OSI Approved :: BSD License',
          'Operating System :: OS Independent',
          'Programming Language :: Python :: 3.8',
          'Programming Language :: C++',
          'Topic :: Scientific/Engineering :: Electronic Design Automation (EDA)'
      ],
      zip_safe=False)
