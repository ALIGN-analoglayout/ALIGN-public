import os

from setuptools import setup, find_packages, Extension
import pybind11

def get_version(pkg_path):
    with open(os.path.join(pkg_path, '__init__.py'), 'r') as fp:
        for line in fp:
            if line.startswith('__version__'):
                return line.split('"' if '"' in line else "'")[1]

def get_readme_text():
    with open("README.md", "r", encoding="utf8") as fp:
        long_description = fp.read()
    return long_description

def get_PnR():

    SRC_FILES ={ # DIRECTORY,List[FILE]
        'PlaceRouteHierFlow/PnRDB': ['readfile.cpp', 'PnRdatabase.cpp', 'ReadDesignRule.cpp', 'ReadDesignRuleJson.cpp', 'HardDesignRule.cpp', 'WriteJSON.cpp', 'ReadVerilog.cpp', 'ReadConstraint.cpp', 'Print.cpp', 'ReadLEF.cpp', 'PnRDBJSON.cpp'],
        'PlaceRouteHierFlow/placer': ['design.cpp', 'SeqPair.cpp', 'ConstGraph.cpp', 'Aplace.cpp', 'Placer.cpp', 'ILP_solver.cpp', 'PlacerIfc.cpp'],
        'PlaceRouteHierFlow/router': ['RawRouter.cpp', 'Grid.cpp', 'GlobalGrid.cpp', 'Graph.cpp', 'A_star.cpp', 'GlobalGraph.cpp', 'GlobalRouter.cpp', 'GcellGlobalRouter.cpp', 'DetailRouter.cpp', 'GcellDetailRouter.cpp', 'PowerRouter.cpp', 'Router.cpp'],
        'PlaceRouteHierFlow/cap_placer': ['capplacer.cpp', 'CapPlacerIfc.cpp'],
        'PlaceRouteHierFlow/MNA': ['MNASimulation.cpp'],
        'PlaceRouteHierFlow/guard_ring': ['GuardRing.cpp', 'GuardRingIfc.cpp'],
        'PlaceRouteHierFlow': ['toplevel.cpp', 'PnR-pybind11.cpp']
    }

    return Extension(
        name='align.PnR',
        sources=[ \
            f'{d}/{f}' \
                for d, files in SRC_FILES.items() \
                    for f in files],
        include_dirs = list(SRC_FILES.keys()) + [ \
            pybind11.get_include(),
            os.environ['LP_DIR'] + '/lp_solve_5.5.2.5_dev_ux64',
            os.environ['JSON'] + '/include',
            os.environ['SPDLOG_DIR'] + '/include',
            os.environ['SuperLu_DIR'] + '/SuperLU_5.2.1/SRC'
        ],
        extra_objects=[
            os.environ['SuperLu_DIR'] + '/SuperLU_5.2.1/build/SRC/libsuperlu.a',
            os.environ['SuperLu_DIR'] + '/SuperLU_5.2.1/build/CBLAS/libblas.a'
        ],
        library_dirs = [
            os.environ['LP_DIR'] + '/lp_solve_5.5.2.5_dev_ux64'
        ],
        libraries = [
            'lpsolve55'
        ]
    )

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
          'pydantic>=1.8',
          'z3-solver',
          'more-itertools',
          'colorlog',
          'plotly'
          ],
      setup_requires=[],
      python_requires='~=3.8',
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
      ext_modules=[get_PnR()],
      zip_safe=False)
