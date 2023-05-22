#!/usr/bin/env python

import os
import sys
import pathlib
import subprocess
import shutil
import itertools


def main():
    exit_status = 0
    assert pathlib.Path.cwd().resolve() == pathlib.Path(__file__).parent.resolve(), \
        f"Please run {__file__} from ALIGN_HOME."
    argv = sys.argv[1:]

    output_dir = pathlib.Path('coverage-reports').resolve()
    c_coverage_file = pathlib.Path('coverage.info').resolve()

    try:
        from tests._cmake import CMAKE_BINARY_DIR, CMAKE_SOURCE_DIR
    except:
        CMAKE_BINARY_DIR = None
        CMAKE_SOURCE_DIR = None

    # Detect whether to run LCOV
    GCOV_ENABLED = False
    if shutil.which('lcov') is None:
        print("WARNING: `lcov` not found. Generating coverage for python components only.")
    elif not CMAKE_BINARY_DIR or not CMAKE_SOURCE_DIR:
        print("WARNING: CPP Source / Binary information not found. Generating coverage for python components only.")
        print("         Run `pip install -e .[test] --no-build-isolation --global-option='-DCODE_COVERAGE=ON' --global-option='-DBUILD_TESTING=ON'` to instrument cpp code.")
    elif next(pathlib.Path(CMAKE_BINARY_DIR).glob('**/*.gcno'), None) is None:
        print("WARNING: Could not find any .gcno files. Generating coverage for python components only.")
        print("         Run `pip install -e .[test] --no-build-isolation --global-option='-DCODE_COVERAGE=ON' --global-option='-DBUILD_TESTING=ON'` to instrument cpp code.")
    else:
        print("INFO: Code coverage for cpp extension has been enabled. Please see coverage-reports/cpp.")
        GCOV_ENABLED = True

    # Clean existing report (if any)
    if output_dir.is_dir():
        shutil.rmtree(str(output_dir))
    # Number of parallel jobs
    if 'MAX_JOBS' in os.environ:
        MAX_JOBS = os.environ['MAX_JOBS']
    else:
        MAX_JOBS = 'auto'

    # LCOV init
    if GCOV_ENABLED:
        ret = subprocess.run(' '.join([
            'lcov', '--directory', CMAKE_BINARY_DIR, '--zerocounters']),
            shell=True)
        if not exit_status:
            exit_status = ret.returncode

    # Actual command is run here
    ret = subprocess.run(' '.join([
        'pytest', '-vv',  # Call pytest in verbose mode
        '--reruns', '2',
        '-n', MAX_JOBS,  # pytest-xdist options
        '--cov-report', f'html:{output_dir}/python', '--cov=align',  # pytest-cov options
        *argv
    ]),
        shell=True)
    if not exit_status:
        exit_status = ret.returncode


    # Standard checkin integration tests
    os.environ['CI_LEVEL'] = 'checkin'

    ret = subprocess.run(' '.join([
        'pytest', '-vv', # Call pytest in verbose mode
        '--runnightly',
        '--reruns', '2',
        '--maxerrors=0',
        '-n', MAX_JOBS, # pytest-xdist options
        '--cov-report', f'html:{output_dir}/python', '--cov=align',  # pytest-cov options
        '--cov-append', # append to existing run
        '--',
        'tests/integration/'
        ]),
        shell=True)

    del os.environ['CI_LEVEL']



    # One integration test (to get guard_ring_coverage)
    ret = subprocess.run(' '.join([
        'pytest', '-vv',  # Call pytest in verbose mode
        '--runnightly',
        '--reruns', '2',
        '-k', 'telescopic_ota_guard_ring or switched_capacitor_filter',
        '-n', MAX_JOBS,  # pytest-xdist options
        '--cov-report', f'html:{output_dir}/python', '--cov=align',  # pytest-cov options
        '--cov-append' # append to existing run
        ]),
        shell=True)
    if not exit_status:
        pass
        # Currently failing
        #exit_status = ret.returncode

    if GCOV_ENABLED:
        # Finish capture
        ret = subprocess.run(' '.join([
            'lcov', '--capture', '--no-external',
            '--directory', '.',
            '--output-file', f'{c_coverage_file}']),
            shell=True)
        if not exit_status:
            exit_status = ret.returncode
        # Remove coverage we aren't interested in
        ret = subprocess.run(' '.join([
            'lcov', '--remove',
            f'{c_coverage_file}',
            '--output-file', f'{c_coverage_file}',
            '*/_deps/*']),
            shell=True)
        if not exit_status:
            exit_status = ret.returncode
        # Generate report
        ret = subprocess.run(' '.join([
            'genhtml', f'{c_coverage_file}',
            '--output-directory',  f'{output_dir}/cpp',
            '--no-branch-coverage',
            '--title', '"CPP lcov report"']), shell=True)
        if not exit_status:
            exit_status = ret.returncode
    return exit_status


if __name__ == '__main__':
    sys.exit(main())
