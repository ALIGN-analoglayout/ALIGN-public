#!/usr/bin/env python

import sys
import pathlib
import subprocess
import shutil
import itertools

from coverage.cmdline import main

def main_wrapper():
    assert pathlib.Path.cwd().resolve() == pathlib.Path(__file__).parent.resolve(), \
        f"Please run {__file__} from ALIGN_HOME."
    argv = sys.argv[1:]

    output_dir = 'coverage-reports'

    c_coverage_file = 'coverage.info'
    build_dir = pathlib.Path.cwd() / 'build' / 'temp.linux-x86_64-3.8'

    # Detect whether to run LCOV
    GCOV_ENABLED = False
    if shutil.which('lcov') is None:
        print("WARNING: `lcov` not found. Generating coverage for python components only.")
    elif next(pathlib.Path.cwd().glob('**/build/temp.linux-x86_64-3.8/**/*.gcno'), None) is None:
        print("WARNING: Could not find any .gcno files. Generating coverage for python components only.")
        print("         Run pip with --editable & --install-option='--coverage' to view cpp coverage as well.")
    else:
        GCOV_ENABLED = True

    # LCOV init
    if GCOV_ENABLED:
        subprocess.run(' '.join([
            'lcov', '--directory', '.', '--zerocounters']),
            shell=True)

    # Actual command is run here
    subprocess.run(' '.join([
        'coverage', 'run', *argv]),
        shell=True)
    # status = main(['run'] + argv)

    # Finish capture
    if GCOV_ENABLED:
        ret = subprocess.run(' '.join([
            'lcov', '--capture',
            '--directory', '.',
            '--output-file', c_coverage_file]),
            shell=True)

    # Clean existing report (if any)
    shutil.rmtree(output_dir)

    # Generate report
    status = main(['html', '-d', f'{output_dir}/python'])
    if GCOV_ENABLED:
        subprocess.run(
            ' '.join([
                'lcov', '--remove', c_coverage_file,
                '/usr/include/*',
                '*/include/pybind11/*',
                '*/include/spdlog/*',
                '*/include/nlohmann/*',
                '*/include/gtest/*',
                '--output-file', c_coverage_file]),
                shell=True)
        subprocess.run(' '.join([
            'genhtml', c_coverage_file,
            '--output-directory',  f'{output_dir}/cpp',
            '--no-branch-coverage',
            '--title', '"CPP lcov report"']), shell=True)

if __name__ == '__main__':
    main_wrapper()