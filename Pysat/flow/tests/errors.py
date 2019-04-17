import sys
import os
import re

rx_dict = {
    'fatal' : re.compile(r'-FATAL-'),
    'warning' : re.compile(r'-ISSUE-'),
    'error' : re.compile(r'-ERROR-'),
    'time' : re.compile(r'Total time:\s*(\d*\.\d+|\d+)'),
    'all' : re.compile(r'All ISSUE messages:') # Start of error summary in file
    }

def parse_line (line):
    for key,rx in rx_dict.items():
        match = rx.search(line)
        if match:
            return key, match
    return None,None

def scan_output (lines):
    completed = False
    timing = 0.0
    fatals = 0
    errors = 0
    warnings = 0
    accumulate = False
    for line in lines:
        key,match = parse_line(line)
        if key == 'all':         accumulate = True
        if accumulate:
            if key == 'fatal':   fatals += 1
            if key == 'error':   errors += 1
            if key == 'warning': warnings += 1
            if key == 'time':
                completed = True
                timing = float(match.group(1))
    return completed, fatals, errors, warnings, timing
