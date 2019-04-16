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
   

def rollup_test (test):
    fn = test + ".log"
    completed = False
    timing = 0.0
    fatals = 0
    errors = 0
    warnings = 0
    if os.path.isfile(fn):
        with open (fn, "rt") as fp:
            line = fp.readline ()
            accumulate = False
            while line:
                key,match = parse_line(line)
                if key == 'all':         accumulate = True
                if accumulate:
                    if key == 'fatal':
                        fatals += 1
#                        print "FATAL %s %d" % (test, line)
                    if key == 'error':
                        errors += 1
#                        print "ERROR %s %d" % (test, line)
                    if key == 'warning': warnings += 1
                    if key == 'time':
                        completed = True
                        timing = float(match.group(1))
                line = fp.readline ()
    else:
        fatals += 1
    return test, completed, fatals, errors, warnings, timing

def main():
    testsuite = "bottom-up"
    completed = 0
    fatals = 0
    errors = 0
    warnings = 0
    totTiming = 0.0
    if len(sys.argv) > 1:
        num_tests = len(sys.argv)-1
        for i in range(1, len(sys.argv)):
            test = sys.argv[i]
            res = rollup_test(test)
            completed += res[1]
            fatals += res[2]
            errors += res[3]
            warnings += res[4]
            totTiming += res[5]

        print ("<testsuites name=\"End-to-end tests\" tests=\"%d\" failures=\"%d\">" %(num_tests, fatals + errors))
        print ("\t<testsuite name=\"%s\" errors=\"%d\" failures=\"%d\" skipped=\"%d\" tests=\"%d\">" % (testsuite, errors, fatals, num_tests-completed, num_tests))
        for i in range(1, len(sys.argv)):
            test = sys.argv[i]
            res = rollup_test(test)
            timing = res[5]
            print ("\t\t<testcase classname=\"%s\" name=\"%s\" time=\"%f\"> </testcase>" % (test, test,timing))
        print ("\t</testsuite>")
        print ("</testsuites>")
    
if __name__ == "__main__":
    main()
