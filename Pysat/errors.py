import sys
import os
import re

rx_dict = {
    'fatal' : re.compile(r'-FATAL-'),
    'warning' : re.compile(r'-ISSUE-'),
    'error' : re.compile(r'-ERROR-'),
    'all' : re.compile(r'All ISSUE messages:') # Start of error summary in file
    }

def parse_line (line):
    for key,rx in rx_dict.items():
        match = rx.search(line)
        if match:
            return key, match
    return None,None
   

def rollup_test (test):
    test = sys.argv[1]
    fn = test + ".log"
    fatals = 0
    errors = 0
    warnings = 0
    if os.path.isfile(fn):
        with open (fn, "rt") as fp:
            line = fp.readline ()
            rx = re.compile
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
                line = fp.readline ()
    else:
        print("Could not open %s" % fn)
        fatals += 1
#    print "Returning %d %d %d" %( fatals, errors, warnings)
    return test, fatals, errors, warnings

def main():
    testsuite = "bottom-up"
    fatals = 0
    errors = 0
    warnings = 0
    if len(sys.argv) > 1:
        num_tests = len(sys.argv)-1
        for i in range(1, len(sys.argv)):
            test = sys.argv[i]
            res = rollup_test(test)
            fatals += res[1]
            errors += res[2]
            warnings += res[3]

        print ("<testsuites name=\"End-to-end tests\" tests=\"%d\" failures=\"%d\">" %(num_tests, fatals + errors))
        print ("\t<testsuite name=\"%s\" errors=\"%d\" failures=\"%d\" skipped=\"0\" tests=\"%d\">" % (testsuite, errors, fatals, num_tests))
        for i in range(1, len(sys.argv)):
            test = sys.argv[i]
            print ("\t\t<testcase classname=\"%s\" name=\"%s\"> </testcase>" % (test, test))
        print ("\t</testsuite>")
        print ("</testsuites>")
    
if __name__ == "__main__":
    main()
