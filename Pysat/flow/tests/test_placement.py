import subprocess
from errors import scan_output

def placement_flow (test):
  output = subprocess.check_output('./flow-json.sh -n %s --script %s.py' % (test, test),
                                   shell=True,cwd='..')
  lines = output.decode("utf-8").split('\n')

  completed, fatals, errors, warnings, timing = scan_output (lines)
  print ("Test %s has %d fatals, %d errors %d warnings in %f time" %
         (test, fatals, errors, warnings, timing))
  print (lines)
  assert completed & (fatals + errors == 0)

def test_ctle_flow ():
  placement_flow("ctle")

def test_wcap_flow ():
  placement_flow("wcap")

def test_diff_flow ():
  placement_flow("diff")

def test_lane_flow ():
  placement_flow("lane")

def test_top_flow ():
  placement_flow("top")
  
