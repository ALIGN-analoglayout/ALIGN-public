import subprocess
from errors import scan_output

def single_flow (test):
  output = subprocess.check_output(['./flow-json.sh', '-n',  test], cwd='..')
  lines = output.decode("utf-8").split('\n')

  completed, fatals, errors, warnings, timing = scan_output (lines)
  print ("Test %s has %d fatals, %d errors %d warnings in %f time" %
         (test, fatals, errors, warnings, timing))
  assert completed & (fatals + errors == 0)

def placement_flow (test):
  scr = "%s.py" % test
  output = subprocess.check_output(['./flow-json.sh', '-n', test, '--script', scr], cwd='..')
  lines = output.decode("utf-8").split('\n')

  completed, fatals, errors, warnings, timing = scan_output (lines)
  print ("Test %s has %d fatals, %d errors %d warnings in %f time" %
         (test, fatals, errors, warnings, timing))
  assert completed & (fatals + errors == 0)

# def test_dp1x_flow ():
#   single_flow("dp1x")

# def test_dp2x_flow ():
#   single_flow("dp2x")

# def test_dp4x_flow ():
#   single_flow("dp4x")

# def test_mirrors_flow ():
#   single_flow("mirrors")

def test_ctle_flow ():
  placement_flow("ctle")

# def test_wcap_flow ():
#   placement_flow("wcap")

# def test_comp_flow ():
#   placement_flow("comp")

# def test_diff_flow ():
#   placement_flow("diff")

# def test_lane_flow ():
#   placement_flow("lane")

# def test_top_flow ():
#   placement_flow("top")
