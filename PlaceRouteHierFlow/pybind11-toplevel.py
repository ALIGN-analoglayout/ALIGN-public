
import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)
from PnR import *

toplevel( ["pnr_compiler", "./testcase_example", "switched_capacitor_filter.lef",
           "switched_capacitor_filter.v",
           "switched_capacitor_filter.map",
           "layers.json", "switched_capacitor_filter",
           "2", "0"])
