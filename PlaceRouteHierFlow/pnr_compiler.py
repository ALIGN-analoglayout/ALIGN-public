#!/usr/bin/env python

import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)
from PnR import *

toplevel( sys.argv)
