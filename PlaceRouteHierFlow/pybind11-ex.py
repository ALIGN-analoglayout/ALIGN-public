
#
# g++ -I ../json/include -I ../lpsolve/lp_solve_5.5 -I ../lpsolve/lp_solve_5.5.2.5_dev_ux64 -O3 -Wall -shared -std=c++11 -fPIC `python -m pybind11 --includes` PnR-pybind11.cpp -o PnR`python3-config --extension-suffix` toplevel.o cap_placer/cap_placer.a placer/placer.a router/router.a PnRDB/PnRDB.a ../googletest/googletest/mybuild/lib/libgtest.so
# LD_LIBRARY_PATH=$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/:`realpath ../googletest/googletest/mybuild/lib/` python
#

import sys, os
sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)
from PnR import *

DB = PnRdatabase( "./testcase_example", "switched_capacitor_filter", "switched_capacitor_filter.v", "switched_capacitor_filter.lef", "switched_capacitor_filter.map", "layers.json")

lefs = DB.checkoutSingleLEF()

topo_order = DB.TraverseHierTree()
for i in topo_order:
    hN = DB.CheckoutHierNode(i)
    print( i, hN.name)
    DB.PrintHierNode( hN)
    DB.WriteDBJSON( hN, f"__json_{hN.name}")
