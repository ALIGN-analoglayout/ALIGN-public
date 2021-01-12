## pybind11 Experiment

Compile PnR module using:
```bash
g++ -I ../json/include -O3 -Wall -shared -std=c++11 -fPIC `python -m pybind11 --includes` PnR-pybind11.cpp -o PnR`python3-config --extension-suffix` toplevel.o cap_placer/cap_placer.a placer/placer.a router/router.a PnRDB/PnRDB.a $GTEST_DIR/mybuild/lib/libgtest.so
```

First you need to recompile googletest using shared libraries:
```bash
cd path/to/googletest/googletest/mybuild
rm -rf ./*
cmake -DBUILD_SHARED_LIBS=ON ..
make
```

After a successful compile, then you can load up the database using C++ routines called from python
```python
from PnR import *

DB = PnRdatabase( "./testcase_example", "switched_capacitor_filter", "switched_capacitor_filter.v", "switched_capacitor_filter.lef", "switched_capacitor_filter.map", "layers.json")

lefs = DB.checkoutSingleLEF()

topo_order = DB.TraverseHierTree()
for i in topo_order:
    hN = DB.CheckoutHierNode(i)
    print( i, hN.name)
    DB.PrintHierNode( hN)
    DB.WriteDBJSON( hN, f"__json_{hN.name}")
```
