
MAKE=make

EXTENSION_SUFFIX?=`python3-config --extension-suffix`

# To compile locally, override LP_DIR as follows:  %> LP_DIR=<path_to_lpsolve> make
SPDLOG_DIR?=/opt/spdlog
LP_DIR?=/usr/local/lib/lpsolve
export LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64
BOOST_LP?=/usr/include

GTEST_DIR?=/opt/googletest/googletest

NOPYBIND11?=0
COVERAGE?=
#OPTS?=-g -O3
OPTS?=-g
WARNS?=-Wall
JSON?=/opt/json
SuperLu_DIR?=/opt/superlu
SuperLu=$(SuperLu_DIR)/SuperLU_5.2.1/SRC/

export CXXFLAGS = $(OPTS) $(WARNS) -w -std=c++17 -m64 -pthread -DNDEBUG -DPRNTlevel=0 -DAdd_ -isystem $(LIB_LP) -I$(BOOST_LP) -I$(SuperLu) -I$(JSON)/include $(COVERAGE) -isystem $(GTEST_DIR)/include -isystem $(SPDLOG_DIR)/include -fPIC
export CXX=g++

export LDFLAGS = -lm -ldl -pthread $(COVERAGE)
export GTEST_LIB_DIR = $(GTEST_DIR)/mybuild/lib

PnRDB_path=PnRDB
cap_placer_path=cap_placer
placer_path=placer
router_path=router
MNA_path=MNA
GuardRing_path=guard_ring

SuperLu_path1=$(SuperLu_DIR)/SuperLU_5.2.1/build/SRC
SuperLu_path2=$(SuperLu_DIR)/SuperLU_5.2.1/build/CBLAS

OBJS=main.o toplevel.o
SRCS=$(OBJS:.o=.cpp)
LIBS=$(placer_path)/placer.a $(router_path)/router.a $(cap_placer_path)/cap_placer.a $(PnRDB_path)/PnRDB.a $(MNA_path)/MNA.a $(SuperLu_path1)/libsuperlu.a $(SuperLu_path2)/libblas.a $(GuardRing_path)/GuardRing.a


all: depend subsystem pnr_compiler python_object_file unit_tests

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) unit_tests.cpp > .depend

-include .depend

subsystem:
	$(MAKE) -C $(PnRDB_path)
	$(MAKE) -C $(placer_path)
	$(MAKE) -C $(router_path)
	$(MAKE) -C $(cap_placer_path)
	$(MAKE) -C $(MNA_path)
	$(MAKE) -C $(GuardRing_path)

pnr_compiler: subsystem $(OBJS) 
	$(CXX) $(CXXFLAGS) -o $@ $(OBJS) $(LIBS) -L$(GTEST_LIB_DIR) -lgtest -L$(LIB_LP) -llpsolve55 $(LDFLAGS)  


ifeq ($(NOPYBIND11),0)
python_object_file: PnR$(EXTENSION_SUFFIX)
PnR$(EXTENSION_SUFFIX): subsystem $(OBJS)
	$(CXX) $(CXXFLAGS) -shared `python -m pybind11 --includes` PnR-pybind11.cpp -o PnR$(EXTENSION_SUFFIX) toplevel.o cap_placer/cap_placer.a placer/placer.a router/router.a PnRDB/PnRDB.a -L$(GTEST_LIB_DIR) -lgtest -L$(LIB_LP) -llpsolve55
else
python_object_file:
	echo "Skipping generation of python object file because NOPYBIND11 is set."
endif

unit_tests: subsystem unit_tests.o
	$(CXX) -o $@ unit_tests.o $(LIBS) -L$(GTEST_LIB_DIR) -lgtest_main -lgtest -L$(LIB_LP) -llpsolve55 $(LDFLAGS) 

clean:
	rm -rf *.o *.so pnr_compiler *.pl *.plt *gds all_* *.gc{da,no}
	make -C $(PnRDB_path) clean
	make -C $(placer_path) clean
	make -C $(router_path) clean
	make -C $(cap_placer_path) clean
	$(MAKE) -C $(MNA_path) clean
	$(MAKE) -C $(GuardRing_path) clean
