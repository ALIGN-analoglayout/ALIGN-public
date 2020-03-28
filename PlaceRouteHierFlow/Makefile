MAKE=make


# To compile locally, override LP_DIR as follows:  %> LP_DIR=<path_to_lpsolve> make
LP_DIR?=/usr/local/lib/lpsolve
LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64
SOURCE_LP= $(LP_DIR)/lp_solve_5.5
BOOST_LP?=/usr/include

GTEST_DIR?=/opt/googletest/googletest

COVERAGE?=
OPTS?=-g -O3
WARNS?=-Wall
JSON?=/opt/json
SuperLu?=/home/grads/x/xurishang/research/test/superlu/SuperLU_5.2.1/SRC/

export CXXFLAGS = $(OPTS) $(WARNS) -w -std=c++14 -m64 -pthread -DNDEBUG -DPRNTlevel=0 -DAdd_ -isystem $(LIB_LP) -isystem $(SOURCE_LP) -I$(BOOST_LP) -I$(SuperLu) -I$(JSON)/include $(COVERAGE) -isystem $(GTEST_DIR)/include 
export CXX=g++

export LDFLAGS = -lm -ldl -pthread $(COVERAGE)
export GTEST_LIB_DIR = $(GTEST_DIR)/mybuild/lib

PnRDB_path=PnRDB
cap_placer_path=cap_placer
placer_path=placer
router_path=router
MNA_path=MNA

SuperLu_path1=/home/grads/x/xurishang/research/test/superlu/SuperLU_5.2.1/build/SRC
SuperLu_path2=/home/grads/x/xurishang/research/test/superlu/SuperLU_5.2.1/build/CBLAS

OBJS=main.o
SRCS=$(OBJS:.o=.cpp)
LIBS=$(placer_path)/placer.a $(router_path)/router.a $(cap_placer_path)/cap_placer.a $(PnRDB_path)/PnRDB.a $(MNA_path)/MNA.a $(SuperLu_path1)/libsuperlu.a $(SuperLu_path2)/libblas.a

all: depend subsystem pnr_compiler unit_tests

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) unit_tests.cpp > .depend

-include .depend

subsystem:
	$(MAKE) -C $(PnRDB_path)
	$(MAKE) -C $(placer_path)
	$(MAKE) -C $(router_path)
	$(MAKE) -C $(cap_placer_path)
	$(MAKE) -C $(MNA_path)

pnr_compiler: subsystem $(OBJS) 
	$(CXX) -o $@ $(OBJS) $(LIBS) -L$(GTEST_LIB_DIR) -lgtest $(LDFLAGS) 

unit_tests: subsystem unit_tests.o
	$(CXX) -o $@ unit_tests.o $(LIBS) -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS) 

clean:
	rm -rf *.o pnr_compiler *.pl *.plt *gds all_* *.gc{da,no}
	make -C $(PnRDB_path) clean
	make -C $(placer_path) clean
	make -C $(router_path) clean
	make -C $(cap_placer_path) clean
	$(MAKE) -C $(MNA_path) clean
