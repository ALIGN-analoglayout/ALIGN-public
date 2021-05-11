
MAKE=make

# External library dependencies
# Paths are currently managed by ALIGN-public/setup.sh
#	%> source setup.sh
# However, it is possible to overwrite all paths below
#	to conform to user environment
# For example, override LP_DIR as follows:
#	%> export LP_DIR=<path_to_lpsolve>
#	%> make
# Or inline as
#	%> LP_DIR=<path_to_lpsolve> make
SPDLOG_DIR?=/opt/spdlog
LP_DIR?=/usr/local/lib/lpsolve
BOOST_LP?=/usr/include
GTEST_DIR?=/opt/googletest/googletest
JSON?=/opt/json
SuperLu_DIR?=/opt/superlu

# Compilation options
# OPTIMFLAGS gets used in `make`
# DEBUGFLAGS gets used in `make debug`
# You may override them before calling make as previously shown
NOPYBIND11?=0
#FLAGS?=-std=c++17 -m64 -fPIC --coverage -DNDEBUG -DPRNTlevel=0 -DAdd_
FLAGS?=-g -w -Wall -std=c++11 -g -O3 -lm -ldl -m64 -pthread -std=c++17 -m64 -fPIC --coverage -DPRNTlevel=0 -DAdd_ -O3 -g -Wall
DEBUGFLAGS?=-O3 -g -Wall # Consider using -Og instead of -O3
OPTIMFLAGS?=-O3 -s -w

all: depend subsystem pnr_compiler python_object_file unit_tests

# Helper to create debug build
debug: OPTS = $(FLAGS) $(DEBUGFLAGS)
debug: all

# Inferred paths
export LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64
SuperLu=$(SuperLu_DIR)/SuperLU_5.2.1/SRC/
export GTEST_LIB_DIR = $(GTEST_DIR)/mybuild/lib

# Inferred flags
OPTS?=$(FLAGS) $(OPTIMFLAGS)
export CXXFLAGS = $(OPTS) -pthread -isystem $(LIB_LP) -I$(BOOST_LP) -I$(SuperLu) -I$(JSON)/include -isystem $(GTEST_DIR)/include -isystem $(SPDLOG_DIR)/include
export CXX=g++
export LDFLAGS = -lm -ldl -pthread

PnRDB_path=PnRDB
cap_placer_path=cap_placer
placer_path=placer
router_path=router
MNA_path=MNA
GuardRing_path=guard_ring
EA_placer_path=EA_placer

SuperLu_path1=$(SuperLu_DIR)/SuperLU_5.2.1/build/SRC
SuperLu_path2=$(SuperLu_DIR)/SuperLU_5.2.1/build/CBLAS

OBJS=main.o toplevel.o
SRCS=$(OBJS:.o=.cpp)
LIBS=$(placer_path)/placer.a $(router_path)/router.a $(cap_placer_path)/cap_placer.a $(PnRDB_path)/PnRDB.a $(MNA_path)/MNA.a $(SuperLu_path1)/libsuperlu.a $(SuperLu_path2)/libblas.a $(GuardRing_path)/GuardRing.a $(EA_placer_path)/EA_placer.a

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
	$(MAKE) -C $(EA_placer_path)     

pnr_compiler: subsystem $(OBJS) 
	$(CXX) $(CXXFLAGS) -o $@ $(OBJS) $(LIBS) -L$(GTEST_LIB_DIR) -lgtest -L$(LIB_LP) -llpsolve55 $(LDFLAGS)  


ifeq ($(NOPYBIND11),0)

PYBIND_INCLUDES = $(shell python -m pybind11 --includes)
PYBIND_SUFFIX = $(shell python3-config --extension-suffix)

python_object_file: PnR$(EXTENSION_SUFFIX)

PnR$(EXTENSION_SUFFIX): subsystem $(OBJS)
	$(CXX) $(CXXFLAGS) -shared $(PYBIND_INCLUDES) PnR-pybind11.cpp -o PnR$(PYBIND_SUFFIX) toplevel.o cap_placer/cap_placer.a placer/placer.a router/router.a PnRDB/PnRDB.a EA_placer/EA_placer.a -L$(GTEST_LIB_DIR) -lgtest -L$(LIB_LP) -llpsolve55
else
python_object_file:
	echo "Skipping generation of python object file because NOPYBIND11 is set."
endif

unit_tests: subsystem unit_tests.o
	$(CXX) $(CXXFLAGS) -o $@ unit_tests.o $(LIBS) -L$(GTEST_LIB_DIR) -lgtest_main -lgtest -L$(LIB_LP) -llpsolve55 $(LDFLAGS) 

clean:
	rm -rf *.o *.so pnr_compiler unit_tests \
		*.pl *.plt *gds all_* \
		*.gc{da,no} $(COVERAGE_HTML) $(COVERAGE_INFO)
	$(MAKE) -C $(PnRDB_path) clean
	$(MAKE) -C $(placer_path) clean
	$(MAKE) -C $(router_path) clean
	$(MAKE) -C $(cap_placer_path) clean
	$(MAKE) -C $(MNA_path) clean
	$(MAKE) -C $(GuardRing_path) clean
	$(MAKE) -C $(EA_placer_path) clean

COVERAGE_INFO=coverage.info
COVERAGE_HTML=htmlcov
COVERAGE_REPORT_OPTIONS=--no-branch-coverage --title "CPython lcov report"

coverage-init:
	lcov --directory . --zerocounters

coverage-report:
	@echo "Creating Coverage report..."
	@rm -f $(COVERAGE_INFO)
	@rm -rf $(COVERAGE_HTML)
	@lcov --capture --directory . \
	    --output-file $(COVERAGE_INFO)
	@lcov --remove $(COVERAGE_INFO) \
		'/usr/include/*' \
		'*/include/pybind11/*' \
		'*/include/spdlog/*' \
		'*/include/nlohmann/*' \
		'*/include/gtest/*' \
		--output-file $(COVERAGE_INFO)
	@genhtml $(COVERAGE_INFO) \
		--output-directory $(COVERAGE_HTML) \
		$(COVERAGE_REPORT_OPTIONS)
	@echo "View report at $(COVERAGE_HTML)/index.html"

# Declare all phony targets
.PHONY: depend subsystem python_object_file
.PHONY: clean coverage-init coverage-report
