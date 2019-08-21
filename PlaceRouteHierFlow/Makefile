
MAKE=make

# To compile locally, override LP_DIR as follows:  %> LP_DIR=<path_to_lpsolve> make
LP_DIR?=/usr/local/lib/lpsolve
LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64
SOURCE_LP= $(LP_DIR)/lp_solve_5.5
BOOST_LP?=/usr/include

GTEST_DIR?=/opt/googletest/googletest

COVERAGE?=
OPTS?=-g -O3
WARNS?=-w -Wall
JSON?=/opt/json

export CXXFLAGS = $(OPTS) $(WARNS) -std=c++14 -m64 -pthread -I$(LIB_LP) -I$(SOURCE_LP) -I$(BOOST_LP) -I$(JSON)/include $(COVERAGE) -isystem $(GTEST_DIR)/include
export CXX=g++

export LDFLAGS = -lm -ldl -pthread $(COVERAGE)
export GTEST_LIB_DIR = $(GTEST_DIR)/mybuild/lib

PnRDB_path=PnRDB
Capplacer_path=cap_placer
placer_path=placer
router_path=router

PnRDB_objs=PnRDB/PnRdatabase.o PnRDB/readfile.o
Capplacer_objs=cap_placer/capplacer.o
placer_objs=placer/Placer.o placer/ConstGraph.o placer/design.o placer/SeqPair.o placer/Aplace.o
router_objs=router/Router.o router/GlobalRouter.o router/Graph.o router/Grid.o router/RawRouter.o router/DetailRouter.o router/PowerRouter.o router/GlobalGrid.o router/GlobalGraph.o router/GcellGlobalRouter.o router/GcellDetailRouter.o

all: subsystem pnr_compiler

pnr_compiler: $(PnRDB_objs) $(placer_objs) $(router_objs) $(Capplacer_objs) main.o
	$(CXX) -o pnr_compiler $(PnRDB_objs) $(placer_objs) $(router_objs) $(Capplacer_objs) main.o $(LDFLAGS)

subsystem:
	$(MAKE) -C $(PnRDB_path);
	$(MAKE) -C $(placer_path);
	$(MAKE) -C $(router_path);
	$(MAKE) -C $(Capplacer_path);

main.o:		main.cpp $(PnRDB_path)/datatype.h $(PnRDB_path)/PnRdatabase.h $(placer_path)/Placer.h $(router_path)/Router.h $(Capplacer_path)/capplacer.h
	$(CXX) $(CXXFLAGS) -c main.cpp -I$(JSON)/include

clean:
	rm -rf *.o $(PnRDB_path)/*.o $(placer_path)/*.o pnr_compiler *.pl *.plt *gds all_*
	make -C $(router_path) clean
	make -C $(Capplacer_path) clean
