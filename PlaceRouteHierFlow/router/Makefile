# Needs CXX and CXXFLAGS

LP_DIR?=/usr/local/lib/lpsolve
LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64
SOURCE_LP= $(LP_DIR)/lp_solve_5.5

OBJS= RawRouter.o Grid.o GlobalGrid.o Graph.o A_star.o GlobalGraph.o GlobalRouter.o GcellGlobalRouter.o DetailRouter.o GcellDetailRouter.o PowerRouter.o Router.o 
SRCS=$(OBJS:.o=.cpp)

all: depend unit_tests router.a
	$(MAKE) -C FastSteinerUM

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

unit_tests: unit_tests.o $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

router.a: $(OBJS)
	ar -r -o $@ $^

#########

clean:
	rm -f  *.o *_exe run.log ./Debug/*.txt output.txt vals ./GDS_To_ASCII/*.txt unit_tests .depend
	make -C FastSteinerUM clean

