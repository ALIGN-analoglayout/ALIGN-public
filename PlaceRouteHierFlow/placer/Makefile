
# Needs CXX and CXXFLAGS to be defined

LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64

OBJS = design.o SeqPair.o ConstGraph.o Aplace.o Placer.o ILP_solver.o
SRCS=$(OBJS:.o=.cpp)

all: depend unit_tests placer.a

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

unit_tests: unit_tests.o 
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS) -L$(LIB_LP) -llpsolve55

placer.a: $(OBJS)
	ar -r -o $@ $^

clean:		
	/bin/rm -f *.o *.a unit_tests .depend
