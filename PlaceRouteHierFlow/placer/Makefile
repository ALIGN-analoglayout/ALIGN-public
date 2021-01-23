
# Needs CXX CXXFLAGS LIB_LP to be defined

OBJS = design.o SeqPair.o ConstGraph.o Aplace.o Placer.o ILP_solver.o PlacerIfc.o
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
