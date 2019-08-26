# Need CXX, and CXXFLAGS to be defined

OBJS=readfile.o PnRdatabase.o ReadDesignRule.o ReadDesignRuleJson.o HardDesignRule.o WriteJSON.o ReadVerilog.o ReadConstraint.o Print.o ReadLEF.o
SRCS=$(OBJS:.o=.cpp)

all: depend unit_tests unit_tests2 PnRDB.a

depend:
	$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

unit_tests: unit_tests.o $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

PnRDB.a: $(OBJS)
	ar -r -o $@ $^

clean:		
	/bin/rm -f *.o *.a unit_tests .depend
