# Need CXX and CXXFLAGS

OBJS=capplacer.o
SRCS=$(OBJS:.o=.cpp)

all: depend unit_tests cap_placer.a

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

unit_tests: unit_tests.o
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

cap_placer.a: $(OBJS)
	ar -r -o $@ $^

clean:		
	/bin/rm -f *.o unit_tests
