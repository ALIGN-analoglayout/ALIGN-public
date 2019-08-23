# Need CXX and CXXFLAGS

all: capplacer.o unit_tests

capplacer.o : capplacer.cpp capplacer.h

unit_tests.o: unit_tests.cpp

unit_tests: unit_tests.o
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

clean:		
	/bin/rm -f *.o unit_tests
