# Need CXX, and CXXFLAGS to be defined

all: readfile.o PnRdatabase.o unit_tests

readfile.o: readfile.cpp readfile.h

PnRdatabase.o: PnRdatabase.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

unit_tests.o: unit_tests.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

unit_tests: unit_tests.o readfile.o PnRdatabase.o
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

clean:		
	/bin/rm -f *.o unit_tests
