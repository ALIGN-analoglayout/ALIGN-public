# Need CXX, and CXXFLAGS to be defined

all: readfile.o PnRdatabase.o unit_tests ReadDesignRule.o ReadDesignRuleJson.o HardDesignRule.o WriteJSON.o ReadVerilog.o ReadConstraint.o Print.o ReadLEF.o

readfile.o: readfile.cpp readfile.h

ReadDesignRule.o: ReadDesignRule.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

ReadDesignRuleJson.o: ReadDesignRuleJson.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

HardDesignRule.o: HardDesignRule.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

WriteJSON.o: WriteJSON.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

ReadVerilog.o: ReadVerilog.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

ReadConstraint.o: ReadConstraint.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

Print.o: Print.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

ReadLEF.o: ReadLEF.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

PnRdatabase.o: PnRdatabase.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

unit_tests.o: unit_tests.cpp PnRdatabase.h readfile.h datatype.h Lexer.h

unit_tests: unit_tests.o readfile.o PnRdatabase.o ReadDesignRule.o ReadDesignRuleJson.o HardDesignRule.o WriteJSON.o ReadVerilog.o ReadConstraint.o Print.o ReadLEF.o
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

clean:		
	/bin/rm -f *.o unit_tests
