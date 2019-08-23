
# Needs CXX and CXXFLAGS to be defined

all: design.o SeqPair.o ConstGraph.o Aplace.o Placer.o unit_tests

Placer.o : Placer.cpp Placer.h

Preadfile.o : Preadfile.cpp

design.o: design.cpp

SeqPair.o: SeqPair.cpp

ConstGraph.o: ConstGraph.cpp

Aplace.o: Aplace.cpp

unit_tests.o: unit_tests.cpp

unit_tests: unit_tests.o
	$(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

clean:		
	/bin/rm -f *.o unit_tests
