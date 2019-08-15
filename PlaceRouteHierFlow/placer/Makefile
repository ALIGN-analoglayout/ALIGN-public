
# Needs CXX and CXXFLAGS to be defined

BOOST_LP?=/usr/local

SOURCE=./
OBJECTS=main.o design.o Preadfile.o SeqPair.o ConstGraph.o Aplace.o

all: design.o SeqPair.o ConstGraph.o Aplace.o Placer.o

Placer.o :	Placer.h
		$(CXX) $(CXXFLAGS) -I$(BOOST_LP) -c Placer.cpp

Preadfile.o :
		$(CXX) $(CXXFLAGS) -c Preadfile.cpp 

design.o:
		$(CXX) $(CXXFLAGS) -c design.cpp 

SeqPair.o:
		$(CXX) $(CXXFLAGS) -c SeqPair.cpp

ConstGraph.o:
		$(CXX) $(CXXFLAGS) -I$(BOOST_LP) -c ConstGraph.cpp

Aplace.o:
		$(CXX) $(CXXFLAGS) -I$(BOOST_LP) -c Aplace.cpp

clean:		
		/bin/rm -f *.o 
