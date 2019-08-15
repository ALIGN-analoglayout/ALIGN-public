
# Need JSON, CXX, and CXXFLAGS to be defined

SOURCE=./
OBJECTS=readfile.o PnRdatabase.o main.o

all: readfile.o PnRdatabase.o

readfile.o :    readfile.cpp readfile.h
		$(CXX) $(CXXFLAGS) -c readfile.cpp 

PnRdatabase.o:	PnRdatabase.cpp PnRdatabase.h readfile.h datatype.h
		$(CXX) $(CXXFLAGS) -c PnRdatabase.cpp -I$(JSON)/include

clean:		
		/bin/rm -f *.o tester
