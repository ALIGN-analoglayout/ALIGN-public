# Need CXX, and CXXFLAGS to be defined

all: readfile.o PnRdatabase.o

readfile.o :    readfile.cpp readfile.h

PnRdatabase.o:	PnRdatabase.cpp PnRdatabase.h readfile.h datatype.h

clean:		
	/bin/rm -f *.o tester
