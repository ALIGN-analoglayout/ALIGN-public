CC=g++ -g -w -Wall -std=c++11
#CC=g++ -w -Wall -std=c++11 -g -DRFLAG
SOURCE=./
OBJECTS=readfile.o PnRdatabase.o main.o

all: readfile.o PnRdatabase.o

readfile.o :    readfile.cpp readfile.h
		$(CC) -c readfile.cpp 

PnRdatabase.o:	PnRdatabase.h readfile.h datatype.h
		$(CC) -c PnRdatabase.cpp

clean:		
		/bin/rm -f *.o tester
