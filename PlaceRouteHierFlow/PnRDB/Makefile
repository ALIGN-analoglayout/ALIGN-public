#CC=g++ -g -w -Wall -std=c++11
CC=g++ -g -w -Wall -std=c++11 -DHFLAG
#CC=g++ -w -Wall -std=c++11 -g -DRFLAG

# JSON place can be over-ridden:  nlohmann/json
JSON?=/opt/json
SOURCE=./
OBJECTS=readfile.o PnRdatabase.o main.o

all: readfile.o PnRdatabase.o

readfile.o :    readfile.cpp readfile.h
		$(CC) -c readfile.cpp 

PnRdatabase.o:	PnRdatabase.cpp PnRdatabase.h readfile.h datatype.h
		$(CC) -c PnRdatabase.cpp -I$(JSON)/include

clean:		
		/bin/rm -f *.o tester
