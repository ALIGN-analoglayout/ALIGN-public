CC=g++ -w -Wall -std=c++11 -g -pthread
#CC=g++ -w -Wall -std=c++11 -g -DRFLAG
SOURCE=./
OBJECTS=main.o design.o Preadfile.o SeqPair.o ConstGraph.o

all: design.o SeqPair.o ConstGraph.o Placer.o

Placer.o :	Placer.h
		$(CC) -c Placer.cpp

Preadfile.o :
		$(CC) -c Preadfile.cpp 

design.o:
		$(CC) -c design.cpp 

SeqPair.o:
		$(CC) -c SeqPair.cpp

ConstGraph.o:
		$(CC) -c ConstGraph.cpp

clean:		
		/bin/rm -f *.o 
