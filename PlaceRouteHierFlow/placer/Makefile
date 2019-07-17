BOOST_LP?=/usr/local
CC=g++ -w -Wall -std=c++11 -g -pthread
CC2=g++ -w -Wall -std=c++11 -g -pthread -I$(BOOST_LP)
#CC=g++ -w -Wall -std=c++11 -g -DRFLAG
SOURCE=./
OBJECTS=main.o design.o Preadfile.o SeqPair.o ConstGraph.o Aplace.o

all: design.o SeqPair.o ConstGraph.o Aplace.o Placer.o

Placer.o :	Placer.h
		$(CC2) -c Placer.cpp

Preadfile.o :
		$(CC) -c Preadfile.cpp 

design.o:
		$(CC) -c design.cpp 

SeqPair.o:
		$(CC) -c SeqPair.cpp

ConstGraph.o:
		$(CC2) -c ConstGraph.cpp

Aplace.o:
		$(CC2) -c Aplace.cpp

clean:		
		/bin/rm -f *.o 
