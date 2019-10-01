BOOST_LP?=/usr/local
CC=g++ -w -Wall -std=c++11 -g -O3 -pthread
CC2=$(CC) -I$(BOOST_LP) 
#CC=g++ -w -Wall -std=c++11 -g -DRFLAG
SOURCE=./router

#all: MNASimulation.o

main: main.o MNASimulation.o 
	$(CC2) main.o MNASimulation.o  -o main
main.o: main.cpp MNASimulation.h
	$(CC2) -c main.cpp
MNASimulation.o: MNASimulation.cpp MNASimulation.h 
	$(CC2) -c MNASimulation.cpp
clean:		
		/bin/rm -f *.o 