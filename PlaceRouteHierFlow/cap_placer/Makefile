SOURCE_LP = ../lpsolve/lp_solve_5.5

CC=g++ -w -Wall -std=c++11 -g -pthread -I$(SOURCE_LP)
#CC=g++ -w -Wall -std=c++11 -g -DRFLAG

# JSON place can be over-ridden:  nlohmann/json
JSON?=/opt/json
SOURCE=./
OBJECTS=main.o capplacer.o

all: capplacer.o 

capplacer.o :	capplacer.cpp capplacer.h
		$(CC) -c capplacer.cpp -I$(JSON)/include

clean:		
		/bin/rm -f *.o 
