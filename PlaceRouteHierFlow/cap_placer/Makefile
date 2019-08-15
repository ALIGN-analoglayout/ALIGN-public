# Need JSON, CXX and CXXFLAGS

OBJECTS=main.o capplacer.o

all: capplacer.o 

capplacer.o :	capplacer.cpp capplacer.h
		$(CXX) $(CXXFLAGS) -c capplacer.cpp -I$(JSON)/include

clean:		
		/bin/rm -f *.o 
