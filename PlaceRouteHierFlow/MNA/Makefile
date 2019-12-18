# Need CXX and CXXFLAGS

OBJS=MNASimulation.o
SRCS=$(OBJS:.o=.cpp)

all: depend MNA.a

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

MNA.a: $(OBJS)
	ar -r -o $@ $^

clean:		
	/bin/rm -f *.o
