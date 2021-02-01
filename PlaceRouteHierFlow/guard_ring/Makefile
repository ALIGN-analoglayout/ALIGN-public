OBJS= GuardRing.o GuardRingIfc.o
SRCS=$(OBJS:.o=.cpp)

all: depend GuardRing.a

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

GuardRing.a: $(OBJS)
	ar -r -o $@ $^

#########

clean:
	rm -f  *.o
