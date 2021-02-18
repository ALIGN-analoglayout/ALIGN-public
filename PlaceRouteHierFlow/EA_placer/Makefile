# Need CXX and CXXFLAGS

OBJS=placement.o FFT/fft.o FFT/fftsg2d.o FFT/fftsg.o 
SRCS=$(OBJS:.o=.cpp)

all: depend EA_placer.a

depend:
	@$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

EA_placer.a: $(OBJS)
	ar -r -o $@ $^

clean:		
	/bin/rm -f *.o
