.SUFFIXES:      .o .cxx

CC	= g++ 
#CC	= g++ -pg
#CC	= purify g++

#DBG_FLAGS  = -DDEBUG
#DBG_FLAGS  = -DDEBUG -g
#DBG_FLAGS  = -DDEBUG -DDEBUG2
#DBG_FLAGS  = -DDEBUG -DDEBUG2 -g
CFLAGS	= -Wall $(DBG_FLAGS)
LIBS	= -lm 

SRCS0	= main.cxx unixtimer.cxx err.cxx random.cxx\
          neighbors.cxx heap.cxx mst2.cxx\
          stnr1.cxx triples.cxx
OBJS0	= $(SRCS0:.cxx=.o) 
MAIN0	= steiner

SRCS1	= gen.cxx
OBJS1	= $(SRCS1:.cxx=.o) 
MAIN1	= gen

new:    clean steiner gen

.cxx.o:
	$(CC) $(INCLUDES) -c $*.cxx

steiner: 	${OBJS0}
	$(CC) -o ${MAIN0} ${OBJS0} $(LIBS)

gen: 	${OBJS1}
	$(CC) -o ${MAIN1} ${OBJS1} $(LIBS)

clean:
	rm -f *.o
	rm -f ${MAIN0}
	rm -f ${MAIN1}
	rm -f core

