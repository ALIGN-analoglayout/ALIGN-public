#lp_solve
LDFLAGS="-Wl,--no-as-needed"
# To compile locally, override LP_DIR as follows:  %> LP_DIR=<path_to_lpsolve> make
LP_DIR?=/usr/local/lib/lpsolve
LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64
SOURCE_LP= $(LP_DIR)/lp_solve_5.5

CC     = g++ -w -Wall -std=c++11 -g -O3 -lm -ldl -m64 -I$(SOURCE_LP)

#GDSWriter
###SOURCE_GDSW = ./GDSWriter

OBJS0	= main.o unixtimer.o err.o random.o neighbors.o heap.o mst2.o stnr1.o triples.o 
MAIN0	= steiner

#Source code
SOURCE_CODE = .

SOURCE_CODE_PnRDB = ../PnRDB

#OBJECTS  = main.o GdsWriter.o readfile.o grid.o GdsReader.o GdsDriver.o

###all: router.o grid.o GdsWriter.o GdsReader.o GdsDriver.o .cxx.o steiner
###
###router.o: $(SOURCE_CODE)/router.h $(SOURCE_CODE)/grid.h
###	$(CC) -c $(SOURCE_CODE)/router.cpp
###
###grid.o:  $(SOURCE_CODE)/grid.h $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE_PnRDB)/readfile.h $(SOURCE_GDSW)/GdsWriter.h $(SOURCE_GDSW)/GdsReader.h  $(SOURCE_GDSW)/GdsRecords.h $(LIB_LP)/lp_lib.h $(SOURCE_LP)/lp_explicit.h 
###	$(CC) -c $(SOURCE_CODE)/grid.cpp 
###
###GdsReader.o:  $(SOURCE_GDSW)/GdsReader.h $(SOURCE_GDSW)/String.h $(SOURCE_GDSW)/GdsRecords.h $(SOURCE_CODE)/grid.h
###	$(CC) -c $(SOURCE_GDSW)/GdsReader.cpp
###
###GdsDriver.o:  $(SOURCE_GDSW)/GdsDriver.h $(SOURCE_GDSW)/GdsReader.h $(SOURCE_GDSW)/String.h $(SOURCE_GDSW)/GdsRecords.h
###	$(CC) -c $(SOURCE_GDSW)/GdsDriver.cpp
###
###GdsWriter.o:  $(SOURCE_GDSW)/GdsWriter.h $(SOURCE_GDSW)/String.h
###	$(CC) -c $(SOURCE_GDSW)/GdsWriter.cpp
###

#########2333333
all: RawRouter.o Grid.o Graph.o GlobalRouter.o DetailRouter.o PowerRouter.o Router.o .cxx.o steiner

RawRouter.o: $(SOURCE_CODE)/RawRouter.h $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE)/Rdatatype.h 
	$(CC) -c $(SOURCE_CODE)/RawRouter.cpp

Grid.o: $(SOURCE_CODE)/Grid.h $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE)/Rdatatype.h
	$(CC) -c $(SOURCE_CODE)/Grid.cpp

Graph.o: $(SOURCE_CODE)/Graph.h $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE)/Rdatatype.h $(SOURCE_CODE)/Grid.h
	$(CC) -c $(SOURCE_CODE)/Graph.cpp

GlobalRouter.o: $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE)/Rdatatype.h $(SOURCE_CODE)/Grid.h $(SOURCE_CODE)/Graph.h $(SOURCE_CODE)/RawRouter.h $(SOURCE_CODE)/GlobalRouter.h $(LIB_LP)/lp_lib.h $(SOURCE_LP)/lp_explicit.h
	$(CC) -c $(SOURCE_CODE)/GlobalRouter.cpp

DetailRouter.o: $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE)/Rdatatype.h $(SOURCE_CODE)/Grid.h $(SOURCE_CODE)/Graph.h $(SOURCE_CODE)/RawRouter.h $(SOURCE_CODE)/GlobalRouter.h $(SOURCE_CODE)/DetailRouter.h
	$(CC) -c $(SOURCE_CODE)/DetailRouter.cpp

PowerRouter.o: $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE)/Rdatatype.h $(SOURCE_CODE)/Grid.h $(SOURCE_CODE)/Graph.h $(SOURCE_CODE)/RawRouter.h $(SOURCE_CODE)/DetailRouter.h $(SOURCE_CODE)/PowerRouter.h
	$(CC) -c $(SOURCE_CODE)/PowerRouter.cpp 

Router.o: $(SOURCE_CODE_PnRDB)/datatype.h $(SOURCE_CODE)/Rdatatype.h $(SOURCE_CODE)/GlobalRouter.h $(SOURCE_CODE)/DetailRouter.h $(SOURCE_CODE)/PowerRouter.h
	$(CC) -c $(SOURCE_CODE)/Router.cpp

#########

INCLUDES = FastSteinerUM/*.cxx

.cxx.o:
	$(CC) $(INCLUDES) -c

#system call steiner executable
steiner: 	${OBJS0}
	$(CC) -o ${MAIN0} ${OBJS0}

clean:
	rm -f  *.o *_exe steiner run.log ./Debug/*.txt output.txt vals ./GDS_To_ASCII/*.txt 

