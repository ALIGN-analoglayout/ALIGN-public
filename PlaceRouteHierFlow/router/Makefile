# Needs CXX and CXXFLAGS

LP_DIR?=/usr/local/lib/lpsolve
LIB_LP = $(LP_DIR)/lp_solve_5.5.2.5_dev_ux64
SOURCE_LP= $(LP_DIR)/lp_solve_5.5

SOURCE_CODE_PnRDB = ../PnRDB

all: RawRouter.o Grid.o GlobalGrid.o Graph.o GlobalGraph.o GlobalRouter.o GcellGlobalRouter.o DetailRouter.o GcellDetailRouter.o PowerRouter.o Router.o
	$(MAKE) -C FastSteinerUM

RawRouter.o: RawRouter.cpp RawRouter.h $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h 

Grid.o: Grid.cpp Grid.h $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h

GlobalGrid.o: GlobalGrid.cpp GlobalGrid.h $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h

Graph.o: Graph.cpp Graph.h $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h Grid.h

GlobalGraph.o: GlobalGraph.cpp GlobalGraph.h $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h GlobalGrid.h

GlobalRouter.o: GlobalRouter.cpp $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h Grid.h Graph.h RawRouter.h GlobalRouter.h $(LIB_LP)/lp_lib.h $(SOURCE_LP)/lp_explicit.h

GcellGlobalRouter.o: GcellGlobalRouter.cpp $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h GlobalGrid.h GlobalGraph.h RawRouter.h GcellGlobalRouter.h $(LIB_LP)/lp_lib.h $(SOURCE_LP)/lp_explicit.h

DetailRouter.o: DetailRouter.cpp $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h Grid.h Graph.h RawRouter.h GlobalRouter.h GcellGlobalRouter.h DetailRouter.h

GcellDetailRouter.o: GcellDetailRouter.cpp $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h Grid.h Graph.h RawRouter.h GlobalRouter.h GcellGlobalRouter.h GcellDetailRouter.h GlobalGrid.h GlobalGraph.h 

PowerRouter.o: PowerRouter.cpp $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h Grid.h Graph.h RawRouter.h DetailRouter.h PowerRouter.h

Router.o: Router.cpp $(SOURCE_CODE_PnRDB)/datatype.h Rdatatype.h GlobalRouter.h DetailRouter.h PowerRouter.h GcellGlobalRouter.h


#########

clean:
	rm -f  *.o *_exe run.log ./Debug/*.txt output.txt vals ./GDS_To_ASCII/*.txt
	make -C FastSteinerUM clean

