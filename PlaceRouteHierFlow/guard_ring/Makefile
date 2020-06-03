OBJS= guardring.o
SRCS=$(OBJS:.o=.cpp)

all: depend unit_tests guardring.a
        $(MAKE) -C FastSteinerUM

depend:
        @$(CXX) $(CXXFLAGS) -E -MM $(SRCS) > .depend

-include .depend

unit_tests: unit_tests.o $(OBJS)
        $(CXX) $(CXXFLAGS) -o $@ $^ -L$(GTEST_LIB_DIR) -lgtest_main -lgtest $(LDFLAGS)

guardring.a: $(OBJS)
        ar -r -o $@ $^

#########

clean:
        rm -f  *.o *_exe run.log ./Debug/*.txt output.txt vals unit_tests .depend
