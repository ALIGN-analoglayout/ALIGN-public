JSON = /opt/json
GTEST = /opt/googletest/googletest

CPPFLAGS += -isystem $(GTEST)/include -I$(JSON)/include

CXXFLAGS += -g -O2 -Wall -pthread -fprofile-arcs -ftest-coverage

tester: test.o $(GTEST)/make/libgtest_main.a
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $^ -lpthread -o $@

