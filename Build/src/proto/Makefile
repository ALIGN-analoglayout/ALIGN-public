JSON = /opt/json
GTEST = /opt/googletest/googletest

CPPFLAGS += -isystem $(GTEST)/include -I$(JSON)/include

CXXFLAGS += -g -O2 -Wall -pthread

all: ptest

b.pb.cc: b.proto
	protoc --cpp_out=. b.proto

ptest: b.pb.o foo.o
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $^ -lpthread -lprotobuf -o $@
