cmake_minimum_required (VERSION 2.8.8)
project (example)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -std=c++14 -W")
link_directories(/home/lion/tensorflow/bazel-bin/tensorflow)
include_directories(
./include
 /home/lion/tensorflow
 /home/lion/tensorflow/bazel-genfiles
 /home/lion/tensorflow/tensorflow/contrib/makefile/downloads/nsync/public
 /home/lion/tensorflow/tensorflow/contrib/makefile/downloads/protobuf
 /home/lion/tensorflow/bazel-bin/tensorflow
 /usr/local/include/eigen3
 /home/lion/tensorflow/tensorflow/contrib/makefile/downloads/absl
  )
add_executable(example  test.cpp) 
target_link_libraries(example tensorflow_cc)















