# How to setup environment for TensorFlow in C++
Here follows some steps to setup Tensorflow environment in C++.  
These works in Ubuntu 16.04.
## 1.install bazel
Open your browser and download https://github.com/bazelbuild/bazel/releases/download/0.26.1/bazel_0.26.1-linux-x86_64.deb  
Install the package using command sudo dpkg -i {path to the download bazel package}
## 2.Install TensorFlow
git clone https://github.com/tensorflow/tensorflow.git  
cd tensorflow  
git checkout r2.0  
./configure (I chose 'No' for every question. You can have your own configuration.)  
bazel build --config=monolithic //tensorflow:libtensorflow_cc.so  
## 3.Install eigen3  
cd tensorflow/tensorflow/contrib/makefile/downloads/eigen  
mkdir build  
cd build  
cmake ..  
make  
sudo make install  
## 4.Install protobuf  
cd tensorflow  
./tensorflow/contrib/makefile/compile_linux_protobuf.sh  
## 5.Write a CMakeLists.txt
cmake_minimum_required (VERSION 2.8.8)  
project (example)  
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -std=c++14 -W")  
link_directories(/home/lion/tensorflow/bazel-bin/tensorflow)  
include_directories(  
./include  
 {path_to_tensorflow}/tensorflow  
 {path_to_tensorflow}/tensorflow/bazel-genfiles  
 {path_to_tensorflow}/tensorflow/tensorflow/contrib/makefile/downloads/nsync/public  
 {path_to_tensorflow}/tensorflow/tensorflow/contrib/makefile/downloads/protobuf  
 {path_to_tensorflow}/tensorflow/bazel-bin/tensorflow  
 /usr/local/include/eigen3  
 {path_to_tensorflow}/tensorflow/tensorflow/contrib/makefile/downloads/absl  
  )  
add_executable(example  test.cpp)  
target_link_libraries(example tensorflow_cc)  
## 6.Build the file
mkdir build && cd build  
cmake ..  
make  