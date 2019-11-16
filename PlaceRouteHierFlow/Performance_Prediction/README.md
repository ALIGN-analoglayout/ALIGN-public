# How to setup environment for TensorFlow in C++
Here follows some steps to setup Tensorflow environment in C++.  
These works in Ubuntu 16.04 4.13.0-36-generic x86_64.     
## 1.install bazel
Open your browser and download https://github.com/bazelbuild/bazel/releases/download/0.26.1/bazel_0.26.1-linux-x86_64.deb  
Install the package using command sudo dpkg -i {path to the download bazel package}
## 2.Install protobuf
download https://github.com/protocolbuffers/protobuf/archive/v3.8.0.tar.gz
tar zxvf protobuf-all-3.8.0.tar.gz
cd protobuf-3.8.0/
./autogen.sh
./configure
make
sudo make install
## 3.Install TensorFlow
git clone https://github.com/tensorflow/tensorflow.git  
cd tensorflow  
git checkout r2.0  
./configure (I chose 'No' for every question. You can have your own configuration.)  
bazel build --config=monolithic //tensorflow:libtensorflow_cc.so  
## 4.Install eigen3  
cd tensorflow/tensorflow/contrib/makefile/downloads/eigen  
mkdir build  
cd build  
cmake ..  
make  
sudo make install    
## 5.Modify Makefile
assign TENSORFLOW_DEPENDENCY with your tensorflow dir (for example, /home/XXX/tensorflow)  
## 6.export LD_LIBRARY_PATH
run the following line in window or add to ~/.bashrc and source  
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:{path to tensorflow dir}  