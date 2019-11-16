# How to setup environment for TensorFlow in C++
Here follows some steps to setup Tensorflow environment in C++.  

## 1.install bazel
1.1. Open your browser and download https://github.com/bazelbuild/bazel/releases/download/0.26.1/bazel_0.26.1-linux-x86_64.deb  
1.2. Packages for bazel:
  sudo apt-get install pkg-config zip g++ zlib1g-dev unzip python
1.3. Install the package using command sudo dpkg -i {path to the download bazel package}
 
## 2.Install TensorFlow
2.1 download
  git clone https://github.com/tensorflow/tensorflow.git  
  cd tensorflow  
  git checkout r2.0  
2.2 download denpendencies of tensorflow
  cd tensorflow
  ./tensorflow/contrib/makefile/download_dependencies.sh
2.3 install protobuf
  pip install autoconf automake libtool curl make g++ unzip gmock
  ./tensorflow/contrib/makefile/compile_linux_protobuf.sh
2.4 install eigen3 (this step can be done after installation of tensorflow)
  cd tensorflow/contrib/makefile/downloads/eigen  
  mkdir build  
  cd build  
  cmake ..  
  make  
  sudo make install
2.5 install dependencies
  pip install future --target=/usr/local/python2.7/dist-packages
  pip install numpy --tar=/usr/local/python2.7/dist-packages
2.5 compiler tensorflow
  ./configure (when configuring choose the packages folder as /usr/local/python2.7/dist-packages)
  bazel build --config=monolithic //tensorflow:libtensorflow_cc.so
  tips:
  this step will cost huge memory, 4g machine will cost 1h30min, 2g machine will cost 3h
  if your machine is only with 4g, please follow the command below--
    bazel build --config=monolithic --local_resources 2048,.5,1.0 //tensorflow:libtensorflow_cc.so
  if still fails, then add your raw memory by--
    sudo dd if=/dve/zero of=/mnt/512Mb.swap bs=1M count=512
    sudo mkswap /mnt/512Mb.swap
    sudo swapon /mnt/512Mb.swap

## 3.Modify Makefile
assign TENSORFLOW_DEPENDENCY with your tensorflow dir (for example, /home/XXX/tensorflow)
  
## 4.export LD_LIBRARY_PATH
run the following line in window or add to ~/.bashrc and source  
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:{path to tensorflow dir}
Please note, this tensorflow dir is $TENSORFLOW_DEPENDENCY/bazel-bin/tensorflow

