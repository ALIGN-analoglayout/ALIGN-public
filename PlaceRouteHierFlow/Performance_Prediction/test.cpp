#include <tensorflow/core/platform/env.h>
#include <tensorflow/core/public/session.h>
#include <iostream>
#include <string>  
#include <vector>  
#include <fstream>  
#include <sstream> 
#include <stdio.h>

using namespace std;
using namespace tensorflow;

int main()
{

    std::vector<double> feature_value;
    std::vector<std::string> feature_name;
    std::string model_path = "../models/GCN_rc.pb";
    std::string input_node_name = "Placeholder";
    std::string output_node_name = "outputs/Relu";
    string input_file = "../rc_OTA_asap7_norm.csv";
    ifstream inFile(input_file, ios::in);
    string lineStr;  
    double array[1000][60];
    double x_test[300][54];
    double y_test[300][4];
    int i,j;
    i=0;
    //read data in x_test and y_test
    while (getline(inFile, lineStr))  
    {  
        j=0;
        stringstream ss(lineStr);  
        string str;     
        while (getline(ss, str, ','))  
        {
            istringstream iss(str);
            iss >> array[i][j];
            if(i==0&&j<54)feature_value.push_back(array[i][j]);
            j++;
        }
        i++;      
    }

    Session* session;
  Status status = NewSession(SessionOptions(), &session); //create new session

  if (!status.ok()) {
    cout << status.ToString() << "\n";
    return -1;
  }else{
    cout << "Session successfully created.\n";
  }

  GraphDef graphdef; //Graph Definition for current model
  Status status_load = ReadBinaryProto(Env::Default(), model_path, &graphdef);
  if (!status_load.ok()){ 
    std::cout << "ERROR: Loading model failed..." << model_path << std::endl; 
    std::cout << status_load.ToString() << std::endl;  
    return -1;
  }else{
    cout << "Model successfully loaded." << endl;
  }

  Status status_create = session->Create(graphdef); //load the graph into session
  if (!status_create.ok()){ 
    std::cout << "ERROR: Creating graph in session failed..." << status_create.ToString() << std::endl; 
    return -1;
  }else{
    cout << "Graph successfully read." << endl;
  }

  int feature_size = feature_value.size();
  Tensor X(DT_DOUBLE, TensorShape({ 1, feature_size })); //define a Tensor X, by default is [1, feature_size]
  auto plane_tensor = X.tensor<double,2>(); //pointer of X
  for (int i = 0; i < feature_size; i++){
      plane_tensor(0,i) = feature_value.at(i); //load data into X
  }

  std::vector<std::pair<std::string,Tensor>> inputs = {{input_node_name,X}}; //input feed_dict
  std::vector<Tensor> outputs; //output tensor
  Status status_run = session->Run(inputs, {output_node_name}, {}, &outputs); //run
  if (!status_run.ok()) {
      std::cout << "ERROR: RUN failed..."  << std::endl;
      std::cout << status_run.ToString() << "\n";
      return -1;
  }else{
      cout << "Prection successfully run." << endl;
  }

  auto out_tensor = outputs[0].tensor<double,2>(); // by default output is [1, 1]
  std::cout <<  out_tensor(0, 0) << std::endl;


    return 0;
}