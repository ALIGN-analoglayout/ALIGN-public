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
    Session* session;
    Status status = NewSession(SessionOptions(), &session); //create new session
    if (!status.ok()) {
        cout << status.ToString() << "\n";
        return -1;
    }else{
    	cout << "Session successfully created.\n";
    }

    string model_path="../models/Gain.pb";
    GraphDef graphdef; //Graph Definition for current model
    Status status_load = ReadBinaryProto(Env::Default(), model_path, &graphdef);
    if (!status_load.ok()){	
    	std::cout << "ERROR: Loading model failed..." << model_path << std::endl;	
    	std:cout << status_load.ToString() << std::endl;	
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

    string input_file = "../rc_OTA_asap7_norm.csv";
    ifstream inFile(input_file, ios::in);
    string lineStr;  
    float array[1000][60];
    float x_test[300][54];
    float y_test[300][4];
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
            j++;
        }
        i++;      
    }  


    Tensor X(DT_FLOAT, TensorShape({ 300, 54 })); //define a Tensor X
    auto plane_tensor = X.tensor<float,2>(); //pointer of X
    for (int i = 0; i < 300; i++){
        for(int j = 0; j < 54; j++)plane_tensor(i,j) = array[i+700][j]; //load data into X
    }
    std::vector<std::pair<std::string,Tensor>> inputs = {{"Gain/Placeholder",X}}; //input feed_dict
    std::vector<Tensor> outputs; //output tensor
    Status status_run = session->Run(inputs, {"Gain/outputs/Relu"}, {}, &outputs); //run
    if (!status_run.ok()) {
        std::cout << "ERROR: RUN failed..."  << std::endl;
        std::cout << status_run.ToString() << "\n";
        return -1;
    }else{
        cout << "Prection successfully run." << endl;
    }
    auto out_tensor = outputs[0].tensor<float,2>();
    for(int i = 0; i < 300; i++)
        for(int j = 0 ; j < 1; j++){
                    std::cout << out_tensor(i,j) << std::endl;
                }


    return 0;
}