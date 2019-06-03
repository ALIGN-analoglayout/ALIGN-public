#include "capplacer.h"

int main(){
  vector<int> ki;
  vector<pair<string, string> > ki_name;
  pair<string, string> temp_name;

  temp_name.first = "C1+";
  temp_name.second = "C1-";
  ki.push_back(1);
  ki_name.push_back(temp_name);
  
  temp_name.first = "C2+";
  temp_name.second = "C2-";
  ki.push_back(3);
  ki_name.push_back(temp_name);


  temp_name.first = "C3+";
  temp_name.second = "C3-";
  ki.push_back(7);
  ki_name.push_back(temp_name);

  temp_name.first = "C4+";
  temp_name.second = "C4-";
  ki.push_back(9);
  ki_name.push_back(temp_name);
  
  string fpath=".";
  string unit_capacitor = "Cap_10f_1x1";
  string final_gds ="all_test";
  PnRDB::hierNode Temp_node;
  //Placer_Router_Cap PRC(ki, ki_name, fpath, unit_capacitor, final_gds);
  Placer_Router_Cap prc(fpath, Temp_node);
  
  return 0;
}



