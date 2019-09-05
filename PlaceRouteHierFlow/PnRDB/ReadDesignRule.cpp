#include "PnRdatabase.h"

long int PnRdatabase::get_number(string str) {
  long int val=0;
  for (unsigned int number=0; number < str.length(); number++) {
    if (isdigit (str[number]))
    val=(10*val)+(str[number]-48);
  }
  return val;
}

void PnRdatabase::ReadDesignRule(string drfile) {
  cout << "PnRDB-Info: reading design rule file " << drfile <<endl;

  ifstream fin;
  fin.open(drfile.c_str());
  string def;

  vector<string> temp;
  vector<string> temp2;

  map<string, vector<int> > SpaceNumTmp;
  //vector<int> V1_SpaceNumTmp;
  //vector<int> V2_SpaceNumTmp;
  //vector<int> V3_SpaceNumTmp;
  //vector<int> V4_SpaceNumTmp;
  //vector<int> V5_SpaceNumTmp;
  //vector<int> V6_SpaceNumTmp;
  //vector<int> V7_SpaceNumTmp;

  //vector<int> M1_SpaceNumTmp;
  //vector<int> M2_SpaceNumTmp;
  //vector<int> M3_SpaceNumTmp;
  //vector<int> M4_SpaceNumTmp;
  //vector<int> M5_SpaceNumTmp;
  //vector<int> M6_SpaceNumTmp;
  //vector<int> M7_SpaceNumTmp;
  //vector<int> M8_SpaceNumTmp;

  map<string, vector<int> > Entmp;
  //vector<int> V1M1Entmp;
  //vector<int> V1M2Entmp;
  //vector<int> V2M2Entmp;
  //vector<int> V2M3Entmp;
  //vector<int> V3M3Entmp;
  //vector<int> V3M4Entmp;
  //vector<int> V4M4Entmp;
  //vector<int> V4M5Entmp;
  //vector<int> V5M5Entmp;
  //vector<int> V5M6Entmp;
  //vector<int> V6M6Entmp;
  //vector<int> V6M7Entmp;
  //vector<int> V7M7Entmp;
  //vector<int> V7M8Entmp;

  size_t found;

  int *p=0;
  int p_temp=0;
  p=&p_temp;

  //design rule parsing

  while(!fin.eof()){
    getline(fin, def);
    if((found=def.find("V1.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("@"))!=string::npos) {
        //cout << "def2: "<< def <<endl;
        temp=split_by_spaces(def);
        //cout <<temp[temp.size()-3]<<endl;
        drData.MinWidth["V1"] = stoi(temp[temp.size()-3]);
      }
    }
    if((found=def.find("V1.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      getline(fin, def);
      if((found=def.find("V1.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp=split_by_spaces(def);
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["V1"].push_back(get_number(temp2[1]));
          //V1_SpaceNumTmp.push_back(get_number(temp2[1]));
        }
      }
    }
    if((found=def.find("V1.M1.EN.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V1.M1.EN.1"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          //cout<<temp[q]<<endl;
          Entmp["V1M1"].push_back(stod(temp[q])*1000);
          //V1M1Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V1.M2.EN.2"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V1.M2.EN.2"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V1M2"].push_back(stod(temp[q])*1000);
          //V1M2Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V2.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("@"))!=string::npos) {
        //cout << "def2: "<< def <<endl;
        temp=split_by_spaces(def);
        //cout <<temp[temp.size()-3]<<endl;
        drData.MinWidth["V2"] = stoi(temp[temp.size()-3]);
      }
    }
    if((found=def.find("V2.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      getline(fin, def);
      if((found=def.find("V2.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp=split_by_spaces(def);
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["V2"].push_back(get_number(temp2[1]));
          //V2_SpaceNumTmp.push_back(get_number(temp2[1]));
        }
      }
    }
    if((found=def.find("V2.M2.EN.1"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V2.M2.EN.1"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V2M2"].push_back(stod(temp[q])*1000);
          //V2M2Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V2.M3.EN.2"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V2.M3.EN.2"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V2M3"].push_back(stod(temp[q])*1000);
          //V2M3Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V3.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("@"))!=string::npos) {
        //cout << "def2: "<< def <<endl;
        temp=split_by_spaces(def);
        //cout <<temp[temp.size()-3]<<endl;
        drData.MinWidth["V3"] = stoi(temp[temp.size()-3]);
      }
    }
    if((found=def.find("V3.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      getline(fin, def);
      if((found=def.find("V3.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp=split_by_spaces(def);
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["V3"].push_back(get_number(temp2[1]));
          //V3_SpaceNumTmp.push_back(get_number(temp2[1]));
        }
      }
    }
    if((found=def.find("V3.M3.EN.1"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V3.M3.EN.1"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V3M3"].push_back(stod(temp[q])*1000);
          //V3M3Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V3.M4.EN.2"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V3.M4.EN.2"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V3M4"].push_back(stod(temp[q])*1000);
          //V3M4Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }

    if((found=def.find("V4.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V4.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["V4"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("V4.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V4.S"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp=split_by_spaces(def);
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["V4"].push_back(get_number(temp2[1]));
          //V4_SpaceNumTmp.push_back(get_number(temp2[1]));
        }
      }
    }
    if((found=def.find("V4.M4.EN.1"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V4.M4.EN.1"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V4M4"].push_back(stod(temp[q])*1000);
          //V4M4Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V4.M5.EN.2"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V4.M5.EN.2"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V4M5"].push_back(stod(temp[q])*1000);
          //V4M5Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }

    if((found=def.find("V5.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V5.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["V5"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("V5.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V5.S"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp=split_by_spaces(def);
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["V5"].push_back(get_number(temp2[1]));
          //V5_SpaceNumTmp.push_back(get_number(temp2[1]));
        }
      }
    }
    if((found=def.find("V5.M5.EN.1"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V5.M5.EN.1"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V5M5"].push_back(stod(temp[q])*1000);
          //V5M5Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V5.M6.EN.2"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V5.M6.EN.2"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V5M6"].push_back(stod(temp[q])*1000);
          //V5M6Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V6.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V6.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["V6"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("V6.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V6.S"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp=split_by_spaces(def);
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["V6"].push_back(get_number(temp2[1]));
          //V6_SpaceNumTmp.push_back(get_number(temp2[1]));
        }
      }
    }
    if((found=def.find("V6.M6.EN.1"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V6.M6.EN.1"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V6M6"].push_back(stod(temp[q])*1000);
          //V6M6Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V6.M7.EN.2"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V6.M7.EN.2"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V6M7"].push_back(stod(temp[q])*1000);
          //V6M7Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V7.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V7.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["V7"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("V7.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("V7.S"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp=split_by_spaces(def);
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["V7"].push_back(get_number(temp2[1]));
          //V7_SpaceNumTmp.push_back(get_number(temp2[1]));
        }
      }
    }
    if((found=def.find("V7.M7.EN.1"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V7.M7.EN.1"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V7M7"].push_back(stod(temp[q])*1000);
          //V7M7Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("V7.M8.EN.2"))!=string::npos) {
      getline(fin, def);
      if((found=def.find("V7.M8.EN.2"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while(!(temp[0].compare("GOOD")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        for(unsigned int q=1;q<temp.size();q++){
          Entmp["V7M8"].push_back(stod(temp[q])*1000);
          //V7M8Entmp.push_back(stod(temp[q])*1000);
        }
      }
    }
    if((found=def.find("M1.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M1.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M1"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M1.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M1.S"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while((temp[0].compare("@")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        if((found=def.find("EXTERNAL"))!=string::npos) {
          temp=split_by_spaces(def);
          for(unsigned int q=0;q<temp.size();q++){
            //cout<<"temp[q]: "<<temp[q]<<endl;
            if(temp[q].compare("<")==0){
              //cout<<"Rule Num in Micron: "<< temp[q+1]<<endl;
              SpaceNumTmp["M1"].push_back(stod(temp[q+1])*1000);
              //M1_SpaceNumTmp.push_back(stod(temp[q+1])*1000);
              break;
            }
          }
        }
      }
    }
    if((found=def.find("M2.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M2.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M2"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M2.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M2.S"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while((temp[0].compare("@")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        if((found=def.find("EXTERNAL"))!=string::npos) {
          temp=split_by_spaces(def);
          for(unsigned int q=0;q<temp.size();q++){
            //cout<<"temp[q]: "<<temp[q]<<endl;
            if(temp[q].compare("<")==0){
              //cout<<"Rule Num in Micron: "<< temp[q+1]<<endl;
              SpaceNumTmp["M2"].push_back(stod(temp[q+1])*1000);
              //M2_SpaceNumTmp.push_back(stod(temp[q+1])*1000);
              break;
            }
          }
        }
      }
    }
    if((found=def.find("M3.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M3.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M3"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M3.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M3.S"))!=string::npos) {
        getline(fin, def);
        temp=split_by_spaces(def);
        while((temp[0].compare("@")==0)) {
          getline(fin, def);
          temp=split_by_spaces(def);
        }
        if((found=def.find("EXTERNAL"))!=string::npos) {
          temp=split_by_spaces(def);
          for(unsigned int q=0;q<temp.size();q++){
            //cout<<"temp[q]: "<<temp[q]<<endl;
            if(temp[q].compare("<")==0){
              //cout<<"Rule Num in Micron: "<< temp[q+1]<<endl;
              SpaceNumTmp["M3"].push_back(stod(temp[q+1])*1000);
              //M3_SpaceNumTmp.push_back(stod(temp[q+1])*1000);
              break;
            }
          }
        }
      }
    }
    if((found=def.find("M4.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M4.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M4"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M4.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M4.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          temp2=get_true_word(found,def,0,';',p);
          //cout <<"after is: "<<temp2[1]<<endl;
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["M4"].push_back(stoi(temp2[1]));
          //M4_SpaceNumTmp.push_back(stoi(temp2[1]));
          //cout<<"stoi(temp2[1]) :"<<stoi(temp2[1])<<endl;
        }
      }
    }
    if((found=def.find("M4.AUX.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M4.AUX.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          temp=split_by_spaces(def);
          drData.TrkSpacing["M4"] = stoi(temp[temp.size()-3]);
          //cout<<"M4 Track Spacing: "<<drData.TrkSpacing["M4"]<<endl;
        }
      }
    }
    if((found=def.find("M5.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M5.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M5"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M5.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M5.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["M5"].push_back(stoi(temp2[1]));
          //M5_SpaceNumTmp.push_back(stoi(temp2[1]));
          //cout<<"stoi(temp2[1]) :"<<stoi(temp2[1])<<endl;
        }
      }
    }
    if((found=def.find("M5.AUX.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M5.AUX.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          temp=split_by_spaces(def);
          drData.TrkSpacing["M5"] = stoi(temp[temp.size()-3]);
          //cout<<"M5 Track Spacing: "<<drData.TrkSpacing["M5"]<<endl;
        }
      }
    }
    if((found=def.find("M6.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M6.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M6"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M6.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M6.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["M6"].push_back(stoi(temp2[1]));
          //M6_SpaceNumTmp.push_back(stoi(temp2[1]));
          //cout<<"stoi(temp2[1]) :"<<stoi(temp2[1])<<endl;
        }
      }
    }
    if((found=def.find("M6.AUX.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M6.AUX.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          temp=split_by_spaces(def);
          drData.TrkSpacing["M6"] = stoi(temp[temp.size()-3]);
          //cout<<"M6 Track Spacing: "<<drData.TrkSpacing["M6"]<<endl;
        }
      }
    }
    if((found=def.find("M7.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M7.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M7"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M7.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M7.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          //cout <<temp[1]<<endl;
          temp2=get_true_word(found,def,0,';',p);
        //cout << "spacing rule dist.: "<<get_number(temp2[1])<<endl;
          SpaceNumTmp["M7"].push_back(stoi(temp2[1]));
          //M7_SpaceNumTmp.push_back(stoi(temp2[1]));
          //cout<<"stoi(temp2[1]) :"<<stoi(temp2[1])<<endl;
        }
      }
    }
    if((found=def.find("M7.AUX.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M7.AUX.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          temp=split_by_spaces(def);
          drData.TrkSpacing["M7"] = stoi(temp[temp.size()-3]);
          //cout<<"M7 Track Spacing: "<<drData.TrkSpacing["M7"]<<endl;
        }
      }
    }
    if((found=def.find("M8.W.1"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M8.W.1"))!=string::npos) {
        getline(fin, def);
        if((found=def.find("@"))!=string::npos) {
          //cout << "def2: "<< def <<endl;
          temp=split_by_spaces(def);
          //cout <<"Test V4: "<<temp[temp.size()-3]<<endl;
          drData.MinWidth["M8"] = stoi(temp[temp.size()-3]);
        }
      }
    }
    if((found=def.find("M8.S"))!=string::npos) {
      //cout << "def1: "<< def <<endl;
      getline(fin, def);
      if((found=def.find("M8.S"))!=string::npos) {
        getline(fin, def);
        getline(fin, def);
        if((found=def.find("is"))!=string::npos) {
          //cout <<temp[1]<<endl;
          temp=split_by_spaces(def);
          //cout <<"spacing rule dist: "<<temp[temp.size()-3]<<endl;
          SpaceNumTmp["M8"].push_back(stoi(temp[temp.size()-3]));
          //M8_SpaceNumTmp.push_back(stoi(temp[temp.size()-3]));
        }
      }
    }
  }
  fin.close();

  //cout<<"Via1 Min.Width: "<<drData.MinWidth["V1"]<<endl;
  //cout<<"Via2 Min.Width: "<<drData.MinWidth["V2"]<<endl;
  //cout<<"Via3 Min.Width: "<<drData.MinWidth["V3"]<<endl;
  //cout<<"Via4 Min.Width: "<<drData.MinWidth["V4"]<<endl;
  //cout<<"Via5 Min.Width: "<<drData.MinWidth["V5"]<<endl;
  //cout<<"Via6 Min.Width: "<<drData.MinWidth["V6"]<<endl;
  //cout<<"Via7 Min.Width: "<<drData.MinWidth["V7"]<<endl;

  drData.MaxSpace["V1"] = *max_element(SpaceNumTmp["V1"].begin(), SpaceNumTmp["V1"].end());
  //cout <<"V1 Spa. Max: "<<drData.MaxSpace["V1"]<<endl;
  drData.MaxSpace["V2"] = *max_element(SpaceNumTmp["V2"].begin(), SpaceNumTmp["V2"].end());
  //cout <<"V2 Spa. Max: "<<drData.MaxSpace["V2"]<<endl;
  drData.MaxSpace["V3"] = *max_element(SpaceNumTmp["V3"].begin(), SpaceNumTmp["V3"].end());
  //cout <<"V3 Spa. Max: "<<drData.MaxSpace["V3"]<<endl;
  drData.MaxSpace["V4"] = *max_element(SpaceNumTmp["V4"].begin(), SpaceNumTmp["V4"].end());
  //cout <<"V4 Spa. Max: "<<drData.MaxSpace["V4"]<<endl;
  drData.MaxSpace["V5"] = *max_element(SpaceNumTmp["V5"].begin(), SpaceNumTmp["V5"].end());
  //cout <<"V5 Spa. Max: "<<drData.MaxSpace["V5"]<<endl;
  drData.MaxSpace["V6"] = *max_element(SpaceNumTmp["V6"].begin(), SpaceNumTmp["V6"].end());
  //cout <<"V6 Spa. Max: "<<drData.MaxSpace["V6"]<<endl;
  drData.MaxSpace["V7"] = *max_element(SpaceNumTmp["V7"].begin(), SpaceNumTmp["V7"].end());
  //cout <<"V7 Spa. Max: "<<drData.MaxSpace["V7"]<<endl;

  //cout<<"M1 Min.Width: "<<drData.MinWidth["M1"]<<endl;
  //cout<<"M2 Min.Width: "<<drData.MinWidth["M2"]<<endl;
  //cout<<"M3 Min.Width: "<<drData.MinWidth["M3"]<<endl;
  //cout<<"M4 Min.Width: "<<drData.MinWidth["M4"]<<endl;
  //cout<<"M5 Min.Width: "<<drData.MinWidth["M5"]<<endl;
  //cout<<"M6 Min.Width: "<<drData.MinWidth["M6"]<<endl;
  //cout<<"M7 Min.Width: "<<drData.MinWidth["M7"]<<endl;

  drData.MaxSpace["M1"] = *max_element(SpaceNumTmp["M1"].begin(), SpaceNumTmp["M1"].end());
  //cout <<"M1 Spa. Max: "<<drData.MaxSpace["M1"]<<endl;
  drData.MaxSpace["M2"] = *max_element(SpaceNumTmp["M2"].begin(), SpaceNumTmp["M2"].end());
  //cout <<"M2 Spa. Max: "<<drData.MaxSpace["M2"]<<endl;
  drData.MaxSpace["M3"] = *max_element(SpaceNumTmp["M3"].begin(), SpaceNumTmp["M3"].end());
  //cout <<"M3 Spa. Max: "<<drData.MaxSpace["M3"]<<endl;
  drData.MaxSpace["M4"] = *max_element(SpaceNumTmp["M4"].begin(), SpaceNumTmp["M4"].end());
  //cout <<"M4 Spa. Max: "<<drData.MaxSpace["M4"]<<endl;
  drData.MaxSpace["M5"] = *max_element(SpaceNumTmp["M5"].begin(), SpaceNumTmp["M5"].end());
  //cout <<"M5 Spa. Max: "<<drData.MaxSpace["M5"]<<endl;
  drData.MaxSpace["M6"] = *max_element(SpaceNumTmp["M6"].begin(), SpaceNumTmp["M6"].end());
  //cout <<"M6 Spa. Max: "<<drData.MaxSpace["M6"]<<endl;
  drData.MaxSpace["M7"] = *max_element(SpaceNumTmp["M7"].begin(), SpaceNumTmp["M7"].end());
  //cout <<"M7 Spa. Max: "<<drData.MaxSpace["M7"]<<endl;
  drData.MaxSpace["M8"] = *max_element(SpaceNumTmp["M8"].begin(), SpaceNumTmp["M8"].end());
  //cout <<"M8 Spa. Max: "<<drData.MaxSpace["M8"]<<endl;

  drData.EnMax["V1M1"] = *max_element(Entmp["V1M1"].begin(), Entmp["V1M1"].end());
  //cout<<"V1M1EnMax: "<<drData.EnMax["V1M1"]<<endl;
  drData.EnMax["V1M2"] = *max_element(Entmp["V1M2"].begin(), Entmp["V1M2"].end());
  //cout<<"V1M2EnMax: "<<drData.EnMax["V1M2"]<<endl;

  drData.EnMax["V2M2"] = *max_element(Entmp["V2M2"].begin(), Entmp["V2M2"].end());
  //cout<<"V2M2EnMax: "<<drData.EnMax["V2M2"]<<endl;
  drData.EnMax["V2M3"] = *max_element(Entmp["V2M3"].begin(), Entmp["V2M3"].end());
  //cout<<"V2M3EnMax: "<<drData.EnMax["V2M3"]<<endl;

  drData.EnMax["V3M3"] = *max_element(Entmp["V3M3"].begin(), Entmp["V3M3"].end());
  //cout<<"V3M3EnMax: "<<drData.EnMax["V3M3"]<<endl;
  drData.EnMax["V3M4"] = *max_element(Entmp["V3M4"].begin(), Entmp["V3M4"].end());
  //cout<<"V3M4EnMax: "<<drData.EnMax["V3M4"]<<endl;

  drData.EnMax["V4M4"] = *max_element(Entmp["V4M4"].begin(), Entmp["V4M4"].end());
  //cout<<"V4M4EnMax: "<<drData.EnMax["V4M4"]<<endl;
  drData.EnMax["V4M5"] = *max_element(Entmp["V4M5"].begin(), Entmp["V4M5"].end());
  //cout<<"V4M5EnMax: "<<drData.EnMax["V4M5"]<<endl;

  drData.EnMax["V5M5"] = *max_element(Entmp["V5M5"].begin(), Entmp["V5M5"].end());
  //cout<<"V5M5EnMax: "<<drData.EnMax["V5M5"]<<endl;
  drData.EnMax["V5M6"] = *max_element(Entmp["V5M6"].begin(), Entmp["V5M6"].end());
  //cout<<"V5M6EnMax: "<<drData.EnMax["V5M6"]<<endl;

  drData.EnMax["V6M6"] = *max_element(Entmp["V6M6"].begin(), Entmp["V6M6"].end());
  //cout<<"V6M6EnMax: "<<drData.EnMax["V6M6"]<<endl;
  drData.EnMax["V6M7"] = *max_element(Entmp["V6M7"].begin(), Entmp["V6M7"].end());
  //cout<<"V6M7EnMax: "<<drData.EnMax["V6M7"]<<endl;

  drData.EnMax["V7M7"] = *max_element(Entmp["V7M7"].begin(), Entmp["V7M7"].end());
  //cout<<"V7M7EnMax: "<<drData.EnMax["V7M7"]<<endl;
  drData.EnMax["V7M8"] = *max_element(Entmp["V7M8"].begin(), Entmp["V7M8"].end());
  //cout<<"V7M8EnMax: "<<drData.EnMax["V7M8"]<<endl;


  drData.grid_unit_x["M1"] = 2*(drData.MaxSpace["M1"]+drData.MinWidth["V1"]+2*drData.EnMax["V1M1"])+10;
  drData.grid_unit_y["M1"] = 2*(drData.MaxSpace["M1"]+drData.MinWidth["V1"]+2*drData.EnMax["V1M1"])+10;
  //cout <<"M1 Grid Pitch x : "<<drData.grid_unit_x["M1"]<<endl;
  //cout <<"M1 Grid Pitch y : "<<drData.grid_unit_y["M1"]<<endl;

  drData.grid_unit_x["M2"] = 2*(drData.MaxSpace["M2"]+drData.MinWidth["V1"]+2*drData.EnMax["V1M2"])+10;
  drData.grid_unit_y["M2"] = 2*(drData.MaxSpace["M2"]+drData.MinWidth["V1"]+2*drData.EnMax["V1M2"])+10;
  //cout <<"M2 Grid Pitch x : "<<drData.grid_unit_x["M2"]<<endl;
  //cout <<"M2 Grid Pitch y : "<<drData.grid_unit_y["M2"]<<endl;

  drData.grid_unit_x["M3"] = 2*(drData.MaxSpace["M3"]+drData.MinWidth["V2"]+2*drData.EnMax["V2M3"])+10;
  drData.grid_unit_y["M3"] = 2*(drData.MaxSpace["M3"]+drData.MinWidth["V2"]+2*drData.EnMax["V2M3"])+10;
  //cout <<"M3 Grid Pitch x : "<<drData.grid_unit_x["M3"]<<endl;
  //cout <<"M3 Grid Pitch y : "<<drData.grid_unit_y["M3"]<<endl;

  drData.grid_unit_x["M4"] = 2*2*(drData.MaxSpace["M4"]+drData.MaxSpace["M4"]+2);
  drData.grid_unit_y["M4"] = 2*2*(drData.TrkSpacing["M4"]+drData.MinWidth["M4"]);
  //cout <<"M4 Grid Pitch x : "<<drData.grid_unit_x["M4"]<<endl;
  //cout <<"M4 Grid Pitch y : "<<drData.grid_unit_y["M4"]<<endl;

  drData.grid_unit_x["M5"] = 2*2*(drData.TrkSpacing["M5"]+drData.MinWidth["M5"]);
  drData.grid_unit_y["M5"] = 2*2*(drData.MaxSpace["M5"]+drData.MaxSpace["M5"]+2);
  //cout <<"M5 Grid Pitch x : "<<drData.grid_unit_x["M5"]<<endl;
  //cout <<"M5 Grid Pitch y : "<<drData.grid_unit_y["M5"]<<endl;

  drData.grid_unit_x["M6"] = 2*2*(drData.MaxSpace["M6"]+drData.MaxSpace["M6"]+2);
  drData.grid_unit_y["M6"] = 2*2*(drData.TrkSpacing["M6"]+drData.MinWidth["M6"]);
  //cout <<"M6 Grid Pitch x : "<<drData.grid_unit_x["M6"]<<endl;
  //cout <<"M6 Grid Pitch y : "<<drData.grid_unit_y["M6"]<<endl;

  drData.grid_unit_x["M7"] = 2*2*(drData.TrkSpacing["M7"]+drData.MinWidth["M7"]);
  drData.grid_unit_y["M7"] = 2*2*(drData.MaxSpace["M7"]+drData.MaxSpace["M7"]+2);
  //cout <<"M7 Grid Pitch x : "<<drData.grid_unit_x["M7"]<<endl;
  //cout <<"M7 Grid Pitch y : "<<drData.grid_unit_y["M7"]<<endl;

  //added by yg
  PnRDB::metal_info temp_metal_info;
  PnRDB::via_info temp_via_info;
  vector<int> dis;
  int minimum;
  if(DRC_info.Metal_info.size()==0){
      //M1
      temp_metal_info.width = drData.MinWidth["M1"];
      temp_metal_info.name = "M1";
      temp_metal_info.grid_unit_x = drData.grid_unit_x["M1"];
      temp_metal_info.grid_unit_y = drData.grid_unit_y["M1"];
      dis = SpaceNumTmp["M1"];
      minimum = dis[0];
      for(unsigned int i = 0;i<dis.size();i++){
           if(dis[i]<minimum){
               minimum = dis[i];
             }
         }
      temp_metal_info.dist_ss = minimum;
      temp_metal_info.direct = 0;
      DRC_info.Metal_info.push_back(temp_metal_info); //store metal_info
      dis.clear();
      
      //M2
      temp_metal_info.width = drData.MinWidth["M2"];
      temp_metal_info.name = "M2";
      temp_metal_info.grid_unit_x = drData.grid_unit_x["M2"];
      temp_metal_info.grid_unit_y = drData.grid_unit_y["M2"];
      dis = SpaceNumTmp["M2"];
      minimum = dis[0];
      for(unsigned int i = 0;i<dis.size();i++){
           if(dis[i]<minimum){
               minimum = dis[i];
             }
         }
      temp_metal_info.dist_ss = minimum;
      temp_metal_info.direct = 1;
      DRC_info.Metal_info.push_back(temp_metal_info); //store metal_info
      dis.clear();
      
      //M3
      temp_metal_info.width = drData.MinWidth["M3"];
      temp_metal_info.name = "M3";
      temp_metal_info.grid_unit_x = drData.grid_unit_x["M3"];
      temp_metal_info.grid_unit_y = drData.grid_unit_y["M3"];
      dis = SpaceNumTmp["M3"];
      minimum = dis[0];
      for(unsigned int i = 0;i<dis.size();i++){
           if(dis[i]<minimum){
               minimum = dis[i];
             }
         }
      temp_metal_info.dist_ss = minimum;
      temp_metal_info.direct = 0;
      DRC_info.Metal_info.push_back(temp_metal_info); //store metal_info
      dis.clear();
     
      //M4
      temp_metal_info.width = drData.MinWidth["M4"];
      temp_metal_info.name = "M4";
      temp_metal_info.grid_unit_x = drData.grid_unit_x["M4"];
      temp_metal_info.grid_unit_y = drData.grid_unit_y["M4"];
      dis = SpaceNumTmp["M4"];
      minimum = dis[0];
      for(unsigned int i = 0;i<dis.size();i++){
           if(dis[i]<minimum){
               minimum = dis[i];
             }
         }
      temp_metal_info.dist_ss = minimum;
      temp_metal_info.direct = 1;
      DRC_info.Metal_info.push_back(temp_metal_info); //store metal_info
      dis.clear();
      
      //M5
      temp_metal_info.width = drData.MinWidth["M5"];
      temp_metal_info.name = "M5";
      temp_metal_info.grid_unit_x = drData.grid_unit_x["M5"];
      temp_metal_info.grid_unit_y = drData.grid_unit_y["M5"];
      dis = SpaceNumTmp["M5"];
      minimum = dis[0];
      for(unsigned int i = 0;i<dis.size();i++){
           if(dis[i]<minimum){
               minimum = dis[i];
             }
         }
      temp_metal_info.dist_ss = minimum;
      temp_metal_info.direct = 0;
      DRC_info.Metal_info.push_back(temp_metal_info); //store metal_info
      dis.clear();
      
      //M6
      temp_metal_info.width = drData.MinWidth["M6"];
      temp_metal_info.name = "M6";
      temp_metal_info.grid_unit_x = drData.grid_unit_x["M6"];
      temp_metal_info.grid_unit_y = drData.grid_unit_y["M6"];
      dis = SpaceNumTmp["M6"];
      minimum = dis[0];
      for(unsigned int i = 0;i<dis.size();i++){
           if(dis[i]<minimum){
               minimum = dis[i];
             }
         }
      temp_metal_info.dist_ss = minimum;
      temp_metal_info.direct = 1;
      DRC_info.Metal_info.push_back(temp_metal_info); //store metal_info
      dis.clear();
      
      //M7
      temp_metal_info.width = drData.MinWidth["M7"];
      temp_metal_info.name = "M7";
      temp_metal_info.grid_unit_x = drData.grid_unit_x["M7"];
      temp_metal_info.grid_unit_y = drData.grid_unit_y["M7"];
      dis = SpaceNumTmp["M7"];
      minimum = dis[0];
      for(unsigned int i = 0;i<dis.size();i++){
           if(dis[i]<minimum){
               minimum = dis[i];
             }
         }
      temp_metal_info.dist_ss = minimum;
      temp_metal_info.direct = 0;
      DRC_info.Metal_info.push_back(temp_metal_info); //store metal_info
      dis.clear();
      
      //V1
      temp_via_info.width = drData.MinWidth["V1"];
      temp_via_info.name = "V1";
      temp_via_info.lower_metal_index = 0;
      temp_via_info.upper_metal_index = 1;
      temp_via_info.dist_ss = drData.MaxSpace["V1"];
      temp_via_info.cover_l = drData.EnMax["V1M1"];
      temp_via_info.cover_u = drData.EnMax["V1M2"];
      DRC_info.Via_info.push_back(temp_via_info); //store via_info
      
      //V2
      temp_via_info.width = drData.MinWidth["V2"];
      temp_via_info.name = "V2";
      temp_via_info.lower_metal_index = 1;
      temp_via_info.upper_metal_index = 2;
      temp_via_info.dist_ss = drData.MaxSpace["V2"];
      temp_via_info.cover_l = drData.EnMax["V2M2"];
      temp_via_info.cover_u = drData.EnMax["V2M3"];
      DRC_info.Via_info.push_back(temp_via_info); //store via_info
      
      //V3
      temp_via_info.width = drData.MinWidth["V3"];
      temp_via_info.name = "V3";
      temp_via_info.lower_metal_index = 2;
      temp_via_info.upper_metal_index = 3;
      temp_via_info.dist_ss = drData.MaxSpace["V3"];
      temp_via_info.cover_l = drData.EnMax["V3M3"];
      temp_via_info.cover_u = drData.EnMax["V3M4"];
      DRC_info.Via_info.push_back(temp_via_info); //store via_info
      
      //V4
      temp_via_info.width = drData.MinWidth["V4"];
      temp_via_info.name = "V4";
      temp_via_info.lower_metal_index = 3;
      temp_via_info.upper_metal_index = 4;
      temp_via_info.dist_ss = drData.MaxSpace["V4"];
      temp_via_info.cover_l = drData.EnMax["V4M4"];
      temp_via_info.cover_u = drData.EnMax["V4M5"];
      DRC_info.Via_info.push_back(temp_via_info); //store via_info
      
      //V5
      temp_via_info.width = drData.MinWidth["V5"];
      temp_via_info.name = "V5";
      temp_via_info.lower_metal_index = 4;
      temp_via_info.upper_metal_index = 5;
      temp_via_info.dist_ss = drData.MaxSpace["V5"];
      temp_via_info.cover_l = drData.EnMax["V5M5"];
      temp_via_info.cover_u = drData.EnMax["V5M6"];
      DRC_info.Via_info.push_back(temp_via_info); //store via_info
      
      //V6
      temp_via_info.width = drData.MinWidth["V6"];
      temp_via_info.name = "V6";
      temp_via_info.lower_metal_index = 5;
      temp_via_info.upper_metal_index = 6;
      temp_via_info.dist_ss = drData.MaxSpace["V6"];
      temp_via_info.cover_l = drData.EnMax["V6M6"];
      temp_via_info.cover_u = drData.EnMax["V6M7"];
      DRC_info.Via_info.push_back(temp_via_info); //store via_info
      
    }
  DRC_info.MaxLayer = 6;

  DRC_info.Metalmap["M1"] = 0;
  DRC_info.Metalmap["M2"] = 1;
  DRC_info.Metalmap["M3"] = 2;
  DRC_info.Metalmap["M4"] = 3;
  DRC_info.Metalmap["M5"] = 4;
  DRC_info.Metalmap["M6"] = 5;
  DRC_info.Metalmap["M7"] = 6;

  DRC_info.Viamap["V1"] = 0;
  DRC_info.Viamap["V2"] = 1;
  DRC_info.Viamap["V3"] = 2;
  DRC_info.Viamap["V4"] = 3;
  DRC_info.Viamap["V5"] = 4;
  DRC_info.Viamap["V6"] = 5;
  //DRC_info.Viamap["V7"] = 6;
  
  //add
  for(unsigned int i=0;i<DRC_info.Metal_info.size();i++){
       DRC_info.metal_weight.push_back(1);
     }
  
  for(unsigned int i=0;i<DRC_info.Via_info.size();i++){
       PnRDB::ViaModel temp_viamodel;
       temp_viamodel.name = DRC_info.Via_info[i].name;
       temp_viamodel.ViaIdx = i;
       temp_viamodel.LowerIdx = i;
       temp_viamodel.UpperIdx = i+1;
       PnRDB::point temp_point;
       //LL
       temp_point.x = 0-DRC_info.Via_info[i].width/2;
       temp_point.y = 0-DRC_info.Via_info[i].width/2;
       temp_viamodel.ViaRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Via_info[i].width/2;
       temp_point.y = 0+DRC_info.Via_info[i].width/2;
       temp_viamodel.ViaRect.push_back(temp_point);
/*       
       //LL LowerRect
       if(DRC_info.Metal_info[i].direct==0){
       temp_point.x = 0-DRC_info.Metal_info[i].width/2;
       temp_point.y = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Metal_info[i].width/2;
       temp_point.y = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       }else{
       temp_point.y = 0-DRC_info.Metal_info[i].width/2;
       temp_point.x = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       //UR
       temp_point.y = 0+DRC_info.Metal_info[i].width/2;
       temp_point.x = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       } 
       
       //LL UpperRect
       if(DRC_info.Metal_info[i+1].direct==0){
       temp_point.x = 0-DRC_info.Metal_info[i+1].width/2;
       temp_point.y = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Metal_info[i+1].width/2;
       temp_point.y = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       }else{
       temp_point.y = 0-DRC_info.Metal_info[i+1].width/2;
       temp_point.x = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       //UR
       temp_point.y = 0+DRC_info.Metal_info[i+1].width/2;
       temp_point.x = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       } 
*/
       //LL LowerRect
       if(DRC_info.Metal_info[i].direct==0){
       temp_point.x = 0-DRC_info.Via_info[i].width/2;
       temp_point.y = 0-DRC_info.Via_info[i].width/2-DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Via_info[i].width/2;
       temp_point.y = 0+DRC_info.Via_info[i].width/2+DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       }else{
       temp_point.y = 0-DRC_info.Via_info[i].width/2;
       temp_point.x = 0-DRC_info.Via_info[i].width/2-DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       //UR
       temp_point.y = 0+DRC_info.Via_info[i].width/2;
       temp_point.x = 0+DRC_info.Via_info[i].width/2+DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       } 
       
       //LL UpperRect
       if(DRC_info.Metal_info[i+1].direct==0){
       temp_point.x = 0-DRC_info.Via_info[i].width/2;
       temp_point.y = 0-DRC_info.Via_info[i].width/2-DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Via_info[i].width/2;
       temp_point.y = 0+DRC_info.Via_info[i].width/2+DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       }else{
       temp_point.y = 0-DRC_info.Via_info[i].width/2;
       temp_point.x = 0-DRC_info.Via_info[i].width/2-DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       //UR
       temp_point.y = 0+DRC_info.Via_info[i].width/2;
       temp_point.x = 0+DRC_info.Via_info[i].width/2+DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       } 
      DRC_info.Via_model.push_back(temp_viamodel);
    }
  
  //added by yg
  DRC_info.MaskID_Metal.push_back("19");
  DRC_info.MaskID_Metal.push_back("20");
  DRC_info.MaskID_Metal.push_back("30");
  DRC_info.MaskID_Metal.push_back("40");
  DRC_info.MaskID_Metal.push_back("50");
  DRC_info.MaskID_Metal.push_back("60");
  DRC_info.MaskID_Metal.push_back("70");

  DRC_info.MaskID_Via.push_back("21");
  DRC_info.MaskID_Via.push_back("25");
  DRC_info.MaskID_Via.push_back("35");
  DRC_info.MaskID_Via.push_back("45");
  DRC_info.MaskID_Via.push_back("55");
  DRC_info.MaskID_Via.push_back("65");
  DRC_info.MaskID_Via.push_back("75");
  
}
