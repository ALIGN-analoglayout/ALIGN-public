#include "PnRdatabase.h"

#include <cmath>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <assert.h>

static double parse_and_scale( const std::string& s, double unitScale)
{
  double scaled = stod(s)*unitScale;
  double result = round(scaled);
  if ( fabs( scaled - result) > 0.001) {
    std::cout << "ERROR: parse_and_scale " << s << " " << unitScale << " Rounded result differs too much from unrounded result (" << result << "," << scaled << ")" << std::endl;
  }
  return result;
}

bool PnRdatabase::ReadLEF(string leffile) {
  cout<<"PnRDB-Info: reading LEF file "<<leffile<<endl;
  ifstream fin;
  string def;
  size_t found;
  vector<string> temp;
  int *p;
  int p_temp=0;
  p=&p_temp;
  string macroName;
  string portEnd="END";
  string obsEnd="END";
  string pinEnd;
  string macroEnd;
  int width=-1, height=-1;
  vector<PnRDB::pin> macroPins;
  vector<PnRDB::contact> interMetals; //metal within each MACRO
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(leffile.c_str());
    int stage=0;
    bool skip_the_rest_of_stage_4 = false;
    while(fin.peek()!=EOF) {
      getline(fin, def);
      //cout<<def<<endl;
      // [wbxu] This function needs to be updated to support internal metals, currently we're lack of data
      if(stage==0) { // idle mode
	cout << "stage0.def: " << def << std::endl;
        if((found=def.find("MACRO"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          macroName=temp[1];
          macroEnd="END "+temp[1];
          //cout<<"Stage "<<stage<<" @ "<<macroName<<" ~~ "<<macroEnd<<endl;
          width=0; height=0;
          macroPins.clear();
          interMetals.clear();
          stage=1;
        }
      } else if (stage==1) { // within MACRO
        if((found=def.find("SIZE"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          width=parse_and_scale( temp[1], unitScale);
          height=parse_and_scale( temp[3], unitScale);
          //cout<<"Stage "<<stage<<" @ W "<<width<<"; H "<<height<<endl;
        } else if((found=def.find("PIN"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          macroPins.resize(macroPins.size()+1);
          macroPins.back().name=temp[1];
          pinEnd="END "+temp[1];
          //cout<<"Stage "<<stage<<" @ pin "<<macroPins.back().name<<"; end "<<pinEnd<<endl;
          stage=2;
        } else if((found=def.find("OBS"))!=string::npos) {
          //interMetals.resize(interMetals.size()+1);
          stage=4;
        } else if((found=def.find(macroEnd))!=string::npos) {
          PnRDB::lefMacro macroIns;
          macroIns.width=width;
          macroIns.height=height;
          macroIns.name=macroName;
          macroIns.macroPins=macroPins;
          macroIns.interMetals=interMetals;
          string key="_AspectRatio";
          std::size_t found = macroIns.name.find(key);
          if(found!=std::string::npos) { // different aspect ratio exists
            macroIns.master=macroIns.name.substr(0, found);
          } else { // different aspect ratio does not exist
            macroIns.master=macroIns.name;
          }
          if(lefData.find(macroIns.master)==lefData.end()) {
            std::vector<PnRDB::lefMacro> lefV; lefV.push_back(macroIns);
            lefData.insert( std::pair<string, std::vector<PnRDB::lefMacro> >(macroIns.master,lefV) );
            //lefData.insert( std::pair<string,PnRDB::lefMacro>(macroName,macroIns) );
          } else {
            lefData[macroIns.master].push_back(macroIns);
         }
          //cout<<"Stage "<<stage<<" @ insert macro data"<<endl;
          stage=0;
        } 
      } else if (stage==4) { // within OBS
	std::cout << "stage4.Def: " << def << std::endl;
        if((found=def.find("LAYER"))!=string::npos) {
	  skip_the_rest_of_stage_4 = false;
          temp=get_true_word(found,def,0,';',p);
          if (temp[1].front() == 'M') {
	    interMetals.resize(interMetals.size()+1);
	    interMetals.back().metal=temp[1];
	  } else {
	    skip_the_rest_of_stage_4 = true;
	  }
        } else if((found=def.find("RECT"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          int LLx=parse_and_scale( temp[1], unitScale);
          int LLy=parse_and_scale( temp[2], unitScale);
          int URx=parse_and_scale( temp[3], unitScale);
          int URy=parse_and_scale( temp[4], unitScale);
          PnRDB::bbox oBox; PnRDB::point tp;
          tp.x=LLx; tp.y=LLy;
          oBox.LL=tp;
          tp.x=URx; tp.y=URy;
          oBox.UR=tp;
	  if ( !skip_the_rest_of_stage_4) {
	    assert( interMetals.size() > 0);
	    interMetals.back().originBox=oBox;
	    interMetals.back().originCenter.x=(LLx+URx)/2;
	    interMetals.back().originCenter.y=(LLy+URy)/2;
	  }
        } else if((found=def.find(obsEnd))!=string::npos) {
          //cout<<"Stage "<<stage<<" @ port end "<<portEnd<<endl;
          stage=1;
        }
      } else if (stage==2) { // within PIN
        if((found=def.find("USE"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          macroPins.back().use=temp[1];
        } else if((found=def.find("DIRECTION"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          macroPins.back().type=temp[1];
          //cout<<"Stage "<<stage<<" @ pin type"<<macroPins.back().type<<endl;
        } else if((found=def.find("PORT"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          //macroPins.back().pinContacts.resize( macroPins.back().pinContacts.size()+1 );
          //cout<<"Stage "<<stage<<" @ new contact for pin"<<endl;
          stage=3;
        } else if((found=def.find(pinEnd))!=string::npos) {
          //cout<<"Stage" << stage<<" @ pin end "<<pinEnd<<endl;
          stage=1;
        } 
      } else if (stage==3) { // within PORT
        if((found=def.find("LAYER"))!=string::npos) {
          //Metal_Flag = true;
          temp=get_true_word(found,def,0,';',p);
          macroPins.back().pinContacts.resize( macroPins.back().pinContacts.size()+1 );
          macroPins.back().pinContacts.back().metal=temp[1];
          //cout<<"Stage "<<stage<<" @ contact layer "<<macroPins.back().pinContacts.back().metal<<endl;
        } else if((found=def.find("RECT"))!=string::npos) {
          //Metal_Flag = true;
          temp=get_true_word(found,def,0,';',p);
          int LLx=parse_and_scale( temp[1], unitScale);
          int LLy=parse_and_scale( temp[2], unitScale);
          int URx=parse_and_scale( temp[3], unitScale);
          int URy=parse_and_scale( temp[4], unitScale);
          PnRDB::bbox oBox; PnRDB::point tp;
          tp.x=LLx; tp.y=LLy;
          oBox.LL=tp;
          tp.x=URx; tp.y=URy;
          oBox.UR=tp;
          macroPins.back().pinContacts.back().originBox=oBox;
          macroPins.back().pinContacts.back().originCenter.x=(LLx+URx)/2;
          macroPins.back().pinContacts.back().originCenter.y=(LLy+URy)/2;
          //cout<<"Stage "<<stage<<" @ bbox ";
          //for(vector<PnRDB::point>::iterator it=macroPins.back().pinContacts.back().originBox.polygon.begin();it!=macroPins.back().pinContacts.back().originBox.polygon.end();++it) {
          //  cout<<" {"<<it->x<<","<<it->y<<"}";
          //}
          //cout<<endl<<"Stage "<<stage<<" @ center "<<macroPins.back().pinContacts.back().originCenter.x<<","<<macroPins.back().pinContacts.back().originCenter.y<<endl;
        } else if((found=def.find(portEnd))!=string::npos) {
          //cout<<"Stage "<<stage<<" @ port end "<<portEnd<<endl;
          if(macroPins.back().pinContacts.size()==0 or macroPins.back().pinContacts.back().metal==""){
             std::cout<<"Error: LEF Physical Pin information Missing"<<std::endl;
             assert(0);          
          }
          stage=2;
        }
      }
    }
    fin.close();
    return true;
  } catch(ifstream::failure& e) {
    cerr<<"PnRDB-Error: fail to read LEF file "<<endl;
  }
  return false;
}
