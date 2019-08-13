#include "PnRdatabase.h"

//using namespace PnRDB;
// for Wenbin's development
//

#include <iostream>
#include <fstream>
#include <iomanip>
#include <time.h>

using namespace nlohmann;

unsigned short
JSON_Presentation (int font, int vp, int hp) {
    if (font < 0 || font > 3) font = 0;
    if (vp < 0 || vp > 2) vp = 0;
    if (hp < 0 || hp > 2) hp = 0;
    return font * 16 + vp * 4 + hp;
}

unsigned short
JSON_STrans (bool reflect, bool abs_angle, bool abs_mag) {
    return 32768 * reflect + 2 * abs_mag + abs_angle;
}

json JSON_TimeTime () {
    static short int year, month;
    time_t* now = (time_t *) malloc( sizeof( time_t ) );
    time (now);
    struct tm *date;
    date = localtime (now);

    year   = 1900 + date->tm_year;   
    month  = 1 + date->tm_mon;
    json timeTime = {year, month, date->tm_mday, date->tm_hour, date->tm_min, date->tm_sec,
		     year, month, date->tm_mday, date->tm_hour, date->tm_min, date->tm_sec};
    free (now);
    return timeTime;
}

long int PnRdatabase::get_number(string str) {
  long int val=0;
  for (int number=0; number < str.length(); number++) {
    if (isdigit (str[number]))
    val=(10*val)+(str[number]-48);
  }
  return val;
}

bool PnRdatabase::ReadDesignRule_metal(string metal_name, vector<string>& jason_file, int& index, string &def, PnRDB::metal_info& temp_metal_info){

  int *p=0;
  int p_temp=0;
  p=&p_temp;

  int times = 2;

  size_t found;
  bool new_drc_found = 0;
  vector<string> temp;
  temp = split_by_spaces_yg(def);
  if((found=def.find(metal_name))!=string::npos and (found=def.find("Layer"))!=string::npos) {
    vector<string> names = get_true_word(0,temp[1],0,',',p);
    string compare_name = "\""+metal_name+"\"";
    if(names[0]!=compare_name){
        return new_drc_found;
      }


    new_drc_found = 1;

    temp_metal_info.name = metal_name;

    index = index + 1;
    def = jason_file[index];
    //"LayerNo": 6,
    
    index = index + 1;
    def = jason_file[index];
    //"Type" : "Signal",

    index = index + 1;
    def = jason_file[index];
    //"Direction": "V",
    std::cout<<"check dir:  "<<def<<std::endl;
    if((found=def.find("Direction"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=def.find("H"))!=string::npos){
          temp_metal_info.direct = 1;
         }else{
          temp_metal_info.direct = 0;
         }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"Pitch": 80,
    if((found=def.find("Pitch"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       temp_metal_info.grid_unit_x = stoi(names[0])*times;
       temp_metal_info.grid_unit_y = temp_metal_info.grid_unit_x;

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"Width": 32,
    if((found=def.find("Width"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       temp_metal_info.width = stoi(names[0])*times;

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"MinL" : 180,
    if((found=def.find("MinL"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[2],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_metal_info.minL = -1;
         }else{
          temp_metal_info.minL = stoi(names[0])*times;
         }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"MaxL" : "NA",
    if((found=def.find("MaxL"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[2],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_metal_info.maxL = -1;
       }else{
          temp_metal_info.maxL = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"End-to-End": 48
    if((found=def.find("End-to-End"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names;
       names.push_back(temp[1]);

       if((found=names[0].find("NA"))!=string::npos){
          temp_metal_info.dist_ee = -1;
       }else{
          temp_metal_info.dist_ee = stoi(names[0])*times;
       }


      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    temp_metal_info.dist_ss = temp_metal_info.grid_unit_x - temp_metal_info.width;
      
      return new_drc_found;

    }else{
      return new_drc_found;
    }


}

bool PnRdatabase::ReadDesignRule_via(string via_name, vector<string>& jason_file, int &index, string &def, PnRDB::via_info& temp_via_info){

  int *p=0;
  int p_temp=0;
  p=&p_temp;

  int times = 2;

  size_t found;
  bool new_drc_found = 0;
  vector<string> temp;
  temp = split_by_spaces_yg(def);

  if((found=def.find(via_name))!=string::npos and (found=def.find("Layer"))!=string::npos) {
    vector<string> names = get_true_word(0,temp[1],0,',',p);
    string compare_name = "\""+via_name+"\"";
    if(names[0]!=compare_name){
        return new_drc_found;
      }


    new_drc_found = 1;

    temp_via_info.name = via_name;
    
    index = index + 1;
    def = jason_file[index];
    //"LayerNo": 11,

    index = index + 1;
    def = jason_file[index];
    //"Type" : "Via",

    index = index + 1;
    def = jason_file[index];

/*
    //"Stack": "M1-M2",
    if((found=def.find("Stack"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,'-',p);
       vector<string> name2 = get_true_word(0,names[1],0,',',p);

       temp_via_info.lower_metal_index = DRC_info.Metalmap[names[0]];
       
       temp_via_info.upper_metal_index = DRC_info.Metalmap[name2[0]];

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }
*/


    index = index + 1;
    def = jason_file[index];
    //"SpaceX": 76,
    if((found=def.find("SpaceX"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.dist_ss = -1;
       }else{
          temp_via_info.dist_ss = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"SpaceY": 76,
    if((found=def.find("SpaceY"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.dist_ss_y = -1;
       }else{
          temp_via_info.dist_ss_y = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"WidthX": 32,
    if((found=def.find("WidthX"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.width = -1;
       }else{
          temp_via_info.width = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"WidthY": 32,
    if((found=def.find("WidthY"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.width_y = -1;
       }else{
          temp_via_info.width_y = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"VencA_L" : 20,
    if((found=def.find("VencA_L"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.cover_l = -1;
       }else{
          temp_via_info.cover_l = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

    index = index + 1;
    def = jason_file[index];
    //"VencA_H" : 20,
    if((found=def.find("VencA_H"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.cover_u = -1;
       }else{
          temp_via_info.cover_u = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }


    index = index + 1;
    def = jason_file[index];
    //"VencP_L" : 20,
    if((found=def.find("VencP_L"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names = get_true_word(0,temp[1],0,',',p);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.cover_l_P = -1;
       }else{
          temp_via_info.cover_l_P = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }


    index = index + 1;
    def = jason_file[index];
    //"VencP_H" : 20
    if((found=def.find("VencP_H"))!=string::npos){
       temp=split_by_spaces_yg(def);
       vector<string> names;
       names.push_back(temp[1]);

       if((found=names[0].find("NA"))!=string::npos){
          temp_via_info.cover_u_P = -1;
       }else{
          temp_via_info.cover_u_P = stoi(names[0])*times;
       }

      }else{
        cout<<"Read Design Rule Error: Direction Error "<<endl;
      }

      return new_drc_found;

    }else{
      return new_drc_found;
    }



}

bool PnRdatabase::ReadPDKJSON(std::string drfile) {
    //std::cout<<"inside "<<drfile<<std::endl;
    //std::string jsonFileName = GDSData + ".json";
    int times=2;
    json jsonStrAry;
    ifstream jsonFile (drfile);
    if (jsonFile.is_open()) {
        //std::cout<<"before parse\n";
	json jedb = json::parse (jsonFile);
        //std::cout<<"Parse\n";
        json layerAry = jedb["Abstraction"];
        std::map<int, PnRDB::metal_info> metalSet;
        std::map<int, PnRDB::via_info> viaSet;
        // 1. Extract metal info
        //std::cout<<"shot\n";
        for(json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
          json layer = *lit;
          std::string lname=layer["Layer"];
          //std::cout<<"Now at "<<lname<<std::endl<<std::endl;
          if(lname.front()=='M') {
            // metal layer
            int lnum=layer["LayerNo"];
            std::string ldir=layer["Direction"];
            int lpitch=-1;
            json pdata=layer["Pitch"];
            if(pdata.is_array()) {
              json::iterator pit=pdata.begin();
              lpitch=(*pit);
            } else if (pdata.is_number()) {
              lpitch=pdata;
            }
            int lwidth=-1;
            json wdata=layer["Width"];
            if(wdata.is_array()) {
              json::iterator wit=wdata.begin();
              lwidth=(*wit);
            } else if (wdata.is_number()) {
              lwidth=wdata;
            }
            int lminL=layer["MinL"];
            //int lmaxL=layer["MaxL"];
            int le2e=layer["EndToEnd"];
            int loff=layer["Offset"];
            PnRDB::metal_info tmp_metal;
            tmp_metal.name=lname;
            tmp_metal.layerNo=lnum;
            if(ldir.compare("V")==0) { tmp_metal.direct=0; tmp_metal.grid_unit_x=times*lpitch; tmp_metal.grid_unit_y=-1;
            } else if (ldir.compare("H")==0) { tmp_metal.direct=1; tmp_metal.grid_unit_y=times*lpitch; tmp_metal.grid_unit_x=-1;
            } else {std::cout<<"PnR-Error: incorrect metal direction\n";}
            tmp_metal.width=times*lwidth;
            tmp_metal.dist_ss=times*(lpitch-lwidth);
            tmp_metal.minL=times*lminL;
            tmp_metal.dist_ee=times*le2e;
            metalSet.insert( std::pair<int, PnRDB::metal_info>(lnum, tmp_metal) );
            //std::cout<<tmp_metal.name<<std::endl;
            //std::cout<<tmp_metal.layerNo<<std::endl;
            //std::cout<<tmp_metal.direct<<std::endl;
            //std::cout<<tmp_metal.grid_unit_x<<std::endl;
            //std::cout<<tmp_metal.grid_unit_y<<std::endl;
            //std::cout<<tmp_metal.width<<std::endl;
            //std::cout<<tmp_metal.dist_ss<<std::endl;
            //std::cout<<tmp_metal.minL<<std::endl;
            //std::cout<<tmp_metal.dist_ee<<std::endl;
            //std::cout<<lname<<lnum<<ldir<<lpitch<<lwidth<<lminL<<le2e<<loff<<std::endl;
            }
        }
        for(std::map<int, PnRDB::metal_info>::iterator it=metalSet.begin(); it!=metalSet.end(); ++it) {
          DRC_info.Metal_info.push_back(it->second);
          DRC_info.Metalmap[it->second.name] = DRC_info.Metal_info.size()-1;
        }
        DRC_info.MaxLayer = DRC_info.Metal_info.size()-1;
        //std::cout<<"Parse via\n";
        // 2. Extract via info
        for(json::iterator lit = layerAry.begin(); lit != layerAry.end(); ++lit) {
          json layer = *lit;
          std::string lname=layer["Layer"];
          if(lname.front()=='V') {
            // via layer
            int lnum=layer["LayerNo"];
            json stackAry = layer["Stack"];
            int lwidthx= layer["WidthX"];
            int lwidthy= layer["WidthY"];
            int lspacex= layer["SpaceX"];
            int lspacey= layer["SpaceY"];
            int lvencal= layer["VencA_L"];
            int lvencah= layer["VencA_H"];
            int lvencpl= layer["VencP_L"];
            int lvencph= layer["VencP_H"];
            int lminno= layer["MinNo"];
            PnRDB::via_info tmp_via;
            tmp_via.name=lname;
            tmp_via.layerNo=lnum;
            tmp_via.width=times*lwidthx;
            tmp_via.width_y=times*lwidthy;
            tmp_via.cover_l=times*lvencal;
            tmp_via.cover_l_P=times*lvencpl;
            tmp_via.cover_u=times*lvencah;
            tmp_via.cover_u_P=times*lvencph;
            tmp_via.dist_ss=times*lspacex;
            tmp_via.dist_ss_y=times*lspacey;
            std::set<int> viaMSet; 
            std::set<int>::iterator vit;
            std::set<int>::reverse_iterator rvit;
            for(json::iterator sit=stackAry.begin(); sit!=stackAry.end(); ++sit) {
              if(sit->is_string()) {
                for(int k=0;k<(int)DRC_info.Metal_info.size();++k) {
                  if( DRC_info.Metal_info.at(k).name.compare(*sit)==0 ) {
                    viaMSet.insert(k);
                    break;
                  } 
                }
              }
            }
            vit=viaMSet.begin();
            tmp_via.lower_metal_index=(*vit);
            rvit=viaMSet.rbegin();
            tmp_via.upper_metal_index=(*rvit);
            viaSet.insert( std::pair<int, PnRDB::via_info>(lnum, tmp_via) );
            //std::cout<<tmp_via.name<<std::endl;
            //std::cout<<tmp_via.layerNo<<std::endl;
            //std::cout<<tmp_via.width<<std::endl;
            //std::cout<<tmp_via.width_y<<std::endl;
            //std::cout<<tmp_via.cover_l<<std::endl;
            //std::cout<<tmp_via.cover_l_P<<std::endl;
            //std::cout<<tmp_via.cover_u<<std::endl;
            //std::cout<<tmp_via.cover_u_P<<std::endl;
            //std::cout<<tmp_via.dist_ss<<std::endl;
            //std::cout<<tmp_via.dist_ss_y<<std::endl;
            //std::cout<<tmp_via.lower_metal_index<<std::endl;
            //std::cout<<tmp_via.upper_metal_index<<std::endl;
            //std::cout<<lname<<lnum<<lwidthx<<lwidthy<<lspacex<<lspacey<<lvencal<<lvencah<<lvencpl<<lvencph<<lminno<<std::endl;
          }
        }
        for(std::map<int, PnRDB::via_info>::iterator it=viaSet.begin(); it!=viaSet.end(); ++it) {
          DRC_info.Via_info.push_back(it->second);
          DRC_info.Viamap[it->second.name] = DRC_info.Via_info.size()-1;
        }

        // 3. Add metal weight
        //add
        for(int i=0;i<DRC_info.Metal_info.size();i++){
             DRC_info.metal_weight.push_back(1);
        }
        // 4. Add Via model
        for(int i=0;i<DRC_info.Via_info.size();i++){
             PnRDB::ViaModel temp_viamodel;
             temp_viamodel.name = DRC_info.Via_info[i].name;
             temp_viamodel.ViaIdx = i;
             temp_viamodel.LowerIdx = i;
             temp_viamodel.UpperIdx = i+1;
             PnRDB::point temp_point;
             //LL
             temp_point.x = 0-DRC_info.Via_info[i].width/2;
             temp_point.y = 0-DRC_info.Via_info[i].width_y/2;
             temp_viamodel.ViaRect.push_back(temp_point);
             //UR
             temp_point.x = 0+DRC_info.Via_info[i].width/2;
             temp_point.y = 0+DRC_info.Via_info[i].width_y/2;
             temp_viamodel.ViaRect.push_back(temp_point);
             
             //LL LowerRect
             if(DRC_info.Metal_info[i].direct==0){
             temp_point.x = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l_P;
             temp_point.y = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l;
             temp_viamodel.LowerRect.push_back(temp_point);
             //UR
             temp_point.x = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l_P;
             temp_point.y = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l;
             temp_viamodel.LowerRect.push_back(temp_point);
             }else{
             temp_point.y = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l_P;
             temp_point.x = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l;
             temp_viamodel.LowerRect.push_back(temp_point);
             //UR
             temp_point.y = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l_P;
             temp_point.x = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l;
             temp_viamodel.LowerRect.push_back(temp_point);
             } 
             
             //LL UpperRect
             if(DRC_info.Metal_info[i+1].direct==0){
             temp_point.x = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u_P;
             temp_point.y = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u;
             temp_viamodel.UpperRect.push_back(temp_point);
             //UR
             temp_point.x = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u_P;
             temp_point.y = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u;
             temp_viamodel.UpperRect.push_back(temp_point);
             }else{
             temp_point.y = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u_P;
             temp_point.x = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u;
             temp_viamodel.UpperRect.push_back(temp_point);
             //UR
             temp_point.y = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u_P;
             temp_point.x = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u;
             temp_viamodel.UpperRect.push_back(temp_point);
             } 
            DRC_info.Via_model.push_back(temp_viamodel);
        }
        // 6. Add mask ID
        //added by wbxu
        for(int i=0;i<(int)DRC_info.Metal_info.size();++i) {
          DRC_info.MaskID_Metal.push_back(std::to_string( DRC_info.Metal_info.at(i).layerNo ));
        }
        for(int i=0;i<(int)DRC_info.Via_info.size();++i) {
          DRC_info.MaskID_Via.push_back(std::to_string( DRC_info.Via_info.at(i).layerNo ));
        }
    }
}

bool PnRdatabase::ReadDesignRule_jason(string drfile){

  cout<<"PnRDB-Info: reading design rule jason file "<<drfile<<endl;

  ifstream fin;
  fin.open(drfile.c_str());
  string def;

  vector<string> temp;
  vector<string> temp2;

  PnRDB::metal_info temp_metal_info;
  PnRDB::via_info temp_via_info;
  string metal_name;
  string via_name;

  vector<string> jason_file;

  while(!fin.eof()){

    getline(fin, def);
    jason_file.push_back(def);
    
   }

  int end_size = jason_file.size();

  int index =0;

  while(index < end_size){

    def = jason_file[index];
    int found_metal_via = 0;

    metal_name = "M1";
    found_metal_via = ReadDesignRule_metal( metal_name, jason_file, index, def, temp_metal_info);
    if(found_metal_via == 1){
       DRC_info.Metal_info.push_back(temp_metal_info);
       DRC_info.Metalmap[metal_name] = DRC_info.Metal_info.size()-1;
       found_metal_via = 0;
      }

    metal_name = "M2";
    found_metal_via = ReadDesignRule_metal( metal_name, jason_file, index, def, temp_metal_info);
    if(found_metal_via == 1){
       DRC_info.Metal_info.push_back(temp_metal_info);
       DRC_info.Metalmap[metal_name] = DRC_info.Metal_info.size()-1;
       found_metal_via = 0;
      }

    metal_name = "M3";
    found_metal_via = ReadDesignRule_metal( metal_name, jason_file, index, def, temp_metal_info);
    if(found_metal_via == 1){
       DRC_info.Metal_info.push_back(temp_metal_info);
       DRC_info.Metalmap[metal_name] = DRC_info.Metal_info.size()-1;
       found_metal_via = 0;
      }

    metal_name = "M4";
    found_metal_via = ReadDesignRule_metal( metal_name, jason_file, index, def, temp_metal_info);
    if(found_metal_via == 1){
       DRC_info.Metal_info.push_back(temp_metal_info);
       DRC_info.Metalmap[metal_name] = DRC_info.Metal_info.size()-1;
       found_metal_via = 0;
      }

    metal_name = "M5";
    found_metal_via = ReadDesignRule_metal( metal_name, jason_file, index, def, temp_metal_info);
    if(found_metal_via == 1){
       DRC_info.Metal_info.push_back(temp_metal_info);
       DRC_info.Metalmap[metal_name] = DRC_info.Metal_info.size()-1;
       found_metal_via = 0;
      }

    metal_name = "M6";
    found_metal_via = ReadDesignRule_metal( metal_name, jason_file, index, def, temp_metal_info);
    if(found_metal_via == 1){
       DRC_info.Metal_info.push_back(temp_metal_info);
       DRC_info.Metalmap[metal_name] = DRC_info.Metal_info.size()-1;
       found_metal_via = 0;
      }

    metal_name = "M7";
    found_metal_via = ReadDesignRule_metal( metal_name, jason_file, index, def, temp_metal_info);
    if(found_metal_via == 1){
       DRC_info.Metal_info.push_back(temp_metal_info);
       DRC_info.Metalmap[metal_name] = DRC_info.Metal_info.size()-1;
       found_metal_via = 0;
      }

    via_name = "V1";
    found_metal_via = ReadDesignRule_via( via_name, jason_file, index, def, temp_via_info);
    if(found_metal_via == 1){
       DRC_info.Via_info.push_back(temp_via_info);
       DRC_info.Viamap[via_name] = DRC_info.Via_info.size()-1;
       found_metal_via = 0;
      }

    via_name = "V2";
    found_metal_via = ReadDesignRule_via( via_name, jason_file, index, def, temp_via_info);
    if(found_metal_via == 1){
       DRC_info.Via_info.push_back(temp_via_info);
       DRC_info.Viamap[via_name] = DRC_info.Via_info.size()-1;
       found_metal_via = 0;
      }

    via_name = "V3";
    found_metal_via = ReadDesignRule_via( via_name, jason_file, index, def, temp_via_info);
    if(found_metal_via == 1){
       DRC_info.Via_info.push_back(temp_via_info);
       DRC_info.Viamap[via_name] = DRC_info.Via_info.size()-1;
       found_metal_via = 0;
      }

    via_name = "V4";
    found_metal_via = ReadDesignRule_via( via_name, jason_file, index, def, temp_via_info);
    if(found_metal_via == 1){
       DRC_info.Via_info.push_back(temp_via_info);
       DRC_info.Viamap[via_name] = DRC_info.Via_info.size()-1;
       found_metal_via = 0;
      }

    via_name = "V5";
    found_metal_via = ReadDesignRule_via( via_name, jason_file, index, def, temp_via_info);
    if(found_metal_via == 1){
       DRC_info.Via_info.push_back(temp_via_info);
       DRC_info.Viamap[via_name] = DRC_info.Via_info.size()-1;
       found_metal_via = 0;
      }

    via_name = "V6";
    found_metal_via = ReadDesignRule_via( via_name, jason_file, index, def, temp_via_info);
    if(found_metal_via == 1){
       DRC_info.Via_info.push_back(temp_via_info);
       DRC_info.Viamap[via_name] = DRC_info.Via_info.size()-1;
       found_metal_via = 0;
      }

   index = index + 1;

   }

  fin.close();

  DRC_info.MaxLayer = DRC_info.Metal_info.size()-1;
  
  //add
  for(int i=0;i<DRC_info.Metal_info.size();i++){
       DRC_info.metal_weight.push_back(1);
     }
  
  for(int i=0;i<DRC_info.Via_info.size();i++){
       PnRDB::ViaModel temp_viamodel;
       temp_viamodel.name = DRC_info.Via_info[i].name;
       temp_viamodel.ViaIdx = i;
       temp_viamodel.LowerIdx = i;
       temp_viamodel.UpperIdx = i+1;
       PnRDB::point temp_point;
       //LL
       temp_point.x = 0-DRC_info.Via_info[i].width/2;
       temp_point.y = 0-DRC_info.Via_info[i].width_y/2;
       temp_viamodel.ViaRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Via_info[i].width/2;
       temp_point.y = 0+DRC_info.Via_info[i].width_y/2;
       temp_viamodel.ViaRect.push_back(temp_point);
       
       //LL LowerRect
       if(DRC_info.Metal_info[i].direct==0){
       temp_point.x = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l_P;
       temp_point.y = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l_P;
       temp_point.y = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       }else{
       temp_point.y = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l_P;
       temp_point.x = 0-DRC_info.Metal_info[i].width/2-DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       //UR
       temp_point.y = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l_P;
       temp_point.x = 0+DRC_info.Metal_info[i].width/2+DRC_info.Via_info[i].cover_l;
       temp_viamodel.LowerRect.push_back(temp_point);
       } 
       
       //LL UpperRect
       if(DRC_info.Metal_info[i+1].direct==0){
       temp_point.x = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u_P;
       temp_point.y = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       //UR
       temp_point.x = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u_P;
       temp_point.y = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       }else{
       temp_point.y = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u_P;
       temp_point.x = 0-DRC_info.Metal_info[i+1].width/2-DRC_info.Via_info[i].cover_u;
       temp_viamodel.UpperRect.push_back(temp_point);
       //UR
       temp_point.y = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u_P;
       temp_point.x = 0+DRC_info.Metal_info[i+1].width/2+DRC_info.Via_info[i].cover_u;
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

bool PnRdatabase::HardDesignRule() {
  PnRDB::metal_info tmp_metal;
  tmp_metal.name="M1";
  tmp_metal.width=18;
  tmp_metal.dist_ss=18;
  tmp_metal.direct=0;
  tmp_metal.grid_unit_x=128;
  tmp_metal.grid_unit_y=128;
  this->DRC_info.Metal_info.push_back(tmp_metal);
  tmp_metal.name="M2";
  tmp_metal.width=18;
  tmp_metal.dist_ss=18;
  tmp_metal.direct=1;
  tmp_metal.grid_unit_x=128;
  tmp_metal.grid_unit_y=128;
  this->DRC_info.Metal_info.push_back(tmp_metal);
  tmp_metal.name="M3";
  tmp_metal.width=18;
  tmp_metal.dist_ss=18;
  tmp_metal.direct=0;
  tmp_metal.grid_unit_x=128;
  tmp_metal.grid_unit_y=128;
  this->DRC_info.Metal_info.push_back(tmp_metal);
  tmp_metal.name="M4";
  tmp_metal.width=24;
  tmp_metal.dist_ss=24;
  tmp_metal.direct=1;
  tmp_metal.grid_unit_x=360;
  tmp_metal.grid_unit_y=192;
  this->DRC_info.Metal_info.push_back(tmp_metal);
  tmp_metal.name="M5";
  tmp_metal.width=24;
  tmp_metal.dist_ss=24;
  tmp_metal.direct=0;
  tmp_metal.grid_unit_x=192;
  tmp_metal.grid_unit_y=360;
  this->DRC_info.Metal_info.push_back(tmp_metal);
  tmp_metal.name="M6";
  tmp_metal.width=32;
  tmp_metal.dist_ss=32;
  tmp_metal.direct=1;
  tmp_metal.grid_unit_x=360;
  tmp_metal.grid_unit_y=256;
  this->DRC_info.Metal_info.push_back(tmp_metal);
  tmp_metal.name="M7";
  tmp_metal.width=32;
  tmp_metal.dist_ss=32;
  tmp_metal.direct=0;
  tmp_metal.grid_unit_x=256;
  tmp_metal.grid_unit_y=360;
  this->DRC_info.Metal_info.push_back(tmp_metal);

  PnRDB::via_info tmp_via;
  tmp_via.name="V1";
  tmp_via.lower_metal_index=0;
  tmp_via.upper_metal_index=1;
  tmp_via.width=18;
  tmp_via.cover_l=5;
  tmp_via.cover_u=5;
  tmp_via.dist_ss=30;
  this->DRC_info.Via_info.push_back(tmp_via);
  tmp_via.name="V2";
  tmp_via.lower_metal_index=1;
  tmp_via.upper_metal_index=2;
  tmp_via.width=18;
  tmp_via.cover_l=5;
  tmp_via.cover_u=5;
  tmp_via.dist_ss=30;
  this->DRC_info.Via_info.push_back(tmp_via);
  tmp_via.name="V3";
  tmp_via.lower_metal_index=2;
  tmp_via.upper_metal_index=3;
  tmp_via.width=18;
  tmp_via.cover_l=5;
  tmp_via.cover_u=11;
  tmp_via.dist_ss=30;
  this->DRC_info.Via_info.push_back(tmp_via);
  tmp_via.name="V4";
  tmp_via.lower_metal_index=3;
  tmp_via.upper_metal_index=4;
  tmp_via.width=24;
  tmp_via.cover_l=11;
  tmp_via.cover_u=11;
  tmp_via.dist_ss=33;
  this->DRC_info.Via_info.push_back(tmp_via);
  tmp_via.name="V5";
  tmp_via.lower_metal_index=4;
  tmp_via.upper_metal_index=5;
  tmp_via.width=24;
  tmp_via.cover_l=11;
  tmp_via.cover_u=11;
  tmp_via.dist_ss=33;
  this->DRC_info.Via_info.push_back(tmp_via);
  tmp_via.name="V6";
  tmp_via.lower_metal_index=5;
  tmp_via.upper_metal_index=6;
  tmp_via.width=32;
  tmp_via.cover_l=11;
  tmp_via.cover_u=11;
  tmp_via.dist_ss=45;
  this->DRC_info.Via_info.push_back(tmp_via);

  PnRDB::ViaModel tmp_vm; std::vector<PnRDB::point> tmp_pv; PnRDB::point tmp_p;
  tmp_vm.name="V1";
  tmp_vm.ViaIdx=0;
  tmp_vm.LowerIdx=0;
  tmp_vm.UpperIdx=1;
  tmp_pv.clear();
  tmp_p.x=-9; tmp_p.y=-9;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=9; tmp_p.y=9;
  tmp_pv.push_back(tmp_p);
  tmp_vm.ViaRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-9; tmp_p.y=-14;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=9; tmp_p.y=14;
  tmp_pv.push_back(tmp_p);
  tmp_vm.LowerRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-14; tmp_p.y=-9;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=14; tmp_p.y=9;
  tmp_pv.push_back(tmp_p);
  tmp_vm.UpperRect=tmp_pv;
  this->DRC_info.Via_model.push_back(tmp_vm);
  tmp_vm.name="V2";
  tmp_vm.ViaIdx=1;
  tmp_vm.LowerIdx=1;
  tmp_vm.UpperIdx=2;
  tmp_pv.clear();
  tmp_p.x=-9; tmp_p.y=-9;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=9; tmp_p.y=9;
  tmp_pv.push_back(tmp_p);
  tmp_vm.ViaRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-14; tmp_p.y=-9;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=14; tmp_p.y=9;
  tmp_pv.push_back(tmp_p);
  tmp_vm.LowerRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-9; tmp_p.y=-14;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=9; tmp_p.y=14;
  tmp_pv.push_back(tmp_p);
  tmp_vm.UpperRect=tmp_pv;
  this->DRC_info.Via_model.push_back(tmp_vm);
  tmp_vm.name="V3";
  tmp_vm.ViaIdx=2;
  tmp_vm.LowerIdx=2;
  tmp_vm.UpperIdx=3;
  tmp_pv.clear();
  tmp_p.x=-9; tmp_p.y=-9;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=9; tmp_p.y=9;
  tmp_pv.push_back(tmp_p);
  tmp_vm.ViaRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-9; tmp_p.y=-14;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=9; tmp_p.y=14;
  tmp_pv.push_back(tmp_p);
  tmp_vm.LowerRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-23; tmp_p.y=-12;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=23; tmp_p.y=12;
  tmp_pv.push_back(tmp_p);
  tmp_vm.UpperRect=tmp_pv;
  this->DRC_info.Via_model.push_back(tmp_vm);
  tmp_vm.name="V4";
  tmp_vm.ViaIdx=3;
  tmp_vm.LowerIdx=3;
  tmp_vm.UpperIdx=4;
  tmp_pv.clear();
  tmp_p.x=-12; tmp_p.y=-12;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=12; tmp_p.y=12;
  tmp_pv.push_back(tmp_p);
  tmp_vm.ViaRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-23; tmp_p.y=-12;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=23; tmp_p.y=12;
  tmp_pv.push_back(tmp_p);
  tmp_vm.LowerRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-12; tmp_p.y=-23;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=12; tmp_p.y=23;
  tmp_pv.push_back(tmp_p);
  tmp_vm.UpperRect=tmp_pv;
  this->DRC_info.Via_model.push_back(tmp_vm);
  tmp_vm.name="V5";
  tmp_vm.ViaIdx=4;
  tmp_vm.LowerIdx=4;
  tmp_vm.UpperIdx=5;
  tmp_pv.clear();
  tmp_p.x=-12; tmp_p.y=-12;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=12; tmp_p.y=12;
  tmp_pv.push_back(tmp_p);
  tmp_vm.ViaRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-12; tmp_p.y=-23;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=12; tmp_p.y=23;
  tmp_pv.push_back(tmp_p);
  tmp_vm.LowerRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-27; tmp_p.y=-16;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=27; tmp_p.y=16;
  tmp_pv.push_back(tmp_p);
  tmp_vm.UpperRect=tmp_pv;
  this->DRC_info.Via_model.push_back(tmp_vm);
  tmp_vm.name="V6";
  tmp_vm.ViaIdx=5;
  tmp_vm.LowerIdx=5;
  tmp_vm.UpperIdx=6;
  tmp_pv.clear();
  tmp_p.x=-16; tmp_p.y=-16;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=16; tmp_p.y=16;
  tmp_pv.push_back(tmp_p);
  tmp_vm.ViaRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-27; tmp_p.y=-16;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=27; tmp_p.y=16;
  tmp_pv.push_back(tmp_p);
  tmp_vm.LowerRect=tmp_pv;
  tmp_pv.clear();
  tmp_p.x=-16; tmp_p.y=-27;
  tmp_pv.push_back(tmp_p);
  tmp_p.x=16; tmp_p.y=27;
  tmp_pv.push_back(tmp_p);
  tmp_vm.UpperRect=tmp_pv;
  this->DRC_info.Via_model.push_back(tmp_vm);

  this->DRC_info.Metalmap["M1"]=0;
  this->DRC_info.Metalmap["M2"]=1;
  this->DRC_info.Metalmap["M3"]=2;
  this->DRC_info.Metalmap["M4"]=3;
  this->DRC_info.Metalmap["M5"]=4;
  this->DRC_info.Metalmap["M6"]=5;
  this->DRC_info.Metalmap["M7"]=6;

  this->DRC_info.Viamap["V1"]=0;
  this->DRC_info.Viamap["V2"]=1;
  this->DRC_info.Viamap["V3"]=2;
  this->DRC_info.Viamap["V4"]=3;
  this->DRC_info.Viamap["V5"]=4;
  this->DRC_info.Viamap["V6"]=5;

  this->DRC_info.metal_weight.resize(7,1);

  this->DRC_info.MaskID_Metal.push_back("19");
  this->DRC_info.MaskID_Metal.push_back("20");
  this->DRC_info.MaskID_Metal.push_back("30");
  this->DRC_info.MaskID_Metal.push_back("40");
  this->DRC_info.MaskID_Metal.push_back("50");
  this->DRC_info.MaskID_Metal.push_back("60");
  this->DRC_info.MaskID_Metal.push_back("70");
  this->DRC_info.MaskID_Via.push_back("21");
  this->DRC_info.MaskID_Via.push_back("25");
  this->DRC_info.MaskID_Via.push_back("35");
  this->DRC_info.MaskID_Via.push_back("45");
  this->DRC_info.MaskID_Via.push_back("55");
  this->DRC_info.MaskID_Via.push_back("65");
  this->DRC_info.MaskID_Via.push_back("75");
}

bool PnRdatabase::ReadDesignRule(string drfile) {
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
        for(int q=1;q<temp.size();q++){
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
          for(int q=0;q<temp.size();q++){
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
          for(int q=0;q<temp.size();q++){
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
          for(int q=0;q<temp.size();q++){
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
      for(int i = 0;i<dis.size();i++){
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
      for(int i = 0;i<dis.size();i++){
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
      for(int i = 0;i<dis.size();i++){
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
      for(int i = 0;i<dis.size();i++){
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
      for(int i = 0;i<dis.size();i++){
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
      for(int i = 0;i<dis.size();i++){
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
      for(int i = 0;i<dis.size();i++){
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
  for(int i=0;i<DRC_info.Metal_info.size();i++){
       DRC_info.metal_weight.push_back(1);
     }
  
  for(int i=0;i<DRC_info.Via_info.size();i++){
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

PnRdatabase::PnRdatabase(string path, string topcell, string vname, string lefname, string mapname, string drname) {
  unitScale=2000;
  maxNode=0;
  cout<<"PnRDB-Info: reading data from path "<<path<<endl;
  #ifndef HFLAG
  std::cout<<"PnRDB-Info: default PDK"<<std::endl;
  this->HardDesignRule();
  #endif
  #ifdef HFLAG
  size_t found;
  if((found=drname.find(".rul"))!=string::npos){
    this->ReadDesignRule(path+"/"+drname);
  }else{
    this->ReadPDKJSON(path+"/"+drname);
    //this->ReadDesignRule_jason(path+"/"+drname);
  }
  std::cout<<"PnRDB-Info: read PDK via "<<drname<<std::endl;
  #endif

  this->ReadLEF(path+"/"+lefname);
  this->ReadMap(path, mapname);
  //cout<<"Before reading verilog"<<endl;
  //PrintLEFData();
  this->ReadVerilog(path, vname, topcell);

  cout<<"PnRDB-Info: complete reading"<<endl;
  //cout<<"After reading verilog"<<endl;
  //PrintLEFData();
}

queue<int> PnRdatabase::TraverseHierTree() {
  queue<int> Q;
  vector<string> color(hierTree.size(), "white");
  TraverseDFS(Q, color, topidx);
  return Q;
}

void PnRdatabase::TraverseDFS(queue<int>& Q, vector<string>& color, int idx) {
  color[idx]="gray";
  for(vector<PnRDB::blockComplex>::iterator it=hierTree.at(idx).Blocks.begin();it!=hierTree.at(idx).Blocks.end();++it) {
    if( it->child!=-1 && color[it->child].compare("white")==0 ) {
      TraverseDFS(Q, color, it->child);
    }
  }
  color[idx]="black";
  Q.push(idx);
}

PnRDB::hierNode PnRdatabase::CheckoutHierNode(int nodeID) {
  //cout<<hierTree.size()<<endl;
  return hierTree[nodeID];
}

bool PnRdatabase::ReadMap(string fpath, string mapname) {
  cout<<"PnRDB-Info: reading map file "<<fpath+"/"+mapname<<endl;
  ifstream fin;
  string def;
  string mapfile=fpath+"/"+mapname;
  vector<string> temp;
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(mapfile.c_str());
    while(fin.peek()!=EOF) {
      getline(fin, def);
      if(def.compare("")==0) {continue;}
      temp = split_by_spaces_yg(def);
      if(temp.size()>=2) {
        gdsData.insert( std::pair<string,string>(temp[0],fpath+"/"+temp[1]) );
      }
    }
    fin.close();
    return true;
  } catch(ifstream::failure e) {
    cerr<<"PnRDB-Error: fail to read map file "<<endl;
  }
  return false;
}

void PnRdatabase::PrintHierTree() {
}

void PnRdatabase::PrintLEFData() {
  cout<<"PnRDB-Info: PrintLEFData"<<endl;
  for(map<string, std::vector<PnRDB::lefMacro> >::iterator it=lefData.begin();it!=lefData.end();++it) {
    cout<<"\nMacro: "<<it->first<<endl;
    for(int w=0;w<(int)it->second.size();++w) {
    std::cout<<"Choice "<<w<<std::endl;
    cout<<"Content: name "<<(it->second).at(w).name<<"; width "<<(it->second).at(w).width<<"; height "<<(it->second).at(w).height<<endl;
    cout<<"Macro pins"<<endl;
    for(vector<PnRDB::pin>::iterator it2=it->second.at(w).macroPins.begin();it2!=it->second.at(w).macroPins.end();++it2) {
      cout<<"\tpin name: "<<it2->name<<"; type: "<<it2->type;
      for(vector<PnRDB::contact>::iterator it4=it2->pinContacts.begin(); it4!= it2->pinContacts.end();it4++) {
        cout<<"\n\tmetal: "<<it4->metal<<"; orginBox: ";
        for(vector<PnRDB::point>::iterator it3=it4->originBox.polygon.begin();it3!=it4->originBox.polygon.end();it3++) {
          cout<<" {"<<it3->x<<","<<it3->y<<"}";
        }
        cout<<" LL-{"<<it4->originBox.LL.x<<","<<it4->originBox.LL.y<<"}";
        cout<<" LR-{"<<it4->originBox.LR.x<<","<<it4->originBox.LR.y<<"}";
        cout<<" UL-{"<<it4->originBox.UL.x<<","<<it4->originBox.UL.y<<"}";
        cout<<" UR-{"<<it4->originBox.UR.x<<","<<it4->originBox.UR.y<<"}";
        cout<<" center-{"<<it4->originCenter.x<<","<<it4->originCenter.y<<"}";
      }
      cout<<endl;
    }
    cout<<"Internal metals"<<endl;
    for(vector<PnRDB::contact>::iterator it4=it->second.at(w).interMetals.begin(); it4!= it->second.at(w).interMetals.end();it4++) {
      cout<<"\tmetal: "<<it4->metal<<"; orginBox: ";
      for(vector<PnRDB::point>::iterator it3=it4->originBox.polygon.begin();it3!=it4->originBox.polygon.end();it3++) {
        cout<<" {"<<it3->x<<","<<it3->y<<"}";
      }
      cout<<" LL-{"<<it4->originBox.LL.x<<","<<it4->originBox.LL.y<<"}";
      cout<<" LR-{"<<it4->originBox.LR.x<<","<<it4->originBox.LR.y<<"}";
      cout<<" UL-{"<<it4->originBox.UL.x<<","<<it4->originBox.UL.y<<"}";
      cout<<" UR-{"<<it4->originBox.UR.x<<","<<it4->originBox.UR.y<<"}";
      cout<<" center-{"<<it4->originCenter.x<<","<<it4->originCenter.y<<"}";
      cout<<endl;
    }
    }
  }
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
  int width, height;
  vector<PnRDB::pin> macroPins;
  vector<PnRDB::contact> interMetals;
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(leffile.c_str());
    int stage=0;
    while(fin.peek()!=EOF) {
      getline(fin, def);
      //cout<<def<<endl;
      // [wbxu] This function needs to be updated to support internal metals, currently we're lack of data
      if(stage==0) { // idle mode
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
          width=int(stod(temp[1])*unitScale);
          height=int(stod(temp[3])*unitScale);
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
        if((found=def.find("LAYER"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          if(temp[1].front()!='M') {continue;} // work around for obs on Via layer - wbxu 20190707
          interMetals.resize(interMetals.size()+1);
          interMetals.back().metal=temp[1];
        } else if((found=def.find("RECT"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          int LLx=int(stod(temp[1])*unitScale);
          int LLy=int(stod(temp[2])*unitScale);
          int URx=int(stod(temp[3])*unitScale);
          int URy=int(stod(temp[4])*unitScale);
          PnRDB::bbox oBox; PnRDB::point tp;
          tp.x=LLx; tp.y=LLy;
          oBox.LL=tp;
          oBox.polygon.push_back(tp);
          tp.x=LLx; tp.y=URy;
          oBox.UL=tp;
          oBox.polygon.push_back(tp);
          tp.x=URx; tp.y=URy;
          oBox.UR=tp;
          oBox.polygon.push_back(tp);
          tp.x=URx; tp.y=LLy;
          oBox.LR=tp;
          oBox.polygon.push_back(tp);
          interMetals.back().originBox=oBox;
          interMetals.back().originCenter.x=(LLx+URx)/2;
          interMetals.back().originCenter.y=(LLy+URy)/2;
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
          temp=get_true_word(found,def,0,';',p);
          macroPins.back().pinContacts.resize( macroPins.back().pinContacts.size()+1 );
          macroPins.back().pinContacts.back().metal=temp[1];
          //cout<<"Stage "<<stage<<" @ contact layer "<<macroPins.back().pinContacts.back().metal<<endl;
        } else if((found=def.find("RECT"))!=string::npos) {
          temp=get_true_word(found,def,0,';',p);
          int LLx=int(stod(temp[1])*unitScale);
          int LLy=int(stod(temp[2])*unitScale);
          int URx=int(stod(temp[3])*unitScale);
          int URy=int(stod(temp[4])*unitScale);
          PnRDB::bbox oBox; PnRDB::point tp;
          tp.x=LLx; tp.y=LLy;
          oBox.LL=tp;
          oBox.polygon.push_back(tp);
          tp.x=LLx; tp.y=URy;
          oBox.UL=tp;
          oBox.polygon.push_back(tp);
          tp.x=URx; tp.y=URy;
          oBox.UR=tp;
          oBox.polygon.push_back(tp);
          tp.x=URx; tp.y=LLy;
          oBox.LR=tp;
          oBox.polygon.push_back(tp);
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
          stage=2;
        }
      }
    }
    fin.close();
    return true;
  } catch(ifstream::failure e) {
    cerr<<"PnRDB-Error: fail to read LEF file "<<endl;
  }
  return false;
}

bool PnRdatabase::ReadConstraint(PnRDB::hierNode& node, string fpath, string suffix) {
  ifstream fin;
  string def;
  vector<string> temp, tempsec;
  size_t found;
  int *p;
  int p_temp=0;
  p=&p_temp;
  string cfile=fpath+"/"+node.name+"."+suffix;
  std::cout<<"start to read const file "<<cfile<<std::endl;
  // constraint format issues(comma): Alignment, Preplace, MatchBlock, Abutment
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(cfile.c_str());
    while(fin.peek()!=EOF) {
      getline(fin, def);
      //std::cout<<"line "<<def<<std::endl;
      if(def.compare("")==0) {continue;}
      temp=split_by_spaces(def);
      //for(int i=0;i<temp.size();i++) {cout<<" ? "<<temp[i];}
      //cout<<endl;
      if(temp[0].compare("SymmNet")==0) {
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        //cout<<word<<endl;
        tempsec=StringSplitbyChar(word, ',');
        //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
        PnRDB::net tmpnet;
        for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
          if(it==tempsec.begin()) {
            tmpnet.name=*it;
          } else {
            if(it->find("/")!=string::npos) { // if block pin
              vector<string> tempthd=StringSplitbyChar(*it, '/');
              for(int i=0;i<(int)node.Blocks.size();i++) {
                if(node.Blocks.at(i).instance.back().name.compare(tempthd[0])==0) {
                  for(int j=0;j<(int)node.Blocks.at(i).instance.back().blockPins.size();j++) {
                    if(node.Blocks.at(i).instance.back().blockPins.at(j).name.compare(tempthd[1])==0) {
                      //cout<<j<<" "<<i<<endl;
                      PnRDB::connectNode newnode={PnRDB::Block, j, i};
                      tmpnet.connected.push_back(newnode);
                      break;
                    }
                  }
                  break;
                }
              }
              //cout<<*it<<" is pin"<<tempthd[0]<<"/"<<tempthd[1]<<endl;
            } else { // if terminal
              for(int i=0;i<(int)node.Terminals.size();i++) {
                if(node.Terminals.at(i).name.compare(*it)==0) {
                  PnRDB::connectNode newnode={PnRDB::Terminal, i, -1};
                  tmpnet.connected.push_back(newnode);
                  break;
                }
              }
              //cout<<*it<<" is terminal"<<endl;
            }
          }
        }
        word=temp[4];
        //cout<<word<<endl;
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        tempsec=StringSplitbyChar(word, ',');
        //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
        PnRDB::net tmpnet2;
        for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
          if(it==tempsec.begin()) {
            tmpnet2.name=*it;
          } else {
            if(it->find("/")!=string::npos) { // if block pin
              vector<string> tempthd=StringSplitbyChar(*it, '/');
              for(int i=0;i<(int)node.Blocks.size();i++) {
                //std::cout<<"block "<<node.Blocks.at(i).instance.back().name<<std::endl;
                if(node.Blocks.at(i).instance.back().name.compare(tempthd[0])==0) {
                  for(int j=0;j<(int)node.Blocks.at(i).instance.back().blockPins.size();j++) {
                    //std::cout<<"\t pin "<<node.Blocks.at(i).instance.back().blockPins.at(j).name<<std::endl;
                    if(node.Blocks.at(i).instance.back().blockPins.at(j).name.compare(tempthd[1])==0) {
                      //cout<<j<<" "<<i<<endl;
                      PnRDB::connectNode newnode={PnRDB::Block, j, i};
                      tmpnet2.connected.push_back(newnode);
                      break;
                    }
                  }
                  break;
                }
              }
              //cout<<*it<<" is pin"<<tempthd[0]<<"/"<<tempthd[1]<<endl;
            } else { // if terminal
              for(int i=0;i<(int)node.Terminals.size();i++) {
                if(node.Terminals.at(i).name.compare(*it)==0) {
                  PnRDB::connectNode newnode={PnRDB::Terminal, i, -1};
                  tmpnet2.connected.push_back(newnode);
                  break;
                }
              }
              //cout<<*it<<" is terminal"<<endl;
            }
          }
        }
        int iter1=-1, iter2=-1; // iterator in Nets
        for(int i=0;i<(int)node.Nets.size()&&(iter1==-1||iter2==-1);i++) {
          if(node.Nets.at(i).name.compare(tmpnet.name)==0) {iter1=i;}
          if(node.Nets.at(i).name.compare(tmpnet2.name)==0) {iter2=i;}
        }
        node.Nets.at(iter1).symCounterpart=iter2;
        node.Nets.at(iter1).iter2SNetLsit=node.SNets.size();
        node.Nets.at(iter2).symCounterpart=iter1;
        node.Nets.at(iter2).iter2SNetLsit=node.SNets.size();
        node.SNets.resize(node.SNets.size()+1);
        node.SNets.back().net1=tmpnet;
        node.SNets.back().net2=tmpnet2;
        node.SNets.back().iter1=iter1;
        node.SNets.back().iter2=iter2;
      } else if (temp[0].compare("CritNet")==0) {
        for(int i=0;i<(int)node.Nets.size();i++) {
          if(node.Nets.at(i).name.compare(temp[2])==0) {
            node.Nets.at(i).priority=temp[4];
            break;
          }
        }
      } else if(temp[0].compare("Preplace")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
        PnRDB::Preplace preplace_const;
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            preplace_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            preplace_const.blockid2 = i;
            break;
          } else {
            preplace_const.conner = block_second;
          }
        }
        preplace_const.distance = distance;
        preplace_const.horizon = horizon;
        node.Preplace_blocks.push_back(preplace_const);
      } else if(temp[0].compare("Alignment")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
        PnRDB::Alignment alignment_const;
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            alignment_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            alignment_const.blockid2 = i;
            break;
          }
        }
        alignment_const.distance = distance;
        alignment_const.horizon = horizon;
        node.Alignment_blocks.push_back(alignment_const);
      } else if(temp[0].compare("Abument")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
      
        PnRDB::Abument abument_const;
      
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            abument_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            abument_const.blockid2 = i;
            break;
          }
        }
        abument_const.distance = distance;
        abument_const.horizon = horizon;
        node.Abument_blocks.push_back(abument_const);
      } else if(temp[0].compare("MatchBlock")==0){
        string block_first=temp[2];
        string block_second=temp[4];
        //int distance= atoi(temp[4].c_str());
        //int horizon = atoi(temp[5].c_str());
      
        PnRDB::MatchBlock match_const;
      
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            match_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            match_const.blockid2 = i;
            break;
          }
        }
        //match_const.distance = distance;
        //match_const.horizon = horizon;
        node.Match_blocks.push_back(match_const);
      } else if(temp[0].compare("bias_graph")==0){
        int distance= atoi(temp[2].c_str());
        node.bias_Hgraph = distance;
        node.bias_Vgraph = distance;
      } else if(temp[0].compare("bias_Hgraph")==0 ) {
        int distance= atoi(temp[2].c_str());
        node.bias_Hgraph = distance;
      } else if(temp[0].compare("bias_Vgraph")==0 ) {
        int distance= atoi(temp[2].c_str());
        node.bias_Vgraph = distance;
      } else if (temp[0].compare("ShieldNet")==0) {
        string shield_net=temp[2];
        for(int i=0;i<(int)node.Nets.size();i++) {
          if(node.Nets.at(i).name.compare(shield_net)==0) {
            node.Nets.at(i).shielding=true; break;
          }
        }
      } else if (temp[0].compare("SymmBlock")==0) { 
        PnRDB::SymmPairBlock temp_SymmPairBlock;
        pair<int,int> temp_pair;
        pair<int,PnRDB::Smark> temp_selfsym;
        for(int i=2;i<temp.size();i=i+2){
          string word=temp[i];
          word=word.substr(1);
          word=word.substr(0, word.length()-1);
          tempsec=StringSplitbyChar(word, ',');
          if((found=temp[i].find(","))!=string::npos) { // sympair
            for(int k=0;k<(int)node.Blocks.size();k++) {
              if(node.Blocks.at(k).instance.back().name.compare(tempsec[0])==0) {temp_pair.first = k;}
              if(node.Blocks.at(k).instance.back().name.compare(tempsec[1])==0) {temp_pair.second = k;}
            }
            int temp_int;
            if(temp_pair.first>temp_pair.second){
              temp_int = temp_pair.second;
              temp_pair.second = temp_pair.first;
              temp_pair.first = temp_int;
            } else if (temp_pair.first==temp_pair.second) {
              std::cerr<<"PnRDB-Error: same block in paired symmetry group"<<std::endl;
            }
            temp_SymmPairBlock.sympair.push_back(temp_pair);
          } else { // selfsym
            for(int j=0;j<(int)node.Blocks.size();j++) {
              if(node.Blocks.at(j).instance.back().name.compare(word)==0) {
                temp_selfsym.first =  j;
                temp_selfsym.second = PnRDB::H;
                temp_SymmPairBlock.selfsym.push_back(temp_selfsym);
                break;
              }
            }
          }
        }
        node.SPBlocks.push_back(temp_SymmPairBlock);
      }else if(temp[0].compare("CC")==0){
        PnRDB::CCCap temp_cccap;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_cccap.CCCap_name = word;
        word = temp[6];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_cccap.Unit_capacitor = word;
        word=temp[4];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        //cout<<word<<endl;
        tempsec=StringSplitbyChar(word, ',');
        for(int p=0;p<tempsec.size();p++){ 
            temp_cccap.size.push_back(atoi(tempsec[p].c_str()));
           }
        if(temp.size()>9){
          temp_cccap.cap_ratio = 1;
          word=temp[8];
          word=word.substr(1);
          word=word.substr(0, word.length()-1);
          //cout<<word<<endl;
          tempsec=StringSplitbyChar(word, ',');
          temp_cccap.cap_r = atoi(tempsec[0].c_str());
          temp_cccap.cap_s = atoi(tempsec[1].c_str());
          }
        //temp_cccap.size = temp[4]; //size?
        
        node.CC_Caps.push_back(temp_cccap);
      } else if (temp[0].compare("AlignBlock")==0) {
        PnRDB::AlignBlock alignment_unit;
        if(temp[2].compare("H")==0) {
          alignment_unit.horizon=1;
        } else {
          alignment_unit.horizon=0;
        }
        for(int j=4;j<(int)temp.size();j+=2) {
          for(int i=0;i<(int)node.Blocks.size();i++) {
            if(node.Blocks.at(i).instance.back().name.compare(temp[j])==0) {
              alignment_unit.blocks.push_back(i);
              break;
            }
          }
        }
        //std::cout<<"AlignBlock "<<alignment_unit.horizon<<" @ ";
        for(int i=0;i<alignment_unit.blocks.size();i++) {std::cout<<alignment_unit.blocks[i]<<" ";}
        //std::cout<<std::endl;
        node.Align_blocks.push_back(alignment_unit);
      } else if (temp[0].compare("PortLocation")==0) {
        // PortLocation(X,L) 
        // This constraint indicates the location of the port ‘X’
        // Considering the block as a rectangle, the edges can be divided into 12 sections as shown in the figure below.
        //  L indicates the approximate position of the port. Value of L should be taken from the set
        // {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT, }
        PnRDB::PortPos tmp_portpos;
        //std::cout<<temp[4]<<temp[2]<<std::endl;
        if(temp[4].compare("TL")==0) {
          tmp_portpos.pos=PnRDB::TL;
          //std::cout<<"TL\n";
        } else if(temp[4].compare("TC")==0) {
	  //std::cout<<"TC\n";
          tmp_portpos.pos=PnRDB::TC;
        } else if(temp[4].compare("TR")==0) {
          //std::cout<<"TR\n";
          tmp_portpos.pos=PnRDB::TR;
        } else if(temp[4].compare("RT")==0) {
          //std::cout<<"RT\n";
          tmp_portpos.pos=PnRDB::RT;
        } else if(temp[4].compare("RC")==0) {
          //std::cout<<"RC\n";
          tmp_portpos.pos=PnRDB::RC;
        } else if(temp[4].compare("RB")==0) {
          //std::cout<<"RB\n";
          tmp_portpos.pos=PnRDB::RB;
        } else if(temp[4].compare("BL")==0) {
          //std::cout<<"BL\n";
          tmp_portpos.pos=PnRDB::BL;
        } else if(temp[4].compare("BC")==0) {
          //std::cout<<"BC\n";
          tmp_portpos.pos=PnRDB::BC;
        } else if(temp[4].compare("BR")==0) {
          //std::cout<<"BR\n";
          tmp_portpos.pos=PnRDB::BR;
        } else if(temp[4].compare("LB")==0) {
          //std::cout<<"LB\n";
          tmp_portpos.pos=PnRDB::LB;
        } else if(temp[4].compare("LC")==0) {
          //std::cout<<"LC\n";
          tmp_portpos.pos=PnRDB::LC;
        } else if(temp[4].compare("LT")==0) {
          //std::cout<<"LT\n";
          tmp_portpos.pos=PnRDB::LT;
        }
        string name=temp[2];
        for(int k=0;k<(int)node.Terminals.size();++k) {
          //std::cout<<name<<" vs "<<node.Terminals.at(k).name<<std::endl;
          if(node.Terminals.at(k).name.compare(name)==0) {
            tmp_portpos.tid=k;
            break;
          }
        }
        std:cout<<"PortLocation "<<tmp_portpos.tid<<" @ "<<tmp_portpos.pos<<std::endl;
        node.Port_Location.push_back(tmp_portpos);
      }
    }
    fin.close();
    //std::cout<<"end read const file "<<cfile<<std::endl;
    return true;
  } catch(ifstream::failure e) {
    cerr<<"PnRDB-Error: fail to read constraint file "<<endl;
  }
  return false;
}


// for Yauang's development
bool PnRdatabase::ReadVerilog(string fpath, string vname, string topcell) {
  string verilogfile=fpath+"/"+vname;
  cout<<"PnRDB-Info: reading Verilog file "<<verilogfile<<endl;
  ifstream fin;
  string verilog_string;
  size_t found;
  vector<string> temp;
  PnRDB::blockComplex temp_blockComplex,clear_blockComplex;
  temp_blockComplex.instance.resize(1);
  clear_blockComplex.instance.resize(1);
  PnRDB::net temp_net,clear_net;
  PnRDB::PowerNet temp_PowerNet, clear_PowerNet;
  PnRDB::terminal temp_terminal,clear_terminal;
  string temp_name;
  PnRDB::pin temp_pin;
  PnRDB::connectNode temp_connectNode;
  PnRDB::hierNode temp_node,clear_node;
  PnRDB::hierNode Supply_node;
  int *p;
  int p_temp=0;
  p=&p_temp;
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    int in_module = 0;
    int lock = 0;
    int specify = 0;
    fin.open(verilogfile.c_str());
    while(fin.peek()!=EOF) {
        getline(fin, verilog_string);
        // If strange modules, then lock reading
        if((found=verilog_string.find("`endcelldefine"))!=string::npos){
           lock = 0;
           continue;
           }
           else{   
               if((found=verilog_string.find("`celldefine"))!=string::npos){
                  lock = 1;
                  continue;
                  }
                  else{
                       if((found=verilog_string.find("//"))!=string::npos){
                           continue;
                           }
                            else{
                                if((found=verilog_string.find("endspecify"))!=string::npos){
                                   specify = 0;
                                   continue;
                                   }
                                   else{
                                       if((found=verilog_string.find("specify"))!=string::npos){
                                           specify = 1;
                                           continue;
                                           }
                                           else{
                                               if(verilog_string.compare("")==0){
                                                 continue;
                                                 }
                                               }
                                       }	
                               }
                      }
               }


///////////////////modefy this part
	if(lock == 1){//find power key word
          if((found=verilog_string.find("endmodule"))!=string::npos){
             in_module = 0;
             //added one nodes to the class
             continue;
             }
             else{
                 if((found=verilog_string.find("module"))!=string::npos){
                    in_module = 1;
                    //read node name, and terminal names
                    temp = split_by_spaces_yg(verilog_string);
                    vector<string> names = get_true_word(0,temp[1],0,';',p);
                    Supply_node.name = names[0];
                    Supply_node.isCompleted = 0;
                    continue;
                    }
                 }
          }
///////////////modify this part

        // judge whether verilog_string is in a certain module node
        if(lock ==0){
          if((found=verilog_string.find("endmodule"))!=string::npos){
             in_module = 0;
             if(DRC_info.Metal_info.size()<=1) {std::cout<<"PnRDB-Error: too less metal layers\n";}
             if(DRC_info.Metal_info[0].direct==1) { //horizontal
               temp_node.bias_Vgraph=DRC_info.Metal_info[0].grid_unit_y;
             } else {
               temp_node.bias_Hgraph=DRC_info.Metal_info[0].grid_unit_x;
             }
             if(DRC_info.Metal_info[1].direct==1) { //horizontal
               temp_node.bias_Vgraph=DRC_info.Metal_info[1].grid_unit_y;
             } else {
               temp_node.bias_Hgraph=DRC_info.Metal_info[1].grid_unit_x;
             }
             //added one nodes to the class
             if(!ReadConstraint(temp_node, fpath, "const")) {cerr<<"PnRDB-Error: fail to read constraint file of module "<<temp_node.name<<endl;}
             else{std::cout<<"Finished reading contraint file"<<std::endl;}
             
             hierTree.push_back(temp_node);
             temp_node = clear_node;
             continue;
             }
             else{
                 if((found=verilog_string.find("module"))!=string::npos){
                    in_module = 1;
                    //read node name, and terminal names
                    temp = split_by_spaces_yg(verilog_string);
                    temp_node.name = temp[1];
                    temp_node.isCompleted = 0;
                    for(int i=3;i<temp.size()-1;i++){
                        vector<string> names = get_true_word(0,temp[i],0,',',p);
                        temp_terminal.name =names[0];
                        temp_node.Terminals.push_back(temp_terminal);
                        }
                        temp_terminal = clear_terminal;
                        continue;
                    }
                 }
            }
		
        //read in module information into block, net
        //read in node information, blocks, net and terminal.
        if(in_module==1&&specify==0){	
          //type inputs or outputs for terminal
          if((found=verilog_string.find("input"))!=string::npos){
             temp = split_by_spaces_yg(verilog_string);
             //name extraction
             for(int i=1;i<temp.size();i++){
                if(i<temp.size()-1){
                vector<string> names = get_true_word(0,temp[i],0,',',p);
                temp_name = names[0];
                }
                else{
                    vector<string> names = get_true_word(0,temp[i],0,';',p);
                    temp_name = names[0];
                    }

             for(int j=0;j<temp_node.Terminals.size();j++){
                if(temp_node.Terminals[j].name.compare(temp_name)==0){
                   temp_node.Terminals[j].type = "input";
                   break;
                  }
                }
            }
            continue;
          }
          else{
              if((found=verilog_string.find("output"))!=string::npos){
                 temp = split_by_spaces_yg(verilog_string);
                 //name extraction
                 for(int i=1;i<temp.size();i++){
                    if(i<temp.size()-1){
                       vector<string> names = get_true_word(0,temp[i],0,',',p);
                       temp_name = names[0];
                      }
                      else{
                          vector<string> names = get_true_word(0,temp[i],0,';',p);
                          temp_name = names[0];
                          }

                 for(int j=0;j<temp_node.Terminals.size();j++){
                    if(temp_node.Terminals[j].name.compare(temp_name)==0){
                       temp_node.Terminals[j].type = "output";
                       break;
                      }
                    }
                   }
                 continue;
                }else{
                   if((found=verilog_string.find("supply0"))!=string::npos){
                      temp = split_by_spaces_yg(verilog_string);
                      temp_blockComplex.instance.back().master=temp[0];
                      vector<string> names = get_true_word(0,temp[1],0,';',p);
                      temp_blockComplex.instance.back().name = names[0];
                      Supply_node.Blocks.push_back(temp_blockComplex);
                      temp_blockComplex = clear_blockComplex;
                      continue;
                    }else{
                      if((found=verilog_string.find("supply1"))!=string::npos){
                        temp = split_by_spaces_yg(verilog_string);
                        temp_blockComplex.instance.back().master=temp[0];
                        vector<string> names = get_true_word(0,temp[1],0,';',p);
                        temp_blockComplex.instance.back().name = names[0];
                        Supply_node.Blocks.push_back(temp_blockComplex);
                        temp_blockComplex = clear_blockComplex;
                        continue;
                       }
                        else{
                        temp = split_by_spaces_yg(verilog_string);
                        temp_blockComplex.instance.back().master=temp[0];
                        temp_blockComplex.instance.back().name=temp[1];
                        // read in pin for blockComplex.instance 
                        for(int i=3;i<temp.size()-1;i++){
                          temp_pin.name =  get_word(temp[i],'.','(');
                          string net_name = get_word(temp[i],'(',')');
                          int net_index=0;
                          if(temp_node.Nets.size()==0){
                            temp_net.name = net_name;
                            temp_net.degree = 1;
                            temp_connectNode.type = PnRDB::Block;
                            temp_connectNode.iter = i-3;
                            temp_connectNode.iter2 = temp_node.Blocks.size();
                            temp_net.connected.push_back(temp_connectNode);
                            temp_node.Nets.push_back(temp_net);
                            temp_net=clear_net;
                            net_index=0;
                            }
                          //to add a connection for terminal, when the nets name = terminal names
                            else{
                               int found_flag=0;
                               for(int k=0;k<temp_node.Nets.size();k++){
                                   if(temp_node.Nets[k].name.compare(net_name)==0){
                                      temp_node.Nets[k].degree++;
                                      temp_connectNode.type = PnRDB::Block;
                                      temp_connectNode.iter = i-3;
                                      temp_connectNode.iter2 = temp_node.Blocks.size();
                                      temp_node.Nets[k].connected.push_back(temp_connectNode);
                                      found_flag=1;
                                      net_index =k;
                                     }
                                   }

                                if(found_flag==0){
                                   temp_net.name = net_name;
                                   temp_net.degree = 1;
                                   temp_connectNode.type = PnRDB::Block;
                                   temp_connectNode.iter = i-3;
                                   temp_connectNode.iter2 = temp_node.Blocks.size();
                                   temp_net.connected.push_back(temp_connectNode);
                                   net_index = temp_node.Nets.size();
                                   temp_node.Nets.push_back(temp_net);
                                   temp_net=clear_net;
                                  }
                              }
                          temp_pin.netIter=net_index;
                          temp_blockComplex.instance.back().blockPins.push_back(temp_pin);
                         }
                       }
               temp_node.Blocks.push_back(temp_blockComplex);
               temp_blockComplex = clear_blockComplex;
              }
           }	
          }
         }
        }
    //update hiear tree here for the class Nodes.
    //inistial 
    for(int i=0;i<hierTree.size();i++){
        for(int j=0;j<hierTree[i].Blocks.size();j++){
            hierTree[i].Blocks[j].child==-1;
            }
        }
		
    //update hiear tree here for the class Nodes.
    for(int i=0;i<hierTree.size();i++){
        for(int j=0;j<hierTree.size();j++){
            for(int k=0;k<hierTree[j].Blocks.size();k++)
                if(hierTree[j].Blocks[k].instance.back().master.compare(hierTree[i].name)==0){
                   hierTree[j].Blocks[k].child = i;
                   int parent_found = 0;
                   for(int p=0;p<hierTree[i].parent.size();p++){
                       if(hierTree[i].parent[p] == j){parent_found=1;} 
                      }
                   if(parent_found==0){hierTree[i].parent.push_back(j);}                   
                  }
            }
        if(hierTree[i].name.compare(topcell)==0){
           topidx =i;
           hierTree[i].isTop = 1;
          }
                //update terminal information
        for(int l=0;l<hierTree[i].Nets.size();l++){
            for(int m=0;m<hierTree[i].Terminals.size();m++){
                if(hierTree[i].Nets[l].name.compare(hierTree[i].Terminals[m].name)==0){
                   hierTree[i].Nets[l].degree++;
                   temp_connectNode.type = PnRDB::Terminal;
                   temp_connectNode.iter = m;
                   temp_connectNode.iter2 = -1;
                   hierTree[i].Nets[l].connected.push_back(temp_connectNode);
                   hierTree[i].Nets[l].sink2Terminal = 1;
                   hierTree[i].Terminals[m].netIter = l;
                   }
                }
            }
      }
		
    for(int i=0;i<hierTree.size();i++){
        for(int j=0;j<hierTree[i].Blocks.size();j++){
            if(hierTree[i].Blocks[j].child==-1){
               hierTree[i].Blocks[j].instance.back().isLeaf=1;
               }
        else{
             hierTree[i].Blocks[j].instance.back().isLeaf=0;
             }
           }
       }

  std::cout<<"Middle\n";
    //mergeLEFandGDS
    for(int i=0;i<hierTree.size();i++){
    //cout<<"hierTree node "<<i<<endl;
    if(!MergeLEFMapData(hierTree[i])){cerr<<"PnRDB-Error: fail to mergeLEFMapData of module "<<hierTree[i].name<<endl;
      }else{
      std::cout<<"Finished merge lef data"<<std::endl;
      }
      }
  // wbxu: following lines need modifications to reflect changes of block instance vector
  //update powernets information
  std::cout<<"Middle\n";
  for(int i=0;i<Supply_node.Blocks.size();i++){
      std::string supply_name_full = Supply_node.name+"."+Supply_node.Blocks[i].instance.back().name;
      std::string supply_name = Supply_node.Blocks[i].instance.back().name;
      int power;
      if(Supply_node.Blocks[i].instance.back().master == "supply0"){
         power = 0;
        }else{
         power =1;
        }
      for(int j=0;j<hierTree.size();j++){
           std::vector<PnRDB::net> temp_net;
           for(int k=0;k<hierTree[j].Nets.size();k++){
               if(hierTree[j].Nets[k].name == supply_name_full or hierTree[j].Nets[k].name == supply_name){
                   PnRDB::PowerNet temp_PowerNet;
                   temp_PowerNet.name = hierTree[j].Nets[k].name;
                   temp_PowerNet.power = power;
                   temp_PowerNet.connected = hierTree[j].Nets[k].connected;
                   hierTree[j].PowerNets.push_back(temp_PowerNet);
                 }else{
                   temp_net.push_back(hierTree[j].Nets[k]);
                 }
              }
            hierTree[j].Nets = temp_net;
         }
     }
 
  //update pins & terminal connection iternet
  for(int i=0;i<hierTree.size();i++){
      for(int j=0;j<hierTree[i].Nets.size();j++){
           for(int k=0;k<hierTree[i].Nets[j].connected.size();k++){
                if(hierTree[i].Nets[j].connected[k].type == PnRDB::Block){
                        for(int m=0;m<(int)hierTree[i].Blocks[hierTree[i].Nets[j].connected[k].iter2].instance.size();++m) {
                            hierTree[i].Blocks[hierTree[i].Nets[j].connected[k].iter2].instance.at(m).blockPins[hierTree[i].Nets[j].connected[k].iter].netIter = j;
                        } // [RA] need confirmation -wbxu
                  }else{
hierTree[i].Terminals[hierTree[i].Nets[j].connected[k].iter].netIter = j;
                  }
              }
         }
       
      for(int j=0;j<hierTree[i].PowerNets.size();j++){

           for(int k=0;k<hierTree[i].PowerNets[j].connected.size();k++){
                if(hierTree[i].PowerNets[j].connected[k].type == PnRDB::Block){
                    for(int m=0;m<(int) hierTree[i].Blocks[hierTree[i].PowerNets[j].connected[k].iter2].instance.size();++m) {
                    hierTree[i].Blocks[hierTree[i].PowerNets[j].connected[k].iter2].instance.at(m).blockPins[hierTree[i].PowerNets[j].connected[k].iter].netIter = -1; 
                    }  // [RA] need confirmation - wbxu
                    hierTree[i].PowerNets[j].Pins.push_back(hierTree[i].Blocks[hierTree[i].PowerNets[j].connected[k].iter2].instance.back().blockPins[hierTree[i].PowerNets[j].connected[k].iter]); // [AR] need modification -wbxu
                  }else{
                    hierTree[i].Terminals[hierTree[i].PowerNets[j].connected[k].iter].netIter = -1;
                    PnRDB::pin temp_pin;
                    temp_pin.name = hierTree[i].Terminals[hierTree[i].PowerNets[j].connected[k].iter].name;
                    temp_pin.netIter = -1;
                    temp_pin.pinContacts = hierTree[i].Terminals[hierTree[i].PowerNets[j].connected[k].iter].termContacts;
                    hierTree[i].PowerNets[j].Pins.push_back(temp_pin);
                  }
              }

         }
     }
   
  std::cout<<"End of reading verilog\n";
  return true;
  }
catch(ifstream::failure e){
  cerr<<"PnRDB-Error: fail to read Verilog file "<<endl;
  return false;
  }
}

bool PnRdatabase::MergeLEFMapData(PnRDB::hierNode& node){
  bool missing_lef_file = 0;

  std::cout<<"PnRdatabase-Info:: merge LEF/map data\n";
  for(int i=0;i<node.Blocks.size();i++){
    string master=node.Blocks[i].instance.back().master;
    if(lefData.find(master)==lefData.end()) {
	// LEF is missing; Ok if a cap or if not a leaf
	if(master.find("Cap")!=std::string::npos or
	   master.find("cap")!=std::string::npos) continue;
	if(node.Blocks[i].instance.back().isLeaf) {
	    cerr<<"PnRDB-Error: the key does not exist in map:"<<" "<<master<<endl;
	    missing_lef_file = 1;
	}
	continue;
    }
    
    //cout<<node.Blocks[i].instance.back().name<<" "<<master<<endl;
    for(int w=0;w<(int)lefData[master].size();++w) {
      if(node.Blocks[i].instNum>0) { node.Blocks[i].instance.push_back( node.Blocks[i].instance.back() ); }
      node.Blocks[i].instNum++;
      node.Blocks[i].instance.back().width=lefData[master].at(w).width;
      node.Blocks[i].instance.back().height=lefData[master].at(w).height;
      node.Blocks[i].instance.back().lefmaster=lefData[master].at(w).name;
      node.Blocks[i].instance.back().originBox.LL.x=0;
      node.Blocks[i].instance.back().originBox.LL.y=0;
      node.Blocks[i].instance.back().originBox.polygon.clear();
      node.Blocks[i].instance.back().originBox.polygon.push_back(node.Blocks[i].instance.back().originBox.LL);
      node.Blocks[i].instance.back().originBox.UL.x=0;
      node.Blocks[i].instance.back().originBox.UL.y=lefData[master].at(w).height;
      node.Blocks[i].instance.back().originBox.polygon.push_back(node.Blocks[i].instance.back().originBox.UL);
      node.Blocks[i].instance.back().originBox.UR.x=lefData[master].at(w).width;
      node.Blocks[i].instance.back().originBox.UR.y=lefData[master].at(w).height;
      node.Blocks[i].instance.back().originBox.polygon.push_back(node.Blocks[i].instance.back().originBox.UR);
      node.Blocks[i].instance.back().originBox.LR.x=lefData[master].at(w).width;
      node.Blocks[i].instance.back().originBox.LR.y=0;
      node.Blocks[i].instance.back().originBox.polygon.push_back(node.Blocks[i].instance.back().originBox.LR);
      node.Blocks[i].instance.back().originCenter.x=lefData[master].at(w).width/2;
      node.Blocks[i].instance.back().originCenter.y=lefData[master].at(w).height/2;

      for(int j=0;j<lefData[master].at(w).macroPins.size();j++){
        bool found = 0;
        for(int k=0;k<node.Blocks[i].instance.back().blockPins.size();k++){
          if(lefData[master].at(w).macroPins[j].name.compare(node.Blocks[i].instance.back().blockPins[k].name)==0){
            node.Blocks[i].instance.back().blockPins[k].type = lefData[master].at(w).macroPins[j].type;
            node.Blocks[i].instance.back().blockPins[k].pinContacts = lefData[master].at(w).macroPins[j].pinContacts;
            node.Blocks[i].instance.back().blockPins[k].use = lefData[master].at(w).macroPins[j].use;
            found = 1;
            }
        }
        if(found == 0){
          node.Blocks[i].instance.back().blockPins.push_back(lefData[master].at(w).macroPins[j]);
        }
      }

      node.Blocks[i].instance.back().interMetals = lefData[master].at(w).interMetals;
      node.Blocks[i].instance.back().gdsFile=gdsData[lefData[master].at(w).name];
  //cout<<"xxx "<<node.Blocks[i].instance.back().gdsFile<<endl;
    }


  }

  assert( !missing_lef_file);

  return 1;
  
}

// [RA] need confirmation - wbxu
void PnRdatabase::updatePowerPins(PnRDB::pin& temp_pin){
 
  for(int i=0;i<temp_pin.pinContacts.size();i++){
    
       temp_pin.pinContacts[i].originBox = temp_pin.pinContacts[i].placedBox;
       temp_pin.pinContacts[i].placedBox.polygon.clear();
       temp_pin.pinContacts[i].originCenter =  temp_pin.pinContacts[i].placedCenter;           

     }

  for(int i=0;i<temp_pin.pinVias.size();i++){

       temp_pin.pinVias[i].originpos = temp_pin.pinVias[i].placedpos;
       temp_pin.pinVias[i].ViaRect.originBox =  temp_pin.pinVias[i].ViaRect.placedBox;
       temp_pin.pinVias[i].ViaRect.placedBox.polygon.clear();
       temp_pin.pinVias[i].ViaRect.originCenter = temp_pin.pinVias[i].ViaRect.placedCenter;

       //temp_pin.pinVias[i].originpos = temp_pin.pinVias[i].placedpos;
       temp_pin.pinVias[i].UpperMetalRect.originBox =  temp_pin.pinVias[i].UpperMetalRect.placedBox;
       temp_pin.pinVias[i].UpperMetalRect.placedBox.polygon.clear();
       temp_pin.pinVias[i].UpperMetalRect.originCenter = temp_pin.pinVias[i].UpperMetalRect.placedCenter;

       //temp_pin.pinVias[i].originpos = temp_pin.pinVias[i].placedpos;
       temp_pin.pinVias[i].LowerMetalRect.originBox =  temp_pin.pinVias[i].LowerMetalRect.placedBox;
       temp_pin.pinVias[i].LowerMetalRect.placedBox.polygon.clear();
       temp_pin.pinVias[i].LowerMetalRect.originCenter = temp_pin.pinVias[i].LowerMetalRect.placedCenter;

     }

};

// [RA] need further modification for hierarchical issue - wbxu
void PnRdatabase::CheckinHierNode(int nodeID, PnRDB::hierNode& updatedNode){
  //In fact, the original node, do not need to be updated. Just update father node is fine.
  //update the original node
  std::cout<<"CheckinHierNode\n";
  PnRDB::layoutAS tmpL;
  tmpL.gdsFile=updatedNode.gdsFile;
  tmpL.width=updatedNode.width;
  tmpL.height=updatedNode.height;
  tmpL.Blocks=updatedNode.Blocks;
  tmpL.Terminals=updatedNode.Terminals;
  tmpL.Nets=updatedNode.Nets;
  hierTree[nodeID].PnRAS.push_back(tmpL);

  hierTree[nodeID].isCompleted = 1;
  hierTree[nodeID].gdsFile = updatedNode.gdsFile;
  //update current node information
  for(int i=0;i<hierTree[nodeID].Blocks.size();i++){
     int sel=updatedNode.Blocks[i].selectedInstance;
     std::cout<<"Block "<<i<<" select "<<sel<<std::endl;
     if(sel<0 or sel>=updatedNode.Blocks[i].instNum) {std::cout<<"PnRDB-Error: unselected block "<<i<<std::endl;continue;}
     //std::cout<<"dB "<<hierTree[nodeID].Blocks[i].instNum<<std::endl;
     if(hierTree[nodeID].Blocks[i].instNum<updatedNode.Blocks[i].instNum) { // for capacitor, new data in place and route
       hierTree[nodeID].Blocks[i].instance.clear();
       hierTree[nodeID].Blocks[i].instance=updatedNode.Blocks[i].instance;
       hierTree[nodeID].Blocks[i].instNum=updatedNode.Blocks[i].instNum;
     }
     hierTree[nodeID].Blocks[i].selectedInstance=sel;
     for(int w=0;w<updatedNode.Blocks[i].instNum;++w) {
     //std::cout<<"\tchoice "<<w<<std::endl;
     //hierTree[nodeID].Blocks[i].instance.at(w).name = updatedNode.Blocks[i].instance.at(w).name;
     hierTree[nodeID].Blocks[i].instance.at(w).orient = updatedNode.Blocks[i].instance.at(w).orient;
     //std::cout<<"\t\tcheck 1\n";
     hierTree[nodeID].Blocks[i].instance.at(w).placedBox = updatedNode.Blocks[i].instance.at(w).placedBox;
     //std::cout<<"\t\tcheck 2\n";
     hierTree[nodeID].Blocks[i].instance.at(w).placedCenter = updatedNode.Blocks[i].instance.at(w).placedCenter;
     //std::cout<<"\t\tcheck 3\n";
     for(int j=0;j<hierTree[nodeID].Blocks[i].instance.at(w).blockPins.size();j++){
        for(int k=0;k<hierTree[nodeID].Blocks[i].instance.at(w).blockPins[j].pinContacts.size();k++){
           hierTree[nodeID].Blocks[i].instance.at(w).blockPins[j].pinContacts[k]= updatedNode.Blocks[i].instance.at(w).blockPins[j].pinContacts[k];
           }
        for(int k=0;k<hierTree[nodeID].Blocks[i].instance.at(w).blockPins[j].pinVias.size();k++){
           hierTree[nodeID].Blocks[i].instance.at(w).blockPins[j].pinVias[k]= updatedNode.Blocks[i].instance.at(w).blockPins[j].pinVias[k];
           }  
        }
     //std::cout<<"\t\tcheck 4\n";
     for(int j=0;j<hierTree[nodeID].Blocks[i].instance.at(w).interMetals.size();j++){
           hierTree[nodeID].Blocks[i].instance.at(w).interMetals[j]= updatedNode.Blocks[i].instance.at(w).interMetals[j];
        }
     //std::cout<<"\t\tcheck 5\n";
     for(int j=0;j<hierTree[nodeID].Blocks[i].instance.at(w).interVias.size();j++){
           hierTree[nodeID].Blocks[i].instance.at(w).interVias[j]= updatedNode.Blocks[i].instance.at(w).interVias[j];
        }     
     }
	 
  }

    

  //update terminals information when the node is top level
    if(updatedNode.isTop==1){	 
       for(int i=0;i<hierTree[nodeID].Terminals.size();i++){
            hierTree[nodeID].Terminals[i].termContacts.clear();
           for(int j=0;j<updatedNode.Terminals[i].termContacts.size();j++){ //this line $$$$yaguang$$$$$
               hierTree[nodeID].Terminals[i].termContacts.push_back( updatedNode.Terminals[i].termContacts[j]  );
               //hierTree[nodeID].Terminals[i].termContacts[j].placedBox= updatedNode.Terminals[i].termContacts[j].placedBox;
	       //hierTree[nodeID].Terminals[i].termContacts[j].placedCenter= updatedNode.Terminals[i].termContacts[j].placedCenter;
               }
         }
       }
  
  //update net information//////
  for(int i=0;i<hierTree[nodeID].Nets.size();i++){
     for(int j=0;j<updatedNode.Nets.size();j++){
          if(hierTree[nodeID].Nets[i].name ==updatedNode.Nets[j].name){
               hierTree[nodeID].Nets[i].path_metal = updatedNode.Nets[j].path_metal;
               hierTree[nodeID].Nets[i].path_via = updatedNode.Nets[j].path_via;
               break;
            }
        }
     }
  std::cout<<"update power net\n";
  //update PowerNet information//////
  std::cout<<"hierTree power net size "<<hierTree[nodeID].PowerNets.size()<<std::endl;
  std::cout<<"updatedNode power net size "<<updatedNode.PowerNets.size()<<std::endl;
  for(int i=0;i<hierTree[nodeID].PowerNets.size();i++){
     for(int j=0;j<updatedNode.PowerNets.size();j++){
         if(hierTree[nodeID].PowerNets[i].name == updatedNode.PowerNets[j].name){
               hierTree[nodeID].PowerNets[i].path_metal = updatedNode.PowerNets[j].path_metal;
               hierTree[nodeID].PowerNets[i].path_via = updatedNode.PowerNets[j].path_via;
               hierTree[nodeID].PowerNets[i].connected = updatedNode.PowerNets[j].connected;
               hierTree[nodeID].PowerNets[i].dummy_connected = updatedNode.PowerNets[j].dummy_connected;
               hierTree[nodeID].PowerNets[i].Pins = updatedNode.PowerNets[j].Pins;
               break;
           }
         }
     }
   std::cout<<"node ID "<<nodeID<<std::endl;
   std::cout<<"hierTree power net size "<<hierTree[nodeID].PowerNets.size()<<std::endl;
   std::cout<<"updatedNode power net size "<<updatedNode.PowerNets.size()<<std::endl;

   hierTree[nodeID].blockPins=updatedNode.blockPins;
   hierTree[nodeID].interMetals=updatedNode.interMetals;
   hierTree[nodeID].interVias=updatedNode.interVias;
  //update father imformation//////
    std::cout<<"Update parent\n";
    for(int i=0;i<hierTree[nodeID].parent.size();i++){

     std::cout<<"Start update blocks in parent"<<std::endl;
     //update father blocks information
     for(int j=0;j<hierTree[hierTree[nodeID].parent[i]].Blocks.size();j++){
        
        if(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().master.compare(updatedNode.name)==0){
          if(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instNum>0) {
            hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.push_back( hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back() );
          }
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instNum++;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().gdsFile = updatedNode.gdsFile;
          //update terminal to pin information
          
          for(int p=0;p<hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().blockPins.size();p++){
              for(int q=0;q<updatedNode.blockPins.size();q++){
                  if(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().blockPins[p].name.compare(updatedNode.blockPins[q].name)==0){                     
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().blockPins[p].pinContacts.clear();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().blockPins[p].pinContacts = updatedNode.blockPins[q].pinContacts;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().blockPins[p].pinVias.clear();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().blockPins[p].pinVias = updatedNode.blockPins[q].pinVias;
          break;     
                     }
                   
                 }
              
          }
          
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().interMetals.clear();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().interMetals = updatedNode.interMetals;
          
/*
          for(int k=0;k<updatedNode.Blocks.size();k++){
              for(int l=0;l<updatedNode.Blocks[k].instance.interMetals.size();l++){                      	   hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.interMetals.push_back(updatedNode.Blocks[k].instance.interMetals[l]);
                 } 
          }
*/          
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().interVias.clear();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().interVias = updatedNode.interVias;
/*
          for(int k=0;k<updatedNode.Blocks.size();k++){
              for(int l=0;l<updatedNode.Blocks[k].instance.interVias.size();l++){                      	   hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.interVias.push_back(updatedNode.Blocks[k].instance.interVias[l]);
                 }
          }
*/
          
          //update block physical information to father.Blocks.instance
	  //int max_x,min_x,max_y,min_y;
          //max_x=updatedNode.Blocks[0].instance.placedBox.LL.x;
          //min_x=updatedNode.Blocks[0].instance.placedBox.LL.x;
          //max_y=updatedNode.Blocks[0].instance.placedBox.LL.y;
          //min_y=updatedNode.Blocks[0].instance.placedBox.LL.y;
          //for(int l=0;l<updatedNode.Blocks.size();l++){
          //   if(updatedNode.Blocks[l].instance.placedBox.LL.x<min_x){
          //      min_x = updatedNode.Blocks[l].instance.placedBox.LL.x;
          //     }
          //   if(updatedNode.Blocks[l].instance.placedBox.LR.x>max_x){
          //      max_x = updatedNode.Blocks[l].instance.placedBox.LR.x;
          //     }
          //   if(updatedNode.Blocks[l].instance.placedBox.LL.y<min_y){
          //      min_y = updatedNode.Blocks[l].instance.placedBox.LL.y;
          //     }
          //   if(updatedNode.Blocks[l].instance.placedBox.UL.y>max_y){
          //      max_y = updatedNode.Blocks[l].instance.placedBox.UR.y;
          //     }
          //   }
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.width=max_x-min_x;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.height=max_y-min_y;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originCenter.x =  min_x+(max_x-min_x)/2;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originCenter.y =  min_y+(max_y-min_y)/2;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LL.x = min_x;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LL.y = min_y;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UL.x = min_x;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UL.y = max_y;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UR.x = max_x;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UR.y = max_y;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LR.x = max_x;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LR.y = min_y;
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.clear();
          //if(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.size()>0){
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          //hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          //}
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().width=updatedNode.width;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().height=updatedNode.height;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originCenter.x = updatedNode.width/2;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originCenter.y = updatedNode.height/2;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.LL.x = 0;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.LL.y = 0;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.UL.x = 0;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.UL.y = updatedNode.height;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.UR.x = updatedNode.width;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.UR.y = updatedNode.height;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.LR.x = updatedNode.width;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.LR.y = 0;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.polygon.clear();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.LL);
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.UL);
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.UR);
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().originBox.LR);
          }
        }

    std::cout<<"Start Update power pin in parent"<<std::endl;
     //update power pin information
     for(int j=0;j<hierTree[hierTree[nodeID].parent[i]].Blocks.size();j++){
          if(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().master.compare(updatedNode.name)==0){
             for(int k = 0; k<updatedNode.PowerNets.size();k++){
                  int found = 0;
                  
                  for(int l =0;l<hierTree[hierTree[nodeID].parent[i]].PowerNets.size();l++){
                       if(updatedNode.PowerNets[k].name == hierTree[hierTree[nodeID].parent[i]].PowerNets[l].name){
                            found = 1;

                            hierTree[hierTree[nodeID].parent[i]].PowerNets[l].dummy_connected.clear();

                            for(int p=0;p<updatedNode.PowerNets[k].Pins.size();p++){
                                  PnRDB::connectNode temp_connectNode;
                                  temp_connectNode.iter2 = j;
                                  temp_connectNode.iter = hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().dummy_power_pin.size();
                                  hierTree[hierTree[nodeID].parent[i]].PowerNets[l].dummy_connected.push_back(temp_connectNode);
                                  PnRDB::pin temp_pin;
                                  temp_pin=updatedNode.PowerNets[k].Pins[p];
                                  
                                  updatePowerPins(temp_pin);

                                  hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().dummy_power_pin.push_back(temp_pin);
                               }
                         }
                     }
                  if(found ==0){
                      PnRDB::PowerNet temp_PowerNet;
                      temp_PowerNet = updatedNode.PowerNets[k];
                      temp_PowerNet.connected.clear();
                      temp_PowerNet.Pins.clear();
                      
                      for(int p=0;p<updatedNode.PowerNets[k].Pins.size();p++){
                             PnRDB::pin temp_pin;
                             PnRDB::connectNode temp_connectNode;
                             temp_connectNode.iter2 = j;
                             temp_connectNode.iter = hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().dummy_power_pin.size();
                             temp_pin = updatedNode.PowerNets[k].Pins[p];
                             updatePowerPins(temp_pin);
                             hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.back().dummy_power_pin.push_back(temp_pin);
                             temp_PowerNet.dummy_connected.push_back(temp_connectNode);
                          }
                      
                      hierTree[hierTree[nodeID].parent[i]].PowerNets.push_back(temp_PowerNet);
                    }
                }             
            }
        }
     std::cout<<"End update power pin in parent"<<std::endl;
     }

  std::cout<<"End update blocks in parent"<<std::endl;
  
  /*
  for(int i=0;i<hierTree[nodeID].parent.size();i++){
     
     //update father blocks information
     for(int j=0;j<hierTree[hierTree[nodeID].parent[i]].Blocks.size();j++){
        
        if(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.master.compare(updatedNode.name)==0){
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.gdsFile = updatedNode.gdsFile;
          //update terminal to pin information
          for(int k=0;k<hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.blockPins.size();k++){
              hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.blockPins[k].pinContacts= updatedNode.Terminals[k].termContacts;
             }
		  //update child node net information to the block intermetels of father
          for(int k=0;k<updatedNode.Nets.size();k++){
			  for(int l=0;l<updatedNode.Nets[k].segments.size();l++){
			      hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.interMetals.push_back(updatedNode.Nets[k].segments[l]);
			  }

                  
                  //to be done: update interVias of child node net information to the block interVias of father
                          for(int l=0;l<updatedNode.Nets[k].interVias.size();l++){
			      hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.interVias.push_back(updatedNode.Nets[k].interVias[l]);
			  }
                           
			 }
          //to be done: update interVias of child node net information to the block interVias of father
          
          //update block physical information to father.Blocks.instance
	  int max_x,min_x,max_y,min_y;
          max_x=updatedNode.Blocks[0].instance.placedBox.LL.x;
          min_x=updatedNode.Blocks[0].instance.placedBox.LL.x;
          max_y=updatedNode.Blocks[0].instance.placedBox.LL.y;
          min_y=updatedNode.Blocks[0].instance.placedBox.LL.y;
          for(int l=0;l<updatedNode.Blocks.size();l++){
             if(updatedNode.Blocks[l].instance.placedBox.LL.x<min_x){
                min_x = updatedNode.Blocks[l].instance.placedBox.LL.x;
               }
             if(updatedNode.Blocks[l].instance.placedBox.LR.x>max_x){
                max_x = updatedNode.Blocks[l].instance.placedBox.LR.x;
               }
             if(updatedNode.Blocks[l].instance.placedBox.LL.y<min_y){
                min_y = updatedNode.Blocks[l].instance.placedBox.LL.y;
               }
             if(updatedNode.Blocks[l].instance.placedBox.UL.y>max_y){
                max_y = updatedNode.Blocks[l].instance.placedBox.UR.y;
               }
             }
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.width=max_x-min_x;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.height=max_y-min_y;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originCenter.x =  min_x+(max_x-min_x)/2;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originCenter.y =  min_y+(max_y-min_y)/2;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LL.x = min_x;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LL.y = min_y;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UL.x = min_x;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UL.y = max_y;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UR.x = max_x;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UR.y = max_y;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LR.x = max_x;
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LR.y = min_y;
          if(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.size()>0){
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.pop_back();
          }
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LL);
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UL);
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.UR);
          hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.polygon.push_back(hierTree[hierTree[nodeID].parent[i]].Blocks[j].instance.originBox.LR);
          }
        }
     }
     */


}

bool PnRdatabase::WriteLef(PnRDB::hierNode &node, string file, string opath){

  std::ofstream leffile;
  string leffile_name = opath + file;

  leffile.open(leffile_name);

  double time = 2000;
  
  leffile<<"MACRO "<<node.name<<std::endl;
  leffile<<"  ORIGIN 0 0 ;"<<std::endl;
  leffile<<"  FOREIGN "<<node.name<<" 0 0 ;"<<std::endl;
  leffile<<"  SIZE "<< (double) node.width/time<<" BY "<<(double) node.height/time <<" ;"<<std::endl;

  //pins
  for(int i=0;i<node.blockPins.size();i++){

      leffile<<"  PIN "<<node.blockPins[i].name<<std::endl;
      leffile<<"    DIRECTION INOUT ;"<<std::endl;
      leffile<<"    USE SIGNAL ;"<<std::endl;
      //leffile<<"    DIRECTION "<<node.blockPins[i].type<<" ;"<<std::endl;
      //leffile<<"    USE "<<node.blockPins[i].use<<" 0 0 ;"<<std::endl;
      leffile<<"    PORT "<<std::endl;

      for(int j=0;j<node.blockPins[i].pinContacts.size();j++){

         leffile<<"      LAYER "<<node.blockPins[i].pinContacts[j].metal<<" ;"<<std::endl;
         leffile<<"        RECT "<<(double) node.blockPins[i].pinContacts[j].originBox.LL.x/time<<" "<<(double) node.blockPins[i].pinContacts[j].originBox.LL.y/time<<" "<<(double) node.blockPins[i].pinContacts[j].originBox.UR.x/time<<" "<<(double) node.blockPins[i].pinContacts[j].originBox.UR.y/time<<" ;"<<std::endl;

         }
      
      leffile<<"    END"<<std::endl;
      leffile<<"  END "<<node.blockPins[i].name<<std::endl;  
      
 
     }

  leffile<<"  OBS "<<std::endl;
  for(int i=0;i<node.interMetals.size();i++){

     
     leffile<<"  LAYER "<<node.interMetals[i].metal<<" ;"<<std::endl;
     leffile<<"        RECT "<<(double) node.interMetals[i].originBox.LL.x/time<<" "<<(double) node.interMetals[i].originBox.LL.y/time<<" "<<(double) node.interMetals[i].originBox.UR.x/time<<" "<<(double) node.interMetals[i].originBox.UR.y/time<<" ;"<<std::endl;

     }
  leffile<<"  END "<<std::endl;

  leffile<<"END "<<node.name<<std::endl;
  
  leffile.close();
  


}

void PnRdatabase::WriteGlobalRoute(PnRDB::hierNode& node, string rofile, string opath) {
  std::ofstream OF2(opath+rofile);
  if(OF2.fail()) {
    cout<< "PnRData-Error: cannot open the file "<<rofile<<endl;
    return;
  }
  OF2<<"{"<<endl<<"  \"wires\": ["<<endl;
  int i=0;
  for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
    for(vector<PnRDB::Metal>::iterator it2=it->path_metal.begin(); it2!=it->path_metal.end(); ++it2) {
      //if(it2->LinePoint.at(0).x==it2->LinePoint.at(1).x and it2->LinePoint.at(0).y==it2->LinePoint.at(1).y) {continue;}
      if(i!=0) {OF2<<","<<std::endl;}
      i++;
      OF2<<"    { \"layer\": \""<<DRC_info.Metal_info.at(it2->MetalIdx).name;
      OF2<<"\", \"net_name\": \""<<it->name<<"\", \"width\": "<<it2->width;
      OF2<<", \"rect\": [ "<<it2->LinePoint.at(0).x<<", "<<it2->LinePoint.at(0).y<<", "<<it2->LinePoint.at(1).x<<", "<<it2->LinePoint.at(1).y<<"],"<<std::endl;
      OF2<<"      \"connected_pins\": ["<<std::endl;
      int mIdx=it2-it->path_metal.begin();
      int sinkCount=0;
      for(int k=0;k<it->connectedContact.size();++k) {
        if(it->connectedContact.at(k).metalIdx!=mIdx) {continue;}
        if(it->connected.at(k).type==PnRDB::Block) {
          if(sinkCount!=0) {OF2<<","<<std::endl;}
          OF2<<"          { "<<"\"sink_name\": \""<<node.Blocks.at(it->connected.at(k).iter2).instance.back().name<<"/"<<node.Blocks.at(it->connected.at(k).iter2).instance.back().blockPins.at(it->connected.at(k).iter).name<<"\"";
        } else if (it->connected.at(k).type==PnRDB::Terminal and node.isTop) {
          if(sinkCount!=0) {OF2<<","<<std::endl;}
          OF2<<"          { "<<"\"sink_name\": \""<<node.Terminals.at(it->connected.at(k).iter).name<<"\"";
        } else {continue;}
        ++sinkCount;
        OF2<<", \"layer\": \""<<it->connectedContact.at(k).conTact.metal<<"\", \"rect\": ["<<it->connectedContact.at(k).conTact.placedBox.LL.x<<", "<<it->connectedContact.at(k).conTact.placedBox.LL.y<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.x<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.y<<"] }";
      }
      if(sinkCount>0) {OF2<<std::endl;}
      OF2<<"      ]"<<std::endl;
      OF2<<"    }";
      //if(it!=node.Nets.end()-1 or it2!=it->segments.end()-1) {OF2<<",";}
      //OF2<<endl;
    }
  }
  OF2<<std::endl<<"  ]"<<endl;
  //OF2<<"  \"rects\": ["<<endl;
  //for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
  //  if(node.isTop) {
  //    if(it->connected.size()<=1) {continue;}
  //  } else {
  //    if(!it->sink2Terminal and it->connected.size()<=1) {continue;}
  //    if(it->sink2Terminal and it->connected.size()<=2) {continue;}
  //  }
  //  for(int k=0;k<it->connectedContact.size();++k) {
  //    if(it->connected.at(k).type==PnRDB::Block) {
  //      OF2<<"    { \"net_name\": \""<<it->name<<"\", \"sink_name\": \""<<node.Blocks.at(it->connected.at(k).iter2).instance.back().name<<"/"<<node.Blocks.at(it->connected.at(k).iter2).instance.back().blockPins.at(it->connected.at(k).iter).name<<"\"";
  //    } else if (it->connected.at(k).type==PnRDB::Terminal and node.isTop) {
  //      OF2<<"    { \"net_name\": \""<<it->name<<"\", \"sink_name\": \""<<node.Terminals.at(it->connected.at(k).iter).name<<"\"";
  //    } else {continue;}
  //    OF2<<", metalIdx: "<<it->connectedContact.at(k).metalIdx<<", \"layer\": \""<<it->connectedContact.at(k).conTact.metal<<"\", \"rect\": ["<<it->connectedContact.at(k).conTact.placedBox.LL.x<<", "<<it->connectedContact.at(k).conTact.placedBox.LL.y<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.x<<", "<<it->connectedContact.at(k).conTact.placedBox.UR.y<<"] },"<<endl;
  //  }
  //}
  OF2<<endl<<"}";
  OF2.close();
}

void PnRdatabase::WritePlaceRoute(PnRDB::hierNode& node, string pofile, string rofile) {
  std::ofstream OF(pofile);
  if(OF.fail()) {
    cout<< "PnRData-Error: cannot open the file "<<pofile<<endl;
    return;
  }
  int Xunit,Yunit;
  switch (DRC_info.Metal_info.at(0).direct) {
    case 1: // H -> Y axis
            Yunit=DRC_info.Metal_info.at(0).grid_unit_y; break;
    case 0: // V -> X axis
            Xunit=DRC_info.Metal_info.at(0).grid_unit_x; break;
    default:
            cout<<"PnRData-Error: incorrect routing direction"<<endl;
  }
  switch (DRC_info.Metal_info.at(1).direct) {
    case 1: // H -> Y axis
            Yunit=DRC_info.Metal_info.at(1).grid_unit_y; break;
    case 0: // V -> X axis
            Xunit=DRC_info.Metal_info.at(1).grid_unit_x; break;
    default:
            cout<<"PnRData-Error: incorrect routing direction"<<endl;
  }
  cout<<"Xunit "<<Xunit<<" ; Yunit "<<Yunit<<endl;
  OF<<"{"<<endl;
  // write current node name
  OF<<"  \"nm\": \""<<node.name<<"\","<<endl;
  OF<<"  \"bbox\": [ "<<0<<", "<<0<<", "<<node.width/Xunit<<", "<<node.height/Yunit<<"],"<<endl;
  //OF<<"  \"bbox\": [ "<<0<<", "<<0<<", "<<node.width<<", "<<node.height<<"],"<<endl;
  // write leaf master
  OF<<"  \"leaves\": ["<<endl;
  string endStr;
  endStr=(lefData.rbegin())->first;
  for( map<string, std::vector<PnRDB::lefMacro> >::iterator it=lefData.begin(); it!=lefData.end(); ++it) {
    string lefname;
    for(int w=0;w<(int)node.Blocks.size();++w) {
      if(it->first.compare(node.Blocks.at(w).instance.back().master)==0) {
        lefname=node.Blocks.at(w).instance.at( node.Blocks.at(w).selectedInstance ).lefmaster;
        break;
      }
    }
    int sel;
    for(int w=0;w<it->second.size();++w) {
      if(it->second.at(w).name.compare(lefname)==0) {sel=w;break;}
    }
    OF<<"    {"<<endl;
    OF<<"      \"template_name\": \""<<(it->second).at(sel).master<<"\","<<endl;
    OF<<"      \"bbox\": [ 0, 0, "<<(it->second).at(sel).width/Xunit<<", "<<(it->second).at(sel).height/Yunit<<"],"<<endl;
    OF<<"      \"terminales\": ["<<endl;
    for(vector<PnRDB::pin>::iterator it2=(it->second).at(sel).macroPins.begin(); it2!=(it->second).at(sel).macroPins.end(); ++it2) {
      for(vector<PnRDB::contact>::iterator it3=it2->pinContacts.begin(); it3!=it2->pinContacts.end(); ++it3) {
        //int metalUnit;
        //int metalIdx=DRC_info.Metalmap[it3->metal];
        //if (DRC_info.Metal_info.at(metalIdx).direct==0) { //V
        //  metalUnit=DRC_info.Metal_info.at(metalIdx).grid_unit_x;
        //  OF<<"        { \"net_name\": \""<<it2->name<<"\", \"layer\": \""<<it3->metal<<"\", \"rect\": [ "<<it3->originBox.LL.x<<", "<<it3->originBox.LL.y<<", "<<it3->originBox.UR.x<<", "<<it3->originBox.UR.y<<"]}";
        //} else if(DRC_info.Metal_info.at(metalIdx).direct==1) { // H
        //  metalUnit=DRC_info.Metal_info.at(metalIdx).grid_unit_y;
        //  OF<<"        { \"net_name\": \""<<it2->name<<"\", \"layer\": \""<<it3->metal<<"\", \"rect\": [ "<<it3->originBox.LL.x<<", "<<it3->originBox.LL.y<<", "<<it3->originBox.UR.x<<", "<<it3->originBox.UR.y<<"]}";
        //} else {
        //  cout<<"PnRDB-Error: undefined direction found"<<endl;
        //}
        OF<<"        { \"net_name\": \""<<it2->name<<"\", \"layer\": \""<<it3->metal<<"\", \"rect\": [ "<<it3->originBox.LL.x<<", "<<it3->originBox.LL.y<<", "<<it3->originBox.UR.x<<", "<<it3->originBox.UR.y<<"]}";
        if(!(it2==(it->second).at(sel).macroPins.end()-1 and it3==it2->pinContacts.end()-1)) {
          OF<<",";
        }
        OF<<endl;
      }
    }
    OF<<"      ]"<<endl<<"    }";
    if(it->first.compare(endStr)!=0) {OF<<",";}
    OF<<endl;
  }
  OF<<"  ],"<<endl;
  // write instances
  OF<<"  \"instances\": ["<<endl;
  for(vector<PnRDB::blockComplex>::iterator it=node.Blocks.begin(); it!=node.Blocks.end(); ++it) {
    int sel=it->selectedInstance;
    if(sel<0 or sel>=it->instNum) {std::cout<<"PnRDB-Error: unselected block\n";}
    OF<<"    {"<<endl;
    OF<<"      \"instance_name\": \""<<it->instance.at(sel).name<<"\","<<endl;
    OF<<"      \"template_name\": \""<<it->instance.at(sel).master<<"\","<<endl;
    OF<<"      \"transformation\": {"<<endl;
    if(it->instance.at(sel).orient==PnRDB::N) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x-(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y-(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<1<<",\n      \"sY\": "<<1<<"\n      },"<<endl;
    } else if (it->instance.at(sel).orient==PnRDB::S) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x+(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y+(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<-1<<",\n      \"sY\": "<<-1<<"\n      },"<<endl;
    } else if (it->instance.at(sel).orient==PnRDB::FN) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x+(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y-(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<-1<<",\n      \"sY\": "<<1<<"\n      },"<<endl;
    } else if (it->instance.at(sel).orient==PnRDB::FS) {
      OF<<"      \"oX\": "<<(it->instance.at(sel).placedCenter.x-(it->instance.at(sel).width/2))/Xunit<<",\n      \"oY\": "<<(it->instance.at(sel).placedCenter.y+(it->instance.at(sel).height/2))/Yunit<<",\n      \"sX\": "<<1<<",\n      \"sY\": "<<-1<<"\n      },"<<endl;
    } else {
      cout<<"PnRDB-Error: unsupported orientation!"<<endl;
    }
    OF<<"      \"formal_actual_map\": {"<<endl;
    int maxNo=0;
    for(vector<PnRDB::pin>::iterator it2=it->instance.at(sel).blockPins.begin(); it2!=it->instance.at(sel).blockPins.end(); ++it2) {
      if(it2->netIter!=-1) maxNo++;
    }
    for(vector<PnRDB::pin>::iterator it2=it->instance.at(sel).blockPins.begin(); it2!=it->instance.at(sel).blockPins.end(); ++it2) {
      int netID=it2->netIter;
      if(netID==-1) {continue;}
      maxNo--;
      OF<<"        \""<<it2->name<<"\": \""<<node.Nets.at(netID).name<<"\"";
      if(maxNo>0) {OF<<",";}
      OF<<endl;
    }
    OF<<"      }"<<endl<<"    }";
    if(it!=node.Blocks.end()-1) {OF<<",";}
    OF<<endl;
  }
  OF<<"  ]"<<endl;
  OF<<"}";
  OF.close();
/*
  std::ofstream OF2(rofile);
  if(OF2.fail()) {
    cout<< "PnRData-Error: cannot open the file "<<rofile<<endl;
    return;
  }
  OF2<<"{"<<endl<<"  \"wires\": ["<<endl;
  for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
    for(vector<PnRDB::route>::iterator it2=it->segments.begin(); it2!=it->segments.end(); ++it2) {
      int metalIdx=DRC_info.Metalmap[it2->metal];
      OF2<<"    { \"layer\": \""<<it2->metal<<"\", \"net_name\": \""<<it->name<<"\", \"width\": "<<DRC_info.Metal_info.at(metalIdx).width*10/2<<", \"rect\": [ "<<it2->src.x<<", "<<it2->src.y<<", "<<it2->dest.x<<", "<<it2->dest.y<<"]}";
      if(it!=node.Nets.end()-1 or it2!=it->segments.end()-1) {OF2<<",";}
      OF2<<endl;
    }
    OF2<<endl;
  }
  OF2<<"  ]"<<endl<<"}";
  OF2.close();
*/
}

void PnRdatabase::PrintDesignRuleData() {
  cout<<"=== Design Rule Data ==="<<endl;
 for(map<string, int>::iterator it=drData.MinWidth.begin(); it!=drData.MinWidth.end(); ++it) {
    cout<<it->first<<" width "<<it->second<<endl;
  }
  for(map<string, int>::iterator it=drData.MaxSpace.begin(); it!=drData.MaxSpace.end(); ++it) {
    cout<<it->first<<" space "<<it->second<<endl;
  }
  for(map<string, int>::iterator it=drData.EnMax.begin(); it!=drData.EnMax.end(); ++it) {
    cout<<it->first<<" enclose "<<it->second<<endl;
  }
  for(map<string, int>::iterator it=drData.TrkSpacing.begin(); it!=drData.TrkSpacing.end(); ++it) {
    cout<<it->first<<" trackspace "<<it->second<<endl;
  }
  for(map<string, int>::iterator it=drData.grid_unit_x.begin(); it!=drData.grid_unit_x.end(); ++it) {
    cout<<it->first<<" grid x "<<it->second<<endl;
  }
  for(map<string, int>::iterator it=drData.grid_unit_y.begin(); it!=drData.grid_unit_y.end(); ++it) {
    cout<<it->first<<" grid y "<<it->second<<endl;
  }
}

// void PnRdatabase::GDSReaderWriterTxTFile_extension(string GDSData, GdsParser::GdsWriter& gw, long int& rndnum, vector<string>& strBlocks, vector<int>& llx, vector<int>& lly, vector<int>& urx, vector<int>& ury)
// {

// //{{{

//   	//cout<<"Reading & Writing GDS & Gen. txt file for debugging"<<endl;
//   	rndnum++;
// 	string GDS_txt = "GDS_Building_Block_" + std::to_string(rndnum)+".txt";
// 	//cout<<"GDS_txt: "<< GDS_txt<<endl;

// 	string GDS_txt_location = "./router/GDS_To_ASCII/" + GDS_txt;

// 	std::ofstream output_GDS_txt;
// 	output_GDS_txt.open(GDS_txt_location);

// 	//blockGDS_file_name.push_back(GDS_txt_location);

// 	//cout <<"#BLOCKS: "<<rndnum<<endl;
// 	EnumDataBase edb;
// 	//cout << "TEST enum API"<<endl;
// 	GdsParser::read(edb, GDSData);

//         // + wbxu
// 	//cout<<"wbxu testing"<<endl;
//         for(int i=0;i<edb.record_list.size();i++) {
//           //cout<<"Line# "<<i<<" "<<edb.record_list.at(i)<<" "<<edb.data_list.at(i)<<endl;
//         }
//         for(int i=0;i<edb.header_db_int2.size();i++) {
// 	  //cout<<"edb.header_db_int2: "<<edb.header_db_int2[i]<<endl;
//         }
// 	//***** Print & Change to lower case GDS Data *****//
// 	//cout <<"begin_end_cbk_vec.size() :"<< edb.begin_end_cbk_vec.size()<<endl;
// 	for(int q=0;q<edb.begin_end_cbk_vec.size();q++){
// 		//Upper case to Lower case	
// 		std::transform(edb.begin_end_cbk_vec[q].begin(), edb.begin_end_cbk_vec[q].end(), edb.begin_end_cbk_vec[q].begin(),::tolower);
// 		//cout<<"edb.begin_end_cbk_vec #"<< q<<" :"<<edb.begin_end_cbk_vec[q]<<endl;
// 	}
// 	//cout<<"after callback"<<endl;;
// 	for(int q=0;q<edb.header_db_int4.size();q++)
// 	{
// 		//cout<<"edb.header_db_int4: "<<edb.header_db_int4[q]<<" edb.vInteger_vec_int4 -> ";
// 		for(int qq=0;qq<edb.vInteger_vec_int4[q].size();qq++){
// 			//cout<<edb.vInteger_vec_int4[q][qq]<<" ";
// 		}
//                 //cout<<endl;
// 	}
// 	//cout <<"header_db_int4.size() :"<< edb.header_db_int4.size()<<endl;
// 	//cout <<"data_type_db_int4.size() :"<< edb.data_type_db_int4.size()<<endl;
// 	//cout <<"vInteger_vec_int4.size() :"<< edb.vInteger_vec_int4.size()<<endl;
// 	for(int q=0;q<edb.header_db_int4.size();q++)
// 	{
// 		//Upper case to Lower case	
// 		std::transform(edb.header_db_int4[q].begin(), edb.header_db_int4[q].end(), edb.header_db_int4[q].begin(),::tolower);
// 		std::transform(edb.data_type_db_int4[q].begin(), edb.data_type_db_int4[q].end(), edb.data_type_db_int4[q].begin(),::tolower);
		
// 		//cout<<"edb.header_db_int4: "<<edb.header_db_int4[q]<<" ";	 
// 		//cout<<"edb.data_type_db_int4: "<< edb.data_type_db_int4[q]<<"edb.vInteger_vec_int4 ->  ";
		
// 		for(int qq=0;qq<edb.vInteger_vec_int4[q].size();qq++){
// 			//cout<<edb.vInteger_vec_int4[q][qq]<<" ";
// 		}
// 		//cout<<endl;	
// 	}	
// 	for(int q=0;q<edb.data_type_db_int4.size();q++){
// 		//cout<<"edb.data_type_db_int4: "<<edb.data_type_db_int4[q]<<endl;
// 	}
// 	for(int q=0;q<edb.vInteger_vec_int4.size();q++){
// 		//cout<<"Data int4: ";
// 		for(int qq=0;qq<edb.vInteger_vec_int4[q].size();qq++){
// 			//cout<<"edb.vInteger_vec_int4: "<<edb.vInteger_vec_int4[q][qq]<<" ";
// 		}
// 		//cout<<endl;
// 	}

// 	for(int q=0;q<edb.header_db_string.size();q++)
// 	{
// 		//Upper case to Lower case	
// 		std::transform(edb.header_db_string[q].begin(), edb.header_db_string[q].end(), edb.header_db_string[q].begin(),::tolower);
// 		std::transform(edb.data_type_db_string[q].begin(), edb.data_type_db_string[q].end(), edb.data_type_db_string[q].begin(),::tolower);
// 		//cout<<"edb.header_db_string: "<<edb.header_db_string[q]<<endl;
// 	}
// 	for(int q=0;q<edb.data_type_db_string.size();q++){
// 		//cout<<"edb.data_type_db_string: "<<edb.data_type_db_string[q]<<endl;
// 	}	
// 	for(int q=0;q<edb.vInteger_vec_string.size();q++){
// 		//cout<<"edb.vInteger_vec_string: "<<edb.vInteger_vec_string[q]<<endl;
// 	}

// 	//cout <<"header_db_Real8.size() :"<< edb.header_db_Real8.size()<<endl;
// 	//cout <<"data_type_db_Real8.size() :"<< edb.data_type_db_Real8.size()<<endl;
// 	//cout <<"vInteger_vec_Real8.size() :"<< edb.vInteger_vec_Real8.size()<<endl;
// 	for(int q=0;q<edb.header_db_Real8.size();q++){
// 		//Upper case to Lower case	
// 		std::transform(edb.header_db_Real8[q].begin(), edb.header_db_Real8[q].end(), edb.header_db_Real8[q].begin(),::tolower);
// 		std::transform(edb.data_type_db_Real8[q].begin(), edb.data_type_db_Real8[q].end(), edb.data_type_db_Real8[q].begin(),::tolower);
// 		//cout<<"edb.header_db_Real8: "<<edb.header_db_Real8[q]<<endl;
// 		//cout<<"edb.data_type_db_Real8: "<<edb.data_type_db_Real8[q]<<" ";
// 		for(int qq=0;qq<edb.vInteger_vec_Real8[q].size();qq++){
// 			//cout<<"edb.vInteger_vec_Real8: "<<edb.vInteger_vec_Real8[q][qq]<<" ";
// 		}
// 		//cout<<endl;
// 	}

// 	//cout<<"print bit array type"<<endl;
// 	//cout<<"bit array header"<<endl;
// 	for(int q=0;q<edb.header_db_bitarray.size();q++)
// 	{
// 		std::transform(edb.header_db_bitarray[q].begin(), edb.header_db_bitarray[q].end(), edb.header_db_bitarray[q].begin(),::tolower);
// 		//cout<<"edb.header_db_bitarray: "<<edb.header_db_bitarray[q]<<endl;
// 	}
// 	//cout<<"bit array datatype"<<endl;
// 	for(int q=0;q<edb.data_type_db_bitarray.size();q++)
// 	{
// 		std::transform(edb.data_type_db_bitarray[q].begin(), edb.data_type_db_bitarray[q].end(), edb.data_type_db_bitarray[q].begin(),::tolower);
// 		//cout<<"edb.data_type_db_bitarray: "<<edb.data_type_db_bitarray[q]<<endl;
// 	}
// 	//cout<<"bit array integer"<<endl;
// 	for(int q=0;q<edb.vInteger_vec_bitarray.size();q++)
// 	{
// 		//cout<<"size vInteger_vec_bitarray[q]: "<<edb.vInteger_vec_bitarray[q].size()<<endl;
// 		for(int qq=0;qq<edb.vInteger_vec_bitarray[q].size();qq++)
// 		{	
// 			//cout<<"edb.vInteger_vec_bitarray: "<<edb.vInteger_vec_bitarray[q][qq]<<endl;
// 		}
// 	}
// 	//Read & Write GDS and Gen. txt file here
//   	double units; 
//   	int layerNo;
//   	double PathWidth; 
//   	int    PathDataType;
//   	int xy_Num;
// 	int datatype;
// 	int texttype;
// 	int presentation;
// 	bool strans;	
// 	int x[5], y[5];
// 	int T_llx=INT_MAX; int T_lly=INT_MAX; int T_urx=-1*INT_MAX; int T_ury=-1*INT_MAX;
//   	string strname;
//   	string sname;
	
// 	//Layer tempLayer;
// 	//Pin tempPin;
	
// 	int be_cbk_cnt=0;	
// 	int int4_cnt=0;	
// 	string tmp_be_cbk_vec;
	
// 	int CntString=0;
// 	int CntHeaderString=0;
// 	int CntReal8=0;
// 	int CntBitArray=0;
// 	int CntBgnstr=0;

// 	//cout <<"Size comparison"<<endl;
// 	//cout <<"header_db_int2.size()    int2  :"<< edb.header_db_int2.size()<<endl;
// 	//cout <<"begin_end_cbk_vec.size() be_cbk:"<< edb.begin_end_cbk_vec.size()<<endl;
// 	//cout <<"header_db_int4.size() :"<< edb.header_db_int4.size()<<endl;
// 	//cout<<"edb.header_db_int2.size(): "<<edb.header_db_int2.size()<<endl;
// 	int int2_idx=0;
//         int int4_idx=0;
//         int real8_idx=0;
//         int string_idx=0;
//         int nodata_idx=0;
//         int bit_idx=0;
// 	for(int i=0;i<edb.record_list.size();i++) {
//           if( edb.record_list[i].compare("HEADER")==0  ) {
//               int2_idx++;
//           } else if( edb.record_list[i].compare("BGNLIB")==0  ) {
//               int2_idx++;
//           } else if( edb.record_list[i].compare("ENDLIB")==0  ) {
//               nodata_idx++;
//           } else if( edb.record_list[i].compare("LIBNAME")==0  ) {
//               string_idx++;
//           } else if( edb.record_list[i].compare("UNITS")==0  ) {
//               real8_idx++;
//           } else if( edb.record_list[i].compare("BGNSTR")==0  ) {
//               gw.gds_write_bgnstr(); 
//               gw.gds_flush(); int2_idx++;
//           } else if( edb.record_list[i].compare("STRNAME")==0  ) {
//               strname=edb.vInteger_vec_string[string_idx]+"_"+std::to_string(rndnum);
// 	      strBlocks.push_back(strname);
//               gw.gds_write_strname( strname.c_str() ); 
//               gw.gds_flush(); string_idx++;
//           } else if( edb.record_list[i].compare("BOUNDARY")==0  ) {
//               gw.gds_write_boundary(); 
//               gw.gds_flush(); nodata_idx++; 
//           } else if( edb.record_list[i].compare("LAYER")==0  ) {
//               gw.gds_write_layer( edb.vInteger_vec_int2[int2_idx][0] ); 
//               gw.gds_flush(); int2_idx++;
//           } else if( edb.record_list[i].compare("DATATYPE")==0  ) {
//               gw.gds_write_datatype(edb.vInteger_vec_int2[int2_idx][0] );
//               gw.gds_flush(); int2_idx++;
//           } else if( edb.record_list[i].compare("XY")==0  ) {
//               int ss=0;
//               for(int w=0;w<(int)edb.vInteger_vec_int4[int4_idx].size();w++) {
// 	          if(w%2 == 0){
// 	      	        x[(int)w/2]=edb.vInteger_vec_int4[int4_idx][w];
// 	          }
// 	          else if(w%2 == 1){
// 	      	        y[(int)w/2]=edb.vInteger_vec_int4[int4_idx][w];
//                         ss++;
// 	          }
//               }
// 	      for(int jj=0;jj<ss;jj++) {
//                   if(T_llx>x[jj]) {T_llx=x[jj];}
//                   if(T_lly>y[jj]) {T_lly=y[jj];}
// 	          if(T_urx<x[jj]) {T_urx=x[jj];} 	
// 	          if(T_ury<y[jj]) {T_ury=y[jj];} 	
// 	      }
// 	      gw.gds_write_xy(  x, y, ss );
//   	      gw.gds_flush(); int4_idx++;
//           } else if( edb.record_list[i].compare("ENDEL")==0  ) {
//               gw.gds_write_endel();
//   	      gw.gds_flush(); nodata_idx++;
//           } else if( edb.record_list[i].compare("ENDSTR")==0  ) {
//               gw.gds_write_endstr(  );
//   	      gw.gds_flush(); nodata_idx++;
//           } else if( edb.record_list[i].compare("TEXT")==0  ) {
//               gw.gds_write_text(  );
//   	      gw.gds_flush(); nodata_idx++;
//           } else if( edb.record_list[i].compare("TEXTTYPE")==0  ) {
//       	      texttype=edb.vInteger_vec_int2[int2_idx][0];
// 	      gw.gds_write_texttype( texttype  );
//   	      gw.gds_flush(); int2_idx++;
//           } else if( edb.record_list[i].compare("PRESENTATION")==0  ) {
// 	      presentation =edb.vInteger_vec_bitarray[bit_idx][0];	
// 	      gw.gds_write_presentation( presentation,1,1 );
// 	      gw.gds_flush(); bit_idx++;
//           } else if( edb.record_list[i].compare("STRANS")==0  ) {
// 	      strans =(bool)edb.vInteger_vec_bitarray[bit_idx][0];	
// 	      gw.gds_write_strans( strans,false,false  );
// 	      gw.gds_flush(); bit_idx++;
//           } else if( edb.record_list[i].compare("MAG")==0  ) {
// 	      gw.gds_write_mag(edb.vInteger_vec_Real8[real8_idx][0]);
// 	      gw.gds_flush(); real8_idx++;
//           } else if( edb.record_list[i].compare("STRING")==0  ) {
// 	      gw.gds_write_string(edb.vInteger_vec_string[string_idx].c_str());
// 	      gw.gds_flush(); string_idx++;
//           } else if( edb.record_list[i].compare("SREF")==0  ) {
//      	      gw.gds_write_sref(  );
//      	      gw.gds_flush(  ); nodata_idx++;
//           } else if( edb.record_list[i].compare("SNAME")==0  ) {
// 	      sname = edb.vInteger_vec_string[string_idx]+"_"+std::to_string(rndnum);	
// 	      gw.gds_write_sname( sname.c_str());
//   	      gw.gds_flush(); string_idx++;
//           } else if( edb.record_list[i].compare("PROPATTR")==0  ) {
//               gw.gds_write_propattr( edb.vInteger_vec_int2[int2_idx][0] );
//               gw.gds_flush(); int2_idx++;   // imcomplete coding- wbxu
//           } else if( edb.record_list[i].compare("PROPVALUE")==0  ) {
//               gw.gds_write_propvalue( edb.vInteger_vec_string[string_idx].c_str() );
//               string_idx++; // imcomplete coding -wbxu
//           } else if( edb.record_list[i].compare("ANGLE")==0  ) {
// 	      gw.gds_write_angle(edb.vInteger_vec_Real8[real8_idx][0]);//angle
//   	      gw.gds_flush(); real8_idx++;
//           } else {
//               std::cerr<<"Error: incorrect record "<<edb.record_list[i]<<std::endl;
//           }
//         }

// /*
// 	for(int q=0;q<edb.header_db_int2.size();q++)
// 	//for(int q=0;q<edb.begin_end_cbk_vec.size();q++)
// 	{
// 	//if(q<edb.header_db_int2.size())	
// 		//Upper case to Lower case	
// 		std::transform(edb.header_db_int2[q].begin(), edb.header_db_int2[q].end(), edb.header_db_int2[q].begin(),::tolower);
// 		std::transform(edb.data_type_db_int2[q].begin(), edb.data_type_db_int2[q].end(), edb.data_type_db_int2[q].begin(),::tolower);
// 		cout<<"Headers int2: "<< edb.header_db_int2[q]<<endl;
	
// 		//int2: header, bgnstr
// 		if(edb.header_db_int2[q].compare("header")==0){
// 			output_GDS_txt << edb.header_db_int2[q]<<" ";
// 			cout<<"Headers int2 header: "<< edb.header_db_int2[q]<<endl;
// 			//output_GDS_txt << edb.data_type_db_int2[q]<<" ";
		
// 			for(int qq=0;qq<edb.vInteger_vec_int2[q].size();qq++){	
// 				output_GDS_txt << edb.vInteger_vec_int2[q][qq]<<" ";
// 			}
// 			output_GDS_txt<<endl;
			
// 		}
// 		else if(edb.header_db_int2[q].compare("bgnlib")==0)
// 		{
// 			cout<<"Headers int2 bgnlib: "<< edb.header_db_int2[q]<<endl;
// 			output_GDS_txt << edb.header_db_int2[q]<<" ";
// 			//output_GDS_txt << edb.data_type_db_int2[q]<<" ";
			
// 			for(int qq=0;qq<edb.vInteger_vec_int2[q].size();qq++){	
// 				output_GDS_txt << edb.vInteger_vec_int2[q][qq]<<" ";
// 			}
// 			output_GDS_txt<<endl;
			
// 			//libname "Research_Project"	
// 			output_GDS_txt<<edb.header_db_string[CntHeaderString]<<" ";
// 			CntHeaderString++;
// 			//output_GDS_txt<<edb.vInteger_vec_string[0]<<endl;
// 	  		cout<<"CntString bgnlib: "<<CntString<<endl;	
// 			output_GDS_txt<<edb.vInteger_vec_string[CntString]<<endl;
// 	  		cout<<"vInteger_vec_string[CntString]: "<<edb.vInteger_vec_string[CntString]<<endl;	
// 			CntString++;
			
// 			//units 0.00025 2.5e-10
// 			output_GDS_txt<<edb.header_db_Real8[CntReal8]<<" ";
// 			for(int qq=0;qq<edb.vInteger_vec_Real8[CntReal8].size();qq++){
// 				output_GDS_txt<<edb.vInteger_vec_Real8[CntReal8][qq]<<" ";
	  			
// 				units=edb.vInteger_vec_Real8[CntReal8][qq];
// 			}
// 			CntReal8++;
// 			output_GDS_txt<<endl;

// 		}
// 		else if(edb.header_db_int2[q].compare("bgnstr")==0 && edb.header_db_string[CntHeaderString].compare("strname")==0)
// 		{
// 			cout<<"Headers int2 bgnstr: "<< edb.header_db_int2[q]<<endl;
// 			output_GDS_txt << edb.header_db_int2[q]<<" ";
// 			//output_GDS_txt << edb.data_type_db_int2[q]<<" ";
			
// 			for(int qq=0;qq<edb.vInteger_vec_int2[q].size();qq++){	
// 				output_GDS_txt << edb.vInteger_vec_int2[q][qq]<<" ";
// 			}
// 			output_GDS_txt<<endl;
// 			output_GDS_txt<<edb.header_db_string[CntHeaderString]<<" ";//strname
// 			cout<<"header_db_string: "<<edb.header_db_string[CntHeaderString]<<endl;//strname
// 			CntHeaderString++;
			
// 			//output_GDS_txt<<edb.vInteger_vec_string[1]<<endl;//GDS Name
// 			output_GDS_txt<<edb.vInteger_vec_string[CntString]<<endl;//GDS Name

// 	  		//strname=edb.vInteger_vec_string[1]+"_"+to_string(rndnum);
// 	  		//strname=edb.vInteger_vec_string[CntString]+"_"+to_string(rndnum);
// 	  		cout<<"CntString bgnstr: "<<CntString<<endl;
// 			strname=edb.vInteger_vec_string[CntString]+"_"+to_string(rndnum);
// 			strBlocks.push_back(strname);
// 			for(int q=0;q<strBlocks.size();q++){
// 				cout<<"strBlocks Name print: "<<strBlocks[q]<<endl;
// 			}

// 			CntString++;
			
// 			if(CntBgnstr!=0)
// 			{
//   				gw.gds_write_endstr(  );
//   				gw.gds_flush(  );
// 				output_GDS_txt<<"endstr"<<endl;
// 			}
//   			// write header and strname for structure
//   			gw.gds_write_bgnstr(  );
//   				gw.gds_flush(  );
//   			CntBgnstr++;
// 			gw.gds_write_strname( strname.c_str() );
//   				gw.gds_flush(  );
// 		}
// 		else
// 		{	
//   	  	//{{{	
// 			InternalPath tempInternalPath;
			
// 			//begin_end: boundary, path, sref	
// 			if(be_cbk_cnt ==0){
// 				//output_GDS_txt <<"q-3? "<<q-3<<endl;	
// 				output_GDS_txt << edb.begin_end_cbk_vec[q-3]<<endl;//"boundary", "path", "text" string
// 				tmp_be_cbk_vec = edb.begin_end_cbk_vec[q-3];	
// 				be_cbk_cnt = 0;	
			
			
// 				if(	tmp_be_cbk_vec.compare("boundary")==0)
// 				{
// 					gw.gds_write_boundary(  );//write "boundary"
//   					gw.gds_flush(  );
// 				}	
// 				if(	tmp_be_cbk_vec.compare("path")==0)
// 				{
// 	  				gw.gds_write_path(  );
//   					gw.gds_flush(  );
// 				}
// 				if(	tmp_be_cbk_vec.compare("text")==0)
// 				{
// 					gw.gds_write_text(  );//write "text"
//   					gw.gds_flush(  );
// 				}	
// 				/////이거 왜 했더라
// 				///////////if(	tmp_be_cbk_vec.compare("sref")==0)
// 				///////////{
//       			///////////	gw.gds_write_sref(  );
// 				///////////}
// 			}	
			
// 			//int2: layers(bn_cbk_cnt==1), datatype(bn_cbk_cnt==2)
// 			output_GDS_txt << edb.header_db_int2[q]<<" ";
// 			be_cbk_cnt++;	
// 			//int2: layers number(bn_cbk_cnt==1), datatype number(bn_cbk_cnt==2)
// 			for(int qq=0;qq<edb.vInteger_vec_int2[q].size();qq++)
// 			{
// 				output_GDS_txt << edb.vInteger_vec_int2[q][qq]<<" ";
		
// 				if(	tmp_be_cbk_vec.compare("boundary")==0)
// 				{//{{{
// 					//gw.gds_write_boundary(  );//write "boundary"

// 					//int2: layers number(bn_cbk_cnt==1)
//       				if(be_cbk_cnt==1){		
// 						layerNo=edb.vInteger_vec_int2[q][qq];///layer 옆 숫자 STORED
// 	  					//tempLayer.layerNum = layerNo;	  //No use 
// 						gw.gds_write_layer( layerNo );
//   						gw.gds_flush(  );
// 					}
// 					//int2: datatype number(bn_cbk_cnt==2)
// 					if(be_cbk_cnt==2){
// 	  					datatype=edb.vInteger_vec_int2[q][qq];///datatype 옆 숫자 STORED
// 						gw.gds_write_datatype( datatype  );
//   						gw.gds_flush(  );
// 					}
// 				}//}}}	
// 				if(	tmp_be_cbk_vec.compare("path")==0)
// 				{//{{{
// 	  				//gw.gds_write_path(  );
// 					//int2: layers number(bn_cbk_cnt==1)
//       				if(be_cbk_cnt==1){		
// 						layerNo=edb.vInteger_vec_int2[q][qq];  ///layer 옆 숫자 STORED
// 	  					//tempLayer.layerNum = layerNo;	   //No use
// 	  					gw.gds_write_layer(  layerNo );
//   						gw.gds_flush(  );
// 					}
// 					//int2: datatype number(bn_cbk_cnt==2)
// 					if(be_cbk_cnt==2){
//       					PathDataType=edb.vInteger_vec_int2[q][qq];//datatype의 숫자
// 	  					tempInternalPath.PathDataType = PathDataType;///datatype 옆 숫자 STORED
// 	  					gw.gds_write_datatype(  PathDataType );
//   						gw.gds_flush(  );
// 					}
// 				}//}}}
// 				if(	tmp_be_cbk_vec.compare("text")==0)
// 				{//{{{
//       				if(be_cbk_cnt==1){		
// 						layerNo=edb.vInteger_vec_int2[q][qq];  ///layer 옆 숫자 STORED
// 	  					//tempLayer.layerNum = layerNo;	   //No use
// 	  					gw.gds_write_layer(  layerNo );
//   						gw.gds_flush(  );
// 					}
// 					//int2: datatype number(bn_cbk_cnt==2)
// 					if(be_cbk_cnt==2){
//       					texttype=edb.vInteger_vec_int2[q][qq];//texttype의 숫자
// 						gw.gds_write_texttype( texttype  );
//   						gw.gds_flush(  );
					
// 					//presentation
// 						if(edb.header_db_bitarray[CntBitArray].compare("presentation")==0)
// 						{
// 							output_GDS_txt <<endl;
// 							output_GDS_txt << edb.header_db_bitarray[CntBitArray]<<" ";
// 							output_GDS_txt << edb.vInteger_vec_bitarray[CntBitArray][0]<<" ";
// 							output_GDS_txt <<endl;
// 							presentation =edb.vInteger_vec_bitarray[CntBitArray][0];	
// 							gw.gds_write_presentation( presentation,1,1  );
//   							gw.gds_flush(  );
// 							CntBitArray++;
// 						}
// 						//strans
// 						if(edb.header_db_bitarray[CntBitArray].compare("strans")==0)
// 						{
// 							output_GDS_txt << edb.header_db_bitarray[CntBitArray]<<" ";
// 							output_GDS_txt << edb.vInteger_vec_bitarray[CntBitArray][0]<<" ";
// 							strans =(bool)edb.vInteger_vec_bitarray[CntBitArray][0];	
// 							gw.gds_write_strans( strans,false,false  );
//   							gw.gds_flush(  );
// 							CntBitArray++;
// 							output_GDS_txt <<endl;
// 						}
// 						//mag
// 						if(	edb.header_db_Real8[CntReal8].compare("mag")==0)
// 						{
// 							//cout<<edb.header_db_Real8[CntReal8]<<" ";
// 							//cout<<edb.vInteger_vec_Real8[CntReal8][0]<<endl;
// 							output_GDS_txt<<edb.header_db_Real8[CntReal8]<<" ";
// 							output_GDS_txt<<edb.vInteger_vec_Real8[CntReal8][0]<<endl;
// 							gw.gds_write_mag(edb.vInteger_vec_Real8[CntReal8][0]);//mag
//   							gw.gds_flush(  );
// 							CntReal8++;
// 						}
// 					}
// 				}//}}}
// 			}
// 			output_GDS_txt<<endl;

// 			//int 4: xy & xy-coordi.(when tmp_be_cbk_vec=="boundary") or  width(when tmp_be_cbk_vec=="path")
// 			if(be_cbk_cnt ==2)
// 			{
// 				output_GDS_txt << edb.header_db_int4[int4_cnt]<<" ";//{{{ 

// 				for(int qq=0;qq<edb.vInteger_vec_int4[int4_cnt].size();qq++)
// 				{
// 					output_GDS_txt<<edb.vInteger_vec_int4[int4_cnt][qq]<<" ";
// 					//cout <<"edb.vInteger_vec_int4[int4_cnt]["<<qq<<"]: "<<edb.vInteger_vec_int4[int4_cnt][qq]<<endl;
// 					//int 4: xy, xy-coordi.(when tmp_be_cbk_vec=="boundary")
// 					if(	tmp_be_cbk_vec.compare("boundary")==0)
// 					{//{{{
// 						if(qq%2 == 0){
// 							//cout<<"vInteger_vec_int4[int4_cnt][qq]: "<<edb.vInteger_vec_int4[int4_cnt][qq]<<endl;
// 							x[(int)qq/2]=edb.vInteger_vec_int4[int4_cnt][qq];
// 							//x[(int)qq/2]=(double)edb.vInteger_vec_int4[int4_cnt][qq];
// 							//cout<< "x[(int)qq/2]:"<<x[(int)qq/2]<<endl;	
// 						}
// 						else if(qq%2 == 1){	
// 							//cout<<"vInteger_vec_int4[int4_cnt][qq]: "<<edb.vInteger_vec_int4[int4_cnt][qq]<<endl;
// 							y[(int)qq/2]=edb.vInteger_vec_int4[int4_cnt][qq];
// 							//y[(int)qq/2]=(double)edb.vInteger_vec_int4[int4_cnt][qq];
// 							//cout<< "y[(int)qq/2]:"<<y[(int)qq/2]<<endl;	
// 						}
// 						else{
// 							//cout<< "x,y coordinates are issue"<<endl;
// 						}
// 					}//}}}
// 					//int 4:width(when tmp_be_cbk_vec=="path")
// 					if(	tmp_be_cbk_vec.compare("path")==0)
// 					{//{{{
//       					PathWidth=(double)(edb.vInteger_vec_int4[int4_cnt][qq]);//width line의 숫자
// 	  					tempInternalPath.PathWidth = PathWidth*units/1000000;
// 	  					gw.gds_write_width(  PathWidth );
//   						gw.gds_flush(  );
// 					}//}}}
// 					//int 4: xy, xy-coordi.(when tmp_be_cbk_vec=="text")
// 					if(	tmp_be_cbk_vec.compare("text")==0)
// 					{//{{{
// 						if(qq%2 == 0){
// 							//cout<<"vInteger_vec_int4[int4_cnt][qq]: "<<edb.vInteger_vec_int4[int4_cnt][qq]<<endl;
// 							x[(int)qq/2]=edb.vInteger_vec_int4[int4_cnt][qq];
// 							//x[(int)qq/2]=(double)edb.vInteger_vec_int4[int4_cnt][qq];
// 							//cout<< "x[(int)qq/2]:"<<x[(int)qq/2]<<endl;	
// 						}
// 						else if(qq%2 == 1){	
// 							//cout<<"vInteger_vec_int4[int4_cnt][qq]: "<<edb.vInteger_vec_int4[int4_cnt][qq]<<endl;
// 							y[(int)qq/2]=edb.vInteger_vec_int4[int4_cnt][qq];
// 							//y[(int)qq/2]=(double)edb.vInteger_vec_int4[int4_cnt][qq];
// 							//cout<< "y[(int)qq/2]:"<<y[(int)qq/2]<<endl;	
// 						}
// 					xy_Num = edb.vInteger_vec_int4[int4_cnt].size()/2;
				
// 					}//}}}
// 				}
// 				output_GDS_txt<<endl;
// 				int4_cnt++;
// 				//int4: xy & xy-coordi, only when previous line is width(path)	
// 				if(tmp_be_cbk_vec.compare("path")==0){
//   	  				InternalPath tempInternalPath;//{{{
// 					output_GDS_txt << edb.header_db_int4[int4_cnt]<<" ";	 
					
// 					for(int qq=0;qq<edb.vInteger_vec_int4[int4_cnt].size();qq++){
// 						output_GDS_txt<<edb.vInteger_vec_int4[int4_cnt][qq]<<" ";
// 						if(qq%2 == 0){
// 							//x[(int)qq/2]=(double)(edb.vInteger_vec_int4[int4_cnt][qq]);
// 							//cout<<"vInteger_vec_int4[int4_cnt][qq]: "<<edb.vInteger_vec_int4[int4_cnt][qq]<<endl;
// 							x[(int)qq/2]=edb.vInteger_vec_int4[int4_cnt][qq];
// 						}	
// 						else if(qq%2 == 1){	
// 							//cout<<"vInteger_vec_int4[int4_cnt][qq]: "<<edb.vInteger_vec_int4[int4_cnt][qq]<<endl;
// 							y[(int)qq/2]=edb.vInteger_vec_int4[int4_cnt][qq];
// 						}	
// 						else{	
// 							//cout<< "x,y coordinates are issue"<<endl;
// 						}	
// 					}
// 					xy_Num = edb.vInteger_vec_int4[int4_cnt].size()/2;
// 					output_GDS_txt<<endl;
// 					int4_cnt++;//}}}
// 				}
// 				//boundary write	
// 				if(	tmp_be_cbk_vec.compare("boundary")==0){
// 					for(int jj=0;jj<5;jj++) {//{{{
//             		if(T_llx>x[jj]) {T_llx=x[jj];}
//             		if(T_lly>y[jj]) {T_lly=y[jj];}
// 					if(T_urx<x[jj]) {T_urx=x[jj];} 	
// 					if(T_ury<y[jj]) {T_ury=y[jj];} 	
// 	    			//cout<<"write boundary: "<<x[jj]<<" "<<y[jj]<<endl;	
// 					}
// 					//tempLayer.pins.push_back(tempPin);//No use
// 					gw.gds_write_xy(  x, y, 5 );//}}}
//   					gw.gds_flush(  );
// 				}	
// 				//path write	
// 				if(	tmp_be_cbk_vec.compare("path")==0){
// 					for(int jj=0;jj<xy_Num;jj++) {//{{{
// 						if(T_llx>x[jj]) {T_llx=x[jj];}
// 						if(T_lly>y[jj]) {T_lly=y[jj];}
// 						if(T_urx<x[jj]) {T_urx=x[jj];}
// 						if(T_ury<y[jj]) {T_ury=y[jj];}
// 					}
// 	  				gw.gds_write_xy(  x, y, xy_Num );
//   					gw.gds_flush(  );
// 					//}}}
// 				}		
// 				//text write	
// 				if(	tmp_be_cbk_vec.compare("text")==0){
// 					for(int jj=0;jj<xy_Num;jj++) {//{{{
//             		if(T_llx>x[jj]) {T_llx=x[jj];}
//             		if(T_lly>y[jj]) {T_lly=y[jj];}
// 					if(T_urx<x[jj]) {T_urx=x[jj];} 	
// 					if(T_ury<y[jj]) {T_ury=y[jj];} 	
// 	    			}
// 					gw.gds_write_xy(  x, y, xy_Num );//}}}
//   					gw.gds_flush(  );
				
// 					//string
// 					if(edb.header_db_string[CntHeaderString].compare("string")==0)
// 					{
// 						output_GDS_txt<<edb.header_db_string[CntHeaderString]<<" ";
// 						CntHeaderString++;
// 	  					cout<<"CntString text_string: "<<CntString<<endl;
// 						//output_GDS_txt<<edb.vInteger_vec_string[0]<<endl;
// 						output_GDS_txt<<edb.vInteger_vec_string[CntString]<<endl;
// 						gw.gds_write_string(edb.vInteger_vec_string[CntString].c_str());
//   						gw.gds_flush(  );
// 						//CntString++;//**temporary comment-out
// 					}	
// 				}	
				
// 			//}}}			
// 			}
// 			//begin_end: endel, endstr, endlib	
// 			if(be_cbk_cnt==2)
// 			{
// 			//{{{	
// 				if(q < edb.header_db_int2.size()-2 &&  q < edb.begin_end_cbk_vec.size())
// 				{
// 				output_GDS_txt << edb.begin_end_cbk_vec[q-3]<<endl;//"endel" string
// 				be_cbk_cnt = 0;
// 				gw.gds_write_endel(  );
//   				gw.gds_flush(  );
// 				}	
// 				//if(q == edb.header_db_int2.size()-1 &&  q < edb.begin_end_cbk_vec.size())
// 				if(q == edb.header_db_int2.size()-2 &&  q < edb.begin_end_cbk_vec.size())
// 				{
// 					for(int qq=q-2; qq<edb.begin_end_cbk_vec.size()-2;qq=qq+2)
// 					{
// 						//output_GDS_txt << qq<<endl;	
// 						output_GDS_txt<<edb.begin_end_cbk_vec[qq]<<endl;//"sref" string
//       					gw.gds_write_sref(  );
//   						gw.gds_flush(  );
						
// 						if(CntHeaderString<edb.header_db_string.size())
// 						{
// 							output_GDS_txt<<edb.header_db_string[CntHeaderString]<<" ";//sname
// 							CntHeaderString++;
// 						}	
						
// 						if(CntString<edb.vInteger_vec_string.size())
// 						{
// 							//cout <<"CntString: "<<CntString<<endl;
// 							output_GDS_txt<<edb.vInteger_vec_string[CntString]<<endl;//"current_mirror"
// 	  						sname = edb.vInteger_vec_string[CntString]+"_"+to_string(rndnum);	
// 							gw.gds_write_sname( sname.c_str());
//   							gw.gds_flush(  );
// 							CntString++;
// 						}

// 						if(CntBitArray<edb.header_db_bitarray.size())
// 						{
// 							output_GDS_txt<<edb.header_db_bitarray[CntBitArray]<<" ";	
// 							output_GDS_txt<<edb.vInteger_vec_bitarray[CntBitArray][0]<<endl;
// 							if(edb.vInteger_vec_bitarray[CntBitArray][0]==32768)//32768=0x8000(hexa)
// 							{
// 								gw.gds_write_strans(true,false,false);	
//   								gw.gds_flush(  );
// 							}	
// 							else if(edb.vInteger_vec_bitarray[CntBitArray][0]==0)
// 							{
// 								gw.gds_write_strans(false,false,false);
//   								gw.gds_flush(  );
// 							}
// 							CntBitArray++;
// 						}

// 						if(CntReal8<edb.vInteger_vec_Real8.size())
// 						{
// 							output_GDS_txt<<edb.header_db_Real8[CntReal8]<<" ";
// 							output_GDS_txt<<edb.vInteger_vec_Real8[CntReal8][0]<<endl;
// 							gw.gds_write_angle(edb.vInteger_vec_Real8[CntReal8][0]);//angle
//   							gw.gds_flush(  );
// 							CntReal8++;
// 						}
						
// 						//if(int4_cnt<edb.vInteger_vec_int4.size())
// 						if(int4_cnt-1<edb.vInteger_vec_int4.size())
// 						{
// 						//cout<<int4_cnt<<endl;	
// 						output_GDS_txt<<"xy 1 ";
// 						//output_GDS_txt<<edb.vInteger_vec_int4[int4_cnt][0]<<" ";
// 						//output_GDS_txt<<edb.vInteger_vec_int4[int4_cnt][1]<<endl;
// 						//x[0] = edb.vInteger_vec_int4[int4_cnt][0];
// 						//y[0] = edb.vInteger_vec_int4[int4_cnt][1];
// 						output_GDS_txt<<edb.vInteger_vec_int4[int4_cnt-1][0]<<" ";
// 						output_GDS_txt<<edb.vInteger_vec_int4[int4_cnt-1][1]<<endl;
// 						x[0] = edb.vInteger_vec_int4[int4_cnt-1][0];
// 						y[0] = edb.vInteger_vec_int4[int4_cnt-1][1];
// 						int4_cnt++;	
// 	  					gw.gds_write_xy(  x, y, 1 );
//   						gw.gds_flush(  );
// 						}	
// 						////sref write	
// 						//if(	tmp_be_cbk_vec.compare("sref")==0){
// 						//	for(int jj=0;jj<1;jj++) {//{{{
// 						//		if(T_llx>x[jj]) {T_llx=x[jj];}
// 						//		if(T_lly>y[jj]) {T_lly=y[jj];}
// 						//		if(T_urx<x[jj]) {T_urx=x[jj];}
// 						//		if(T_ury<y[jj]) {T_ury=y[jj];}
// 						//	}
// 	  					//	gw.gds_write_xy(  x, y, 1 );
// 						//	//}}}
// 						//}		
						
// 						output_GDS_txt<<edb.begin_end_cbk_vec[qq+1]<<endl;//"endel" string
//       					gw.gds_write_endel(  );
//   						gw.gds_flush(  );
// 					}
// 				}
// 					///////////if(q == edb.header_db_int2.size() -1) //int2 ends
// 					///////////{	
// 					///////////	output_GDS_txt << edb.begin_end_cbk_vec[q-2]<<endl;//"endstr" string
// 					///////////	output_GDS_txt << edb.begin_end_cbk_vec[q-1]<<endl;//"endlib" string
// 					///////////}	
// 			//}}}	
// 			}
// 		//}}}	
// 		}//else ends
	
// 	}//for loop ends


//   	gw.gds_write_endstr(  );
//   	gw.gds_flush(  );
//         */
//   	llx.push_back(T_llx);
//   	lly.push_back(T_lly);
//   	urx.push_back(T_urx);
//   	ury.push_back(T_ury);

// 	for(int q=0;q<edb.data_type_db_int2.size();q++){
// 		//cout<<"Data type int2: "<< edb.data_type_db_int2[q]<<endl;

// 	}
// 	for(int q=0;q<edb.vInteger_vec_int2.size();q++){
// 		//cout<<"Data int2: ";
// 		for(int qq=0;qq<edb.vInteger_vec_int2[q].size();qq++){	
// 			//cout << edb.vInteger_vec_int2[q][qq]<<" ";
// 		}
// 		//cout<<endl;	
// 	}
	
	
// 	////cout <<"header_db_Real8.size() :"<< edb.header_db_Real8.size()<<endl;
// 	////cout <<"data_type_db_Real8.size() :"<< edb.data_type_db_Real8.size()<<endl;
// 	////cout <<"vInteger_vec_Real8.size() :"<< edb.vInteger_vec_Real8.size()<<endl;
// 	//for(int q=0;q<edb.header_db_Real8.size();q++){
// 	//	//Upper case to Lower case	
// 	//	std::transform(edb.header_db_Real8[q].begin(), edb.header_db_Real8[q].end(), edb.header_db_Real8[q].begin(),::tolower);
// 	//	std::transform(edb.data_type_db_Real8[q].begin(), edb.data_type_db_Real8[q].end(), edb.data_type_db_Real8[q].begin(),::tolower);
// 	//	
// 	//	//cout<<"Headers Real8: "<<edb.header_db_Real8[q]<<endl;
// 	//	output_GDS_txt<<edb.header_db_Real8[q]<<" ";
// 	//	//output_GDS_txt<<edb.data_type_db_Real8[q]<<" ";
// 	//	for(int qq=0;qq<edb.vInteger_vec_Real8[q].size();qq++){
// 	//		output_GDS_txt<<edb.vInteger_vec_Real8[q][qq]<<" ";
// 	//	}
// 	//	output_GDS_txt<<endl;

// 	//}
	
// 	//for(int q=0;q<edb.data_type_db_Real8.size();q++)
// 	//	//cout<<"Data type Real8: "<<edb.data_type_db_Real8[q]<<endl;
// 	//for(int q=0;q<edb.vInteger_vec_Real8.size();q++){
// 	//	//cout<<"Data Real8: ";
// 	//	for(int qq=0;qq<edb.vInteger_vec_Real8[q].size();qq++){
// 	//		//cout<<edb.vInteger_vec_Real8[q][qq]<<" ";
// 	//	}
// 	//	//cout<<endl;
// 	//}
// 	//cout <<"header_db_string.size() :"<< edb.header_db_string.size()<<endl;
// 	//cout <<"data_type_db_string.size() :"<< edb.data_type_db_string.size()<<endl;
// 	//cout <<"vInteger_vec_string.size() :"<< edb.vInteger_vec_string.size()<<endl;
// 	//for(int q=0;q<edb.header_db_string.size();q++){
// 	//	//Upper case to Lower case	
// 	//	std::transform(edb.header_db_string[q].begin(), edb.header_db_string[q].end(), edb.header_db_string[q].begin(),::tolower);
// 	//	std::transform(edb.data_type_db_string[q].begin(), edb.data_type_db_string[q].end(), edb.data_type_db_string[q].begin(),::tolower);
// 	//	
// 	//	//cout<<"Headers string: "<<edb.header_db_string[q]<<endl;
// 	//	output_GDS_txt<<edb.header_db_string[q]<<" ";
// 	//	//output_GDS_txt<<edb.data_type_db_string[q]<<" ";
// 	//	output_GDS_txt<<edb.vInteger_vec_string[q]<<endl;
// 	//}
// 	//for(int q=0;q<edb.data_type_db_string.size();q++)
// 	//	//cout<<"Data type string: "<<edb.data_type_db_string[q]<<endl;
// 	//for(int q=0;q<edb.vInteger_vec_string.size();q++)
// 	//	//cout<<"Data string: "<<edb.vInteger_vec_string[q]<<endl;

// 	//cout <<"Size comparison"<<endl;
// 	//cout <<"header_db_int2.size()    int2  :"<< edb.header_db_int2.size()<<endl;
// 	//cout <<"begin_end_cbk_vec.size() be_cbk:"<< edb.begin_end_cbk_vec.size()<<endl;
// 	//cout <<"header_db_int4.size() :"<< edb.header_db_int4.size()<<endl;


// 	output_GDS_txt.close();	
// //}}}

// };

// [RA] need confirmation -wbxu
void PnRdatabase::AddingPowerPins(PnRDB::hierNode &node){

  for(int i=0;i<node.PowerNets.size();i++){
       
       for(int j=0;j<node.PowerNets[i].dummy_connected.size();j++){
            int iter2 = node.PowerNets[i].dummy_connected[j].iter2;
            int iter = node.PowerNets[i].dummy_connected[j].iter;
            for(int k=0;k<node.Blocks[iter2].instance.size();k++){
                 PnRDB::pin temp_pin;
                 temp_pin = node.Blocks[iter2].instance[k].dummy_power_pin[iter];
                 temp_pin.netIter = -2;
                 node.PowerNets[i].dummy_connected[j].iter = node.Blocks[iter2].instance[k].blockPins.size();
                 node.Blocks[iter2].instance[k].blockPins.push_back(temp_pin);
               }
           
          }     
     }

   
};

// [RA] need confirmation -wbxu
void PnRdatabase::Extract_RemovePowerPins(PnRDB::hierNode &node){

//extract power pin information

  for(int i = 0;i<node.PowerNets.size();i++){

       node.PowerNets[i].Pins.clear();
      
       for(int j=0;j<node.PowerNets[i].connected.size();j++){
             PnRDB::pin temp_pin;
             int iter = node.PowerNets[i].connected[j].iter;
             int iter2 = node.PowerNets[i].connected[j].iter2;
             temp_pin = node.Blocks[iter2].instance[node.Blocks[iter2].selectedInstance].blockPins[iter];
             node.PowerNets[i].Pins.push_back(temp_pin);
           }

       for(int j=0;j<node.PowerNets[i].dummy_connected.size();j++){
             PnRDB::pin temp_pin;
             int iter = node.PowerNets[i].dummy_connected[j].iter;
             int iter2 = node.PowerNets[i].dummy_connected[j].iter2;
             temp_pin = node.Blocks[iter2].instance[node.Blocks[iter2].selectedInstance].blockPins[iter];
             node.PowerNets[i].Pins.push_back(temp_pin);
           }
     
     }

//remove power pins in blocks

  for(int i=0;i<node.Blocks.size();i++){
     
     for(int k=0;k<node.Blocks[i].instance.size();k++){
       std::vector<PnRDB::pin> temp_pins;
       for(int j=0;j<node.Blocks[i].instance[k].blockPins.size();j++){
            int netIter = node.Blocks[i].instance[k].blockPins[j].netIter;
            if(netIter!=-2){
                 temp_pins.push_back(node.Blocks[i].instance[k].blockPins[j]);
              }else{
                 break;
              }
          }
        node.Blocks[i].instance[k].blockPins.clear();
        node.Blocks[i].instance[k].blockPins = temp_pins;
        }
     }


};

void
JSONExtractUit (string GDSData, double& unit)
{
    std::string jsonFileName = GDSData + ".json";
    //std::cout << "GDS JSON FILE=" << jsonFileName << std::endl;
    json jsonStrAry;
    ifstream jsonFile (jsonFileName);
    if (jsonFile.is_open()) {
	json jedb = json::parse (jsonFile);
	if (jedb["header"].is_number ()) {
	    json libAry = jedb["bgnlib"];
	    for (json::iterator lit = libAry.begin(); lit != libAry.end(); ++lit) {
		json lib = *lit;
		json strAry = lib["units"];
                if(strAry.is_array()) {
                     std::cout<<"Unit "<<strAry<<std::endl;
		     json::iterator xyI = strAry.begin();
                     double xyU=*xyI;
                     unit=2*0.00025/xyU;
                     return;
                }
            }
        }
    }
}

void
JSONReaderWrite_subcells (string GDSData, long int& rndnum,
			  vector<string>& strBlocks, vector<int>& llx, vector<int>& lly,
			  vector<int>& urx, vector<int>& ury, json& mjsonStrAry)
{
    rndnum++;

    std::string jsonFileName = GDSData + ".json";
    std::cout << "GDS JSON FILE=" << jsonFileName << std::endl;

    int TJ_llx=INT_MAX; int TJ_lly=INT_MAX; int TJ_urx=-1*INT_MAX; int TJ_ury=-1*INT_MAX;

    json jsonStrAry;
    ifstream jsonFile (jsonFileName);
    if (jsonFile.is_open()) {
	json jedb = json::parse (jsonFile);
	if (jedb["header"].is_number ()) {
	    json libAry = jedb["bgnlib"];
	    for (json::iterator lit = libAry.begin(); lit != libAry.end(); ++lit) {
		json lib = *lit;
		json strAry = lib["bgnstr"];
		for (json::iterator sit = strAry.begin(); sit != strAry.end(); ++sit) {
		    json str = *sit;
		    string nm = str["strname"];
		    string strname = nm + "_" + std::to_string(rndnum);
		    //json elements = str["elements"];
		    for (json::iterator elmI = str["elements"].begin(); elmI != str["elements"].end(); ++elmI) {
                        TJ_llx=INT_MAX; TJ_lly=INT_MAX; TJ_urx=INT_MIN; TJ_ury=INT_MIN;
			json elm = *elmI;
			if (elm["xy"].is_array()) {
			    json xyAry = elm["xy"];
			    int pos = 0;
			    for (json::iterator xyI = xyAry.begin(); xyI != xyAry.end(); ++xyI, pos++) {
				if (pos % 2) {
				    if (*xyI > TJ_ury) TJ_ury = *xyI;
				    if (*xyI < TJ_lly) TJ_lly = *xyI;
				} else {
				    if (*xyI > TJ_urx) TJ_urx = *xyI;
				    if (*xyI < TJ_llx) TJ_llx = *xyI;
				}
			    }
			} 
                        if (elm["sname"].is_string()) {
                          string sn=elm["sname"];
                          (*elmI)["sname"]=sn+ "_" + std::to_string(rndnum);
                        }
		    }
		    strBlocks.push_back(strname);
		    str["strname"] = strname;
		    mjsonStrAry.push_back (str);
		}
	    }
	} else
	    std::cout << "NOT a VALID JSON FILE: " << jsonFileName << std::endl;
    } else {
	std::cout << "NO JSON FILE: " << jsonFileName << std::endl;
	// DAK: This means we will have a missing subcell!
	// DAK: Should error here
    }
    llx.push_back(TJ_llx);
    lly.push_back(TJ_lly);
    urx.push_back(TJ_urx);
    ury.push_back(TJ_ury);
};

void
JSONLabelTerminals(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, json& elmAry, double unit)
{
    elmAry = json::array();
  
    cout<<"Top: "<<node.isTop<<endl;
    cout<<"#terminals print"<<endl;
    cout<<"#size: "<<node.Terminals.size()<<endl;
    for(int i=0;i<node.Terminals.size();i++){
	cout<<"#name: "<<node.Terminals[i].name<<endl; 
	cout<<"#type: "<<node.Terminals[i].type<<endl; 
	cout<<"#netIter: "<<node.Terminals[i].netIter<<endl; 
	cout<<"#termContact size: "<<node.Terminals[i].termContacts.size()<<endl;
	for(int j=0;j<node.Terminals[i].termContacts.size();j++){
	    cout<<"#contact-metal: "<<node.Terminals[i].termContacts[j].metal<<endl;
	    cout<<"#contact-placedCenter(x,y): "<<node.Terminals[i].termContacts[j].placedCenter.x<<" "
		<<node.Terminals[i].termContacts[j].placedCenter.y<<endl;
	}
    }
    int test_layer;//
    int test_font=1,test_vp=1,test_hp=1;
    int test_texttype=251;//pin purpose
    double test_mag=0.03; 
    int center_x[1],center_y[1];
    string tmpstring;
    
    if (node.isTop == 1) {
	for (int i = 0; i < node.Terminals.size(); i++) {
	    int write = 0;
	    for (int j = 0; j < node.Terminals[i].termContacts.size(); j++) {
		PnRDB::contact con = node.Terminals[i].termContacts[j];
           
		//if (con.metal.compare(NULL)==0){
		if (! con.metal.empty()) {
		    tmpstring = con.metal;
		    cout<<"#test metal string: "<<tmpstring<<endl;
		}
		if (write == 0) {
		    test_layer = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[con.metal]]);
		    center_x[0] = unit * con.placedCenter.x;
		    center_y[0] = unit * con.placedCenter.y;

		    json elm;
		    elm["type"] = "text";
		    elm["layer"] = test_layer;
		    elm["texttype"] = test_texttype;
		    elm["presentation"] = JSON_Presentation (test_font, test_vp, test_hp);

		    elm["strans"] = 0;
		    elm["mag"] = test_mag;
		    json xy = json::array();
		    xy.push_back (center_x[0]);
		    xy.push_back (center_y[0]);
		    elm["xy"] = xy;
		    elm["string"] = node.Terminals[i].name.c_str();
		    elmAry.push_back (elm);
	  
		    write = 1;
		}
	    }
	}
    }
}

void
assignBoxPoints (int* x, int*y, struct PnRDB::bbox b, double unit) {
    x[0] = unit * b.LL.x;
    x[1] = unit * b.UL.x;
    x[2] = unit * b.UR.x;
    x[3] = unit * b.LR.x;
    x[4] = x[0];
    y[0] = unit * b.LL.y;
    y[1] = unit * b.UL.y;
    y[2] = unit * b.UR.y;
    y[3] = unit * b.LR.y;
    y[4] = y[0];
}

void
addTextElements (json& jsonElements, int cenX, int cenY, int layer, const string& text) {
    int test_font=1,test_vp=1,test_hp=1;
    int test_texttype=251; //draw 0, label 2, pin 251, blockage 4
    double test_mag=0.03; 
    json element;
    element["type"] = "text";
    element["layer"] = layer;
    element["texttype"] = test_texttype;
    element["presentation"] = JSON_Presentation (test_font, test_vp, test_hp);

    element["strans"] = 0;
    element["mag"] = test_mag;
    json xy = json::array();
    xy.push_back (cenX);
    xy.push_back (cenY);
    element["xy"] = xy;
    element["string"] = text;
    jsonElements.push_back (element);
}

bool
addMetalBoundaries (json& jsonElements, struct PnRDB::Metal& metal, PnRDB::Drc_info& drc_info, double unit) {
    int x[5], y[5];
    assignBoxPoints (x, y, metal.MetalRect.placedBox, unit);

    if (metal.LinePoint[0].x != metal.LinePoint[1].x or
	metal.LinePoint[0].y != metal.LinePoint[1].y) {
	json bound0;
	bound0["type"] = "boundary";
	bound0["layer"] = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[metal.MetalRect.metal]]);
	bound0["datatype"] = 0;
	json xy = json::array();
	for (size_t i = 0; i < 5; i++) {
	    xy.push_back (x[i]);
	    xy.push_back (y[i]);
	}
	bound0["xy"] = xy;
	jsonElements.push_back (bound0);
	return true;
    }
    return false;
}

bool
addContactBoundaries (json& jsonElements, struct PnRDB::contact& Contact, PnRDB::Drc_info& drc_info, int unit) {

    int x[5], y[5];
    assignBoxPoints (x, y, Contact.placedBox, unit);
    json bound0;
    bound0["type"] = "boundary";
    bound0["layer"] = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[Contact.metal]]);
    bound0["datatype"] = 0;
    json xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	 xy.push_back (x[i]);
	 xy.push_back (y[i]);
       }
    bound0["xy"] = xy; 
    jsonElements.push_back (bound0);


}



void
addOABoundaries (json& jsonElements, int width, int height) {
  int x[5],y[5];
  x[0]=y[0]=x[1]=y[3]=x[4]=y[4]=0; x[2]=x[3]=width; y[1]=y[2]=height;
  json bound1;
  bound1["type"] = "boundary";
  bound1["layer"]=235;
  bound1["datatype"]=5;
  json xy = json::array();
  for (size_t i = 0; i < 5; i++) {
      xy.push_back (x[i]);
      xy.push_back (y[i]);
  }
  bound1["xy"] = xy;
  bound1["propattr"]=126;
  bound1["propvalue"]="oaBoundary:pr";
  jsonElements.push_back (bound1);
//   boundary
//       layer 235
//       datatype 5
//       xy   5   0 0   0 1608   8640 1608   8640 0
//                0 0
//       propattr 126
//       propvalue "oaBoundary:pr"
//       endel

}



void addViaBoundaries (json& jsonElements, struct PnRDB::Via& via, PnRDB::Drc_info& drc_info, double unit) {
    int x[5], y[5];
    assignBoxPoints (x, y, via.ViaRect.placedBox, unit);
    
    json bound0;
    bound0["type"] = "boundary";
    bound0["layer"] = stoi(drc_info.MaskID_Via[drc_info.Viamap[via.ViaRect.metal]]);
    bound0["datatype"] = 0;
    json xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	xy.push_back (x[i]);
	xy.push_back (y[i]);
    }
    bound0["xy"] = xy;
    jsonElements.push_back (bound0);

    //LowerMetalRect
    assignBoxPoints (x, y, via.LowerMetalRect.placedBox, unit);
     
    json bound1;
    bound1["type"] = "boundary";
    bound1["layer"] = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[via.LowerMetalRect.metal]]);
    bound1["datatype"] = 0;
    xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	xy.push_back (x[i]);
	xy.push_back (y[i]);
    }
    bound1["xy"] = xy;
    jsonElements.push_back (bound1);

    //UpperMetalRect
    assignBoxPoints (x, y, via.UpperMetalRect.placedBox, unit);
     
    json bound2;
    bound2["type"] = "boundary";
    bound2["layer"] =
	stoi(drc_info.MaskID_Metal[drc_info.Metalmap[via.UpperMetalRect.metal]]);
    bound2["datatype"] = 0;
    xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	xy.push_back (x[i]);
	xy.push_back (y[i]);
    }
    bound2["xy"] = xy;
    jsonElements.push_back (bound2);
}

std::string
PnRdatabase::WriteJSON (PnRDB::hierNode& node, bool includeBlock, bool includeNet, bool includePowerNet,
			bool includePowerGrid, std::string gdsName, PnRDB::Drc_info& drc_info, string opath) {
    std::cout << "JSON WRITE CELL " << gdsName << std::endl;
    node.gdsFile = opath+gdsName+".gds";
    string TopCellName = gdsName;
    std::set<string> uniGDSset;
    double unitScale=2;
	for (int i = 0; i < node.Blocks.size(); i++) 
	    uniGDSset.insert(node.Blocks[i].instance.at( node.Blocks[i].selectedInstance ).gdsFile);

	for (std::set<string>::iterator it=uniGDSset.begin();it!=uniGDSset.end();++it) {
	    JSONExtractUit (*it, unitScale);
	}   
    std::cout<<"unitScale "<<unitScale<<std::endl;
    uniGDSset.clear();
  
    std::ofstream jsonStream;
    jsonStream.open (node.gdsFile + ".json");
    json jsonTop;
    json jsonLibAry = json::array();
    jsonTop["header"] = 600;
    json jsonLib;
    jsonLib["time"] = JSON_TimeTime ();
    double dbUnitUser=2*0.00025/unitScale;
    double dbUnitMeter=dbUnitUser/1e6;
    jsonLib["units"] = {dbUnitUser, dbUnitMeter};
    //jsonLib["units"] = {0.00025, 2.5e-10};
    jsonLib["libname"] = "test";
    json jsonStrAry = json::array();

    vector<string> strBlocks;
    std::map<string, int> gdsMap2strBlock;
    vector<string> strBlocks_Top;
    vector<int> llx, lly, urx, ury;
    long int rndnum = static_cast<long int>(time(NULL));

    int idx = 0;
    if (includeBlock) {
	for (int i = 0; i < node.Blocks.size(); i++) 
	    uniGDSset.insert(node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile);

	cout<<"start wrting sub-blocks"<<endl;
	for (std::set<string>::iterator it=uniGDSset.begin();it!=uniGDSset.end();++it) {
	    json j;
	    JSONReaderWrite_subcells (*it, rndnum, strBlocks, llx,lly,urx,ury, j);
	    for (json::iterator str = j.begin(); str != j.end(); ++str)
		jsonStrAry.push_back (*str);
	    strBlocks_Top.push_back(strBlocks.back());
	    gdsMap2strBlock.insert( std::make_pair(*it, idx) );
	    idx++;
	}   
    }

    json jsonStr;
    jsonStr["time"] = JSON_TimeTime();
    // DAK: Hack to match time for repeated runs
    jsonStr["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
    jsonStr["strname"] = TopCellName.c_str();
    json jsonElements = json::array();

    int x[5], y[5];
    int write_blockPins_name = 0;
    if (write_blockPins_name){
	for (int i = 0; i < node.blockPins.size(); i++) {
	    int write = 0;
	    for (int j = 0; j < node.blockPins[i].pinContacts.size(); j++) {
		PnRDB::contact con = node.blockPins[i].pinContacts[j];
		assignBoxPoints (x, y, con.placedBox, unitScale);
		if (write == 0) {
		    addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2,
				     stoi(drc_info.MaskID_Metal[drc_info.Metalmap[con.metal]]),
				     node.blockPins[i].name);
		    write = 1;	// added by yg 
		}
	    }
	}
    }

    if (includeNet) {
	//cout<<"start writing nets"<<endl;
	for (int i = 0; i < node.Nets.size(); i++) {
	    //path_metal
	    int write = 1;
	    for (int j = 0; j < node.Nets[i].path_metal.size(); j++) {
		PnRDB::Metal metal = node.Nets[i].path_metal[j];
		if (addMetalBoundaries (jsonElements, metal, drc_info, unitScale)) {
		    if (write == 0) {
			assignBoxPoints (x, y, metal.MetalRect.placedBox, unitScale);
			addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2,
					 stoi(drc_info.MaskID_Metal[drc_info.Metalmap[metal.MetalRect.metal]]),
					 node.Nets[i].name);
			write = 1; // added by yg 
		    }
		}
	    }
	    //path_via
	    for (int j = 0; j < node.Nets[i].path_via.size(); j++) 
		addViaBoundaries(jsonElements, node.Nets[i].path_via[j], drc_info, unitScale);
	}
    }
    json j;
    JSONLabelTerminals(node, drc_info, j, unitScale);
    for (json::iterator elm = j.begin(); elm != j.end(); ++elm) jsonElements.push_back (*elm);

    if (includePowerNet) {
	for (int i = 0; i < node.PowerNets.size(); i++) {
	    //path_metal
	    int write = 0;
	    for (int j = 0; j < node.PowerNets[i].path_metal.size(); j++) {
		PnRDB::Metal metal = node.PowerNets[i].path_metal[j];
		if (addMetalBoundaries (jsonElements,  metal, drc_info, unitScale)) {
		    if (write == 0) {
			assignBoxPoints (x, y, metal.MetalRect.placedBox, unitScale);
			addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2,
					 stoi(drc_info.MaskID_Metal[drc_info.Metalmap[metal.MetalRect.metal]]),
					 node.PowerNets[i].name);
			write = 1; //added by yg 
		    }
		}
	    }
	    //path_via
	    for (int j = 0; j < node.PowerNets[i].path_via.size(); j++) 
		addViaBoundaries(jsonElements, node.PowerNets[i].path_via[j], drc_info, unitScale);
	}
    }

    if (includePowerGrid) {
	int vdd = 1; int gnd = 1;
	if (vdd == 1) {
	    for (int i = 0; i < node.Vdd.metals.size(); i++) 
		addMetalBoundaries (jsonElements, node.Vdd.metals[i], drc_info, unitScale);

	    for (int i = 0; i < node.Vdd.vias.size(); i++) 
		addViaBoundaries(jsonElements, node.Vdd.vias[i], drc_info, unitScale);
	}
	if (gnd == 1) {
	    for (int i = 0; i < node.Gnd.metals.size(); i++) 
		addMetalBoundaries (jsonElements, node.Gnd.metals[i], drc_info, unitScale);

	    for (int i = 0; i < node.Gnd.vias.size(); i++) 
		addViaBoundaries(jsonElements, node.Gnd.vias[i], drc_info, unitScale);
	}
    }

    if (includeBlock) {
	int bOrient;
   
        //for(int i = 0;i < node.Blocks.size(); i++){
        //    //int index=gdsMap2strBlock[node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile];
        //    for( int j=0;j<node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).interMetals.size();j++){
        //         addContactBoundaries(jsonElements, node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).interMetals[j], drc_info, unitScale);
        //       }
        //   }

	for (int i = 0; i < node.Blocks.size(); i++) {
	    int index=gdsMap2strBlock[node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile];

	    json sref;
	    sref["type"] = "sref";
	    sref["sname"] = strBlocks_Top[index].c_str();

	    switch (node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).orient) {
	    case PnRDB::N:   bOrient = 0; break;
	    case PnRDB::S:   bOrient = 1; break;
	    case PnRDB::E:   bOrient = 2; break;
	    case PnRDB::W:   bOrient = 3; break;
	    case PnRDB::FN:  bOrient = 4; break;
	    case PnRDB::FS:  bOrient = 5; break;
	    case PnRDB::FE:  bOrient = 6; break;
	    case PnRDB::FW:  bOrient = 7; break;
	    default: bOrient = 8;
	    }

	    PnRDB::bbox box = node.Blocks[i].instance.at(node.Blocks[i].selectedInstance ).placedBox;
	    switch (bOrient) {
	    case 0:
		sref["strans"] = 0;
		sref["angle"] = 0.0;
		x[0] = unitScale * box.LL.x;
		y[0] = unitScale * box.LL.y;
		break;
	    case 1:
		sref["strans"] = 0;
		sref["angle"] = 180.0;
		x[0] = unitScale * box.UR.x+llx[index];
		y[0] = unitScale * box.UR.y+lly[index];
		break;
	    case 2:
		sref["strans"] = 0;
		sref["angle"] = 90.0;
		x[0] = unitScale * box.UL.x-lly[index];
		y[0] = unitScale * box.UL.y+llx[index];
		break;
	    case 3:
		sref["strans"] = 0;
		sref["angle"] = 270.0;
		x[0] = unitScale * box.LR.x-lly[index];
		y[0] = unitScale * box.LR.y-llx[index];
		break;
	    case 4:
		sref["strans"] = 32768; // DAK: HACK
		sref["angle"] = 180.0;
		x[0] = unitScale * box.LR.x+llx[index];
		y[0] = unitScale * box.LR.y-lly[index];
		break;
	    case 5:
		sref["strans"] = 32768; // DAK: HACK
		sref["angle"] = 0.0;
		x[0] = unitScale * box.UL.x-llx[index];
		y[0] = unitScale * box.UL.y+lly[index];
		break;
	    case 6:
		sref["strans"] = 32768; // DAK: HACK
		sref["angle"] = 270.0;
		x[0] = unitScale * box.UR.x+lly[index];
		y[0] = unitScale * box.UR.x+llx[index]; 
		break;
	    case 7:
		sref["strans"] = 32768; // DAK: HACK
		sref["angle"] = 180.0;
		x[0] = unitScale * box.LL.x+lly[index];
		y[0] = unitScale * box.UL.y+llx[index]; 
		break;
	    default:
		sref["strans"] = 0; // DAK: HACK
		sref["angle"] = 0.0;
		x[0] = unitScale * box.LL.x;
		y[0] = unitScale * box.LL.y;
	    }
	    json xy = json::array();
	    for (size_t i = 0; i < 1; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    sref["xy"] = xy;
	    jsonElements.push_back (sref);
	}
    }

    addOABoundaries (jsonElements, unitScale * node.width, unitScale * node.height);
    jsonStr["elements"] = jsonElements;
    jsonStrAry.push_back (jsonStr);
    jsonLib["bgnstr"] = jsonStrAry;
  
    jsonLibAry.push_back(jsonLib);
    jsonTop["bgnlib"] = jsonLibAry;
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    std::cout << " JSON FINALIZE " <<  gdsName << std::endl;
    return node.gdsFile;
}

// std::string PnRdatabase::WriteGDS(PnRDB::hierNode& node, bool includeBlock, bool includeNet, bool includePowerNet, bool includePowerGrid, std::string gdsName, PnRDB::Drc_info& drc_info){
//   //begin to write GDS file from unit capacitor to final capacitor file
//   //inherit from another class !!!

//   //initial gw part

//   string topGDS_loc = gdsName+".gds";
//   node.gdsFile=topGDS_loc;
//   string TopCellName = gdsName;
//   node.gdsFile = topGDS_loc;
//   GdsParser::GdsWriter gw(topGDS_loc.c_str());
//   gw.create_lib("test", 0.00025, 2.5e-10);
//   int randnum = 111;
//   //what is this
//   vector<string> strBlocks;
//   std::map<string, int> gdsMap2strBlock;
//   std::set<string> uniGDSset;
//   vector<string> strBlocks_Top;
//   vector<int> llx, lly, urx, ury;
//   long int rndnum = static_cast<long int>(time(NULL));
//   //long int rndnum=1;
//   int idx=0;
//   //cout<<"start writing gds"<<endl;
//   if(includeBlock) {
//     for(int i=0;i<node.Blocks.size();i++){
//         uniGDSset.insert(node.Blocks[i].instance.gdsFile);
//         //cout<<node.Blocks[i].instance.gdsFile<<endl;
//     }
//     cout<<"start wrting sub-blocks"<<endl;
//     //int rndnum=111;
//     for(std::set<string>::iterator it=uniGDSset.begin();it!=uniGDSset.end();++it) {
//           GDSReaderWriterTxTFile_extension(*it, gw, rndnum, strBlocks, llx,lly,urx,ury);
//           strBlocks_Top.push_back(strBlocks.back());
//           gdsMap2strBlock.insert( std::make_pair(*it, idx) );
//           idx++;
//     }   
//   }
//   for(int i=0;i<(int)llx.size();i++) {
//     //cout<<"llx "<<llx[i]<<" lly "<<lly[i]<<" urx "<<urx[i]<<" ury "<<ury[i]<<endl;
//   }
//   int x[5], y[5];
//   gw.gds_write_bgnstr();
//   gw.gds_flush();
//   gw.gds_write_strname(TopCellName.c_str());
//   gw.gds_flush();
  
//   int write_blockPins_name = 0;
//   if(write_blockPins_name){
   
//     for(int i=0;i<node.blockPins.size();i++){
//          int write = 0;
//          for(int j=0;j<node.blockPins[i].pinContacts.size();j++){

//                  x[0]=node.blockPins[i].pinContacts[j].placedBox.LL.x;
//                  x[1]=node.blockPins[i].pinContacts[j].placedBox.UL.x;
//                  x[2]=node.blockPins[i].pinContacts[j].placedBox.UR.x;
//                  x[3]=node.blockPins[i].pinContacts[j].placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.blockPins[i].pinContacts[j].placedBox.LL.y;
//                  y[1]=node.blockPins[i].pinContacts[j].placedBox.UL.y;
//                  y[2]=node.blockPins[i].pinContacts[j].placedBox.UR.y;
//                  y[3]=node.blockPins[i].pinContacts[j].placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];

// //added by yg    
//                  if(write ==0){
//                  int test_layer=stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.blockPins[i].pinContacts[j].metal]]);
//                  int test_font=1,test_vp=1,test_hp=1;
//                  int test_texttype=251;//draw 0, label 2, pin 251, blockage 4
//                  double test_mag=0.03; 
//                  int center_x[1],center_y[1];
//                  string tmpstring;
//                  center_x[0] = (x[0]+x[2])/2;
//                  center_y[0] = (y[0]+y[2])/2;
//                  gw.gds_write_text( );
//                  gw.gds_write_layer( test_layer );
//                  gw.gds_write_texttype( test_texttype  );
//                  gw.gds_write_presentation( test_font,test_vp,test_hp );
//                  gw.gds_write_strans( false,false,false  );
//                  gw.gds_write_mag(test_mag);
//                  gw.gds_write_xy(center_x,center_y,1);
//                  gw.gds_write_string(node.blockPins[i].name.c_str());
//                  gw.gds_write_endel();
//                  gw.gds_flush();
// //added by yg 
//                  write = 1;
//                  }
            
//              }
        
//        }
    

//     }

//   if(includeNet){
//        //cout<<"start writing nets"<<endl;
//        //drc_info.MaskID_metal;
//        //drc_info.MaskID_via;

//        for(int i=0;i<node.Nets.size();i++){
//             //path_metal
//             int write = 1;
//             for(int j=0;j<node.Nets[i].path_metal.size();j++){
//                  x[0]=node.Nets[i].path_metal[j].MetalRect.placedBox.LL.x;
//                  x[1]=node.Nets[i].path_metal[j].MetalRect.placedBox.UL.x;
//                  x[2]=node.Nets[i].path_metal[j].MetalRect.placedBox.UR.x;
//                  x[3]=node.Nets[i].path_metal[j].MetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Nets[i].path_metal[j].MetalRect.placedBox.LL.y;
//                  y[1]=node.Nets[i].path_metal[j].MetalRect.placedBox.UL.y;
//                  y[2]=node.Nets[i].path_metal[j].MetalRect.placedBox.UR.y;
//                  y[3]=node.Nets[i].path_metal[j].MetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];

//                  if(node.Nets[i].path_metal[j].LinePoint[0].x==node.Nets[i].path_metal[j].LinePoint[1].x and node.Nets[i].path_metal[j].LinePoint[0].y==node.Nets[i].path_metal[j].LinePoint[1].y) {continue;}


// //added by yg    
//                  if(write ==0){
//                  int test_layer=stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Nets[i].path_metal[j].MetalRect.metal]]);
//                  int test_font=1,test_vp=1,test_hp=1;
//                  int test_texttype=251;//draw 0, label 2, pin 251, blockage 4
//                  double test_mag=0.03; 
//                  int center_x[1],center_y[1];
//                  string tmpstring;
//                  center_x[0] = (x[0]+x[2])/2;
//                  center_y[0] = (y[0]+y[2])/2;
//                  gw.gds_write_text( );
//                  gw.gds_write_layer( test_layer );
//                  gw.gds_write_texttype( test_texttype  );
//                  gw.gds_write_presentation( test_font,test_vp,test_hp );
//                  gw.gds_write_strans( false,false,false  );
//                  gw.gds_write_mag(test_mag);
//                  gw.gds_write_xy(center_x,center_y,1);
//                  gw.gds_write_string(node.Nets[i].name.c_str());
//                  gw.gds_write_endel();
//                  gw.gds_flush();
// //added by yg 
//                  write = 1;
//                  }

//                  gw.gds_write_boundary();
//                  gw.gds_flush();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[node.Nets[i].path_metal[j].MetalIdx]));
//                  gw.gds_flush();
//                  gw.gds_write_datatype(0);
//                  gw.gds_flush();
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_flush();
//                  gw.gds_write_endel();
//                  gw.gds_flush();
                 
                 
//                }
//             //path_via
//             for(int j=0;j<node.Nets[i].path_via.size();j++){
//                  //ViaRect
//                  x[0]=node.Nets[i].path_via[j].ViaRect.placedBox.LL.x;
//                  x[1]=node.Nets[i].path_via[j].ViaRect.placedBox.UL.x;
//                  x[2]=node.Nets[i].path_via[j].ViaRect.placedBox.UR.x;
//                  x[3]=node.Nets[i].path_via[j].ViaRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Nets[i].path_via[j].ViaRect.placedBox.LL.y;
//                  y[1]=node.Nets[i].path_via[j].ViaRect.placedBox.UL.y;
//                  y[2]=node.Nets[i].path_via[j].ViaRect.placedBox.UR.y;
//                  y[3]=node.Nets[i].path_via[j].ViaRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Via[drc_info.Viamap[node.Nets[i].path_via[j].ViaRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //LowerMetalRect
//                  x[0]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.LL.x;
//                  x[1]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.UL.x;
//                  x[2]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.UR.x;
//                  x[3]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.LL.y;
//                  y[1]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.UL.y;
//                  y[2]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.UR.y;
//                  y[3]=node.Nets[i].path_via[j].LowerMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Nets[i].path_via[j].LowerMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //UpperMetalRect
//                  x[0]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.LL.x;
//                  x[1]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.UL.x;
//                  x[2]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.UR.x;
//                  x[3]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.LL.y;
//                  y[1]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.UL.y;
//                  y[2]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.UR.y;
//                  y[3]=node.Nets[i].path_via[j].UpperMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Nets[i].path_via[j].UpperMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
               
//                }
//           }
//     }


//   labelTerminals(node, gw, drc_info); 

//   if(includePowerNet){
//        //cout<<"start writing nets"<<endl;
//        //drc_info.MaskID_metal;
//        //drc_info.MaskID_via;

//        for(int i=0;i<node.PowerNets.size();i++){
//             //path_metal
//             int write = 0;
//             for(int j=0;j<node.PowerNets[i].path_metal.size();j++){
//                  x[0]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.LL.x;
//                  x[1]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.UL.x;
//                  x[2]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.UR.x;
//                  x[3]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.LL.y;
//                  y[1]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.UL.y;
//                  y[2]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.UR.y;
//                  y[3]=node.PowerNets[i].path_metal[j].MetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];

//                  if(node.PowerNets[i].path_metal[j].LinePoint[0].x==node.PowerNets[i].path_metal[j].LinePoint[1].x and node.PowerNets[i].path_metal[j].LinePoint[0].y==node.PowerNets[i].path_metal[j].LinePoint[1].y) {continue;}

// //added by yg    
//                  if(write ==0){
//                  int test_layer=stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.PowerNets[i].path_metal[j].MetalRect.metal]]);
//                  int test_font=1,test_vp=1,test_hp=1;
//                  int test_texttype=251;//draw 0, label 2, pin 251, blockage 4
//                  double test_mag=0.03; 
//                  int center_x[1],center_y[1];
//                  string tmpstring;
//                  center_x[0] = (x[0]+x[2])/2;
//                  center_y[0] = (y[0]+y[2])/2;
//                  gw.gds_write_text( );
//                  gw.gds_write_layer( test_layer );
//                  gw.gds_write_texttype( test_texttype  );
//                  gw.gds_write_presentation( test_font,test_vp,test_hp );
//                  gw.gds_write_strans( false,false,false  );
//                  gw.gds_write_mag(test_mag);
//                  gw.gds_write_xy(center_x,center_y,1);
//                  gw.gds_write_string(node.PowerNets[i].name.c_str());
//                  gw.gds_write_endel();
//                  gw.gds_flush();
// //added by yg 
//                  write = 1;
//                  }
 
//                  gw.gds_write_boundary();
//                  gw.gds_flush();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[node.PowerNets[i].path_metal[j].MetalIdx]));
//                  gw.gds_flush();
//                  gw.gds_write_datatype(0);
//                  gw.gds_flush();
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_flush();
//                  gw.gds_write_endel();
//                  gw.gds_flush();
                 
                 
//                }
//             //path_via
//             for(int j=0;j<node.PowerNets[i].path_via.size();j++){
//                  //ViaRect
//                  x[0]=node.PowerNets[i].path_via[j].ViaRect.placedBox.LL.x;
//                  x[1]=node.PowerNets[i].path_via[j].ViaRect.placedBox.UL.x;
//                  x[2]=node.PowerNets[i].path_via[j].ViaRect.placedBox.UR.x;
//                  x[3]=node.PowerNets[i].path_via[j].ViaRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.PowerNets[i].path_via[j].ViaRect.placedBox.LL.y;
//                  y[1]=node.PowerNets[i].path_via[j].ViaRect.placedBox.UL.y;
//                  y[2]=node.PowerNets[i].path_via[j].ViaRect.placedBox.UR.y;
//                  y[3]=node.PowerNets[i].path_via[j].ViaRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Via[drc_info.Viamap[node.PowerNets[i].path_via[j].ViaRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //LowerMetalRect
//                  x[0]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.LL.x;
//                  x[1]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.UL.x;
//                  x[2]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.UR.x;
//                  x[3]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.LL.y;
//                  y[1]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.UL.y;
//                  y[2]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.UR.y;
//                  y[3]=node.PowerNets[i].path_via[j].LowerMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.PowerNets[i].path_via[j].LowerMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //UpperMetalRect
//                  x[0]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.LL.x;
//                  x[1]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.UL.x;
//                  x[2]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.UR.x;
//                  x[3]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.LL.y;
//                  y[1]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.UL.y;
//                  y[2]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.UR.y;
//                  y[3]=node.PowerNets[i].path_via[j].UpperMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.PowerNets[i].path_via[j].UpperMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
               
//                }
//           }
//     }

//   if(includePowerGrid){
//        //cout<<"start writing nets"<<endl;
//        //drc_info.MaskID_metal;
//        //drc_info.MaskID_via;
       
//        int vdd = 1;
//        int gnd = 1;
       
//        if(vdd==1){
          
//           for(int i=0;i<node.Vdd.metals.size();i++){

//                  x[0]=node.Vdd.metals[i].MetalRect.placedBox.LL.x;
//                  x[1]=node.Vdd.metals[i].MetalRect.placedBox.UL.x;
//                  x[2]=node.Vdd.metals[i].MetalRect.placedBox.UR.x;
//                  x[3]=node.Vdd.metals[i].MetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Vdd.metals[i].MetalRect.placedBox.LL.y;
//                  y[1]=node.Vdd.metals[i].MetalRect.placedBox.UL.y;
//                  y[2]=node.Vdd.metals[i].MetalRect.placedBox.UR.y;
//                  y[3]=node.Vdd.metals[i].MetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];

//                  if(node.Vdd.metals[i].LinePoint[0].x==node.Vdd.metals[i].LinePoint[1].x and node.Vdd.metals[i].LinePoint[0].y==node.Vdd.metals[i].LinePoint[1].y) {continue;}



//                  gw.gds_write_boundary();
//                  gw.gds_flush();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[node.Vdd.metals[i].MetalIdx]));
//                  gw.gds_flush();
//                  gw.gds_write_datatype(0);
//                  gw.gds_flush();
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_flush();
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//              }

//           for(int i=0;i<node.Vdd.vias.size();i++){

//                  //ViaRect
//                  x[0]=node.Vdd.vias[i].ViaRect.placedBox.LL.x;
//                  x[1]=node.Vdd.vias[i].ViaRect.placedBox.UL.x;
//                  x[2]=node.Vdd.vias[i].ViaRect.placedBox.UR.x;
//                  x[3]=node.Vdd.vias[i].ViaRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Vdd.vias[i].ViaRect.placedBox.LL.y;
//                  y[1]=node.Vdd.vias[i].ViaRect.placedBox.UL.y;
//                  y[2]=node.Vdd.vias[i].ViaRect.placedBox.UR.y;
//                  y[3]=node.Vdd.vias[i].ViaRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Via[drc_info.Viamap[node.Vdd.vias[i].ViaRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //LowerMetalRect
//                  x[0]=node.Vdd.vias[i].LowerMetalRect.placedBox.LL.x;
//                  x[1]=node.Vdd.vias[i].LowerMetalRect.placedBox.UL.x;
//                  x[2]=node.Vdd.vias[i].LowerMetalRect.placedBox.UR.x;
//                  x[3]=node.Vdd.vias[i].LowerMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Vdd.vias[i].LowerMetalRect.placedBox.LL.y;
//                  y[1]=node.Vdd.vias[i].LowerMetalRect.placedBox.UL.y;
//                  y[2]=node.Vdd.vias[i].LowerMetalRect.placedBox.UR.y;
//                  y[3]=node.Vdd.vias[i].LowerMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Vdd.vias[i].LowerMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //UpperMetalRect
//                  x[0]=node.Vdd.vias[i].UpperMetalRect.placedBox.LL.x;
//                  x[1]=node.Vdd.vias[i].UpperMetalRect.placedBox.UL.x;
//                  x[2]=node.Vdd.vias[i].UpperMetalRect.placedBox.UR.x;
//                  x[3]=node.Vdd.vias[i].UpperMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Vdd.vias[i].UpperMetalRect.placedBox.LL.y;
//                  y[1]=node.Vdd.vias[i].UpperMetalRect.placedBox.UL.y;
//                  y[2]=node.Vdd.vias[i].UpperMetalRect.placedBox.UR.y;
//                  y[3]=node.Vdd.vias[i].UpperMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Vdd.vias[i].UpperMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//              }

//          }

//        if(gnd==1){

//           for(int i=0;i<node.Gnd.metals.size();i++){

//                  x[0]=node.Gnd.metals[i].MetalRect.placedBox.LL.x;
//                  x[1]=node.Gnd.metals[i].MetalRect.placedBox.UL.x;
//                  x[2]=node.Gnd.metals[i].MetalRect.placedBox.UR.x;
//                  x[3]=node.Gnd.metals[i].MetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Gnd.metals[i].MetalRect.placedBox.LL.y;
//                  y[1]=node.Gnd.metals[i].MetalRect.placedBox.UL.y;
//                  y[2]=node.Gnd.metals[i].MetalRect.placedBox.UR.y;
//                  y[3]=node.Gnd.metals[i].MetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];

//                  if(node.Gnd.metals[i].LinePoint[0].x==node.Gnd.metals[i].LinePoint[1].x and node.Gnd.metals[i].LinePoint[0].y==node.Gnd.metals[i].LinePoint[1].y) {continue;}

//                  gw.gds_write_boundary();
//                  gw.gds_flush();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[node.Gnd.metals[i].MetalIdx]));
//                  gw.gds_flush();
//                  gw.gds_write_datatype(0);
//                  gw.gds_flush();
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_flush();
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//              }

//           for(int i=0;i<node.Gnd.vias.size();i++){

//                  //ViaRect
//                  x[0]=node.Gnd.vias[i].ViaRect.placedBox.LL.x;
//                  x[1]=node.Gnd.vias[i].ViaRect.placedBox.UL.x;
//                  x[2]=node.Gnd.vias[i].ViaRect.placedBox.UR.x;
//                  x[3]=node.Gnd.vias[i].ViaRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Gnd.vias[i].ViaRect.placedBox.LL.y;
//                  y[1]=node.Gnd.vias[i].ViaRect.placedBox.UL.y;
//                  y[2]=node.Gnd.vias[i].ViaRect.placedBox.UR.y;
//                  y[3]=node.Gnd.vias[i].ViaRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Via[drc_info.Viamap[node.Gnd.vias[i].ViaRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //LowerMetalRect
//                  x[0]=node.Gnd.vias[i].LowerMetalRect.placedBox.LL.x;
//                  x[1]=node.Gnd.vias[i].LowerMetalRect.placedBox.UL.x;
//                  x[2]=node.Gnd.vias[i].LowerMetalRect.placedBox.UR.x;
//                  x[3]=node.Gnd.vias[i].LowerMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Gnd.vias[i].LowerMetalRect.placedBox.LL.y;
//                  y[1]=node.Gnd.vias[i].LowerMetalRect.placedBox.UL.y;
//                  y[2]=node.Gnd.vias[i].LowerMetalRect.placedBox.UR.y;
//                  y[3]=node.Gnd.vias[i].LowerMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Gnd.vias[i].LowerMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//                  //UpperMetalRect
//                  x[0]=node.Gnd.vias[i].UpperMetalRect.placedBox.LL.x;
//                  x[1]=node.Gnd.vias[i].UpperMetalRect.placedBox.UL.x;
//                  x[2]=node.Gnd.vias[i].UpperMetalRect.placedBox.UR.x;
//                  x[3]=node.Gnd.vias[i].UpperMetalRect.placedBox.LR.x;
//                  x[4]=x[0];
                 
//                  y[0]=node.Gnd.vias[i].UpperMetalRect.placedBox.LL.y;
//                  y[1]=node.Gnd.vias[i].UpperMetalRect.placedBox.UL.y;
//                  y[2]=node.Gnd.vias[i].UpperMetalRect.placedBox.UR.y;
//                  y[3]=node.Gnd.vias[i].UpperMetalRect.placedBox.LR.y;
//                  y[4]=y[0];

//                  x[0]=2*x[0];
//                  x[1]=2*x[1];    
//                  x[2]=2*x[2];
//                  x[3]=2*x[3];
//                  x[4]=2*x[4];
            
//                  y[0]=2*y[0];
//                  y[1]=2*y[1];
//                  y[2]=2*y[2];
//                  y[3]=2*y[3];
//                  y[4]=2*y[4];
     
//                  gw.gds_write_boundary();
//                  gw.gds_write_layer(stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Gnd.vias[i].UpperMetalRect.metal]]));
//                  gw.gds_write_datatype(0);
//                  gw.gds_write_xy(x,y,5);
//                  gw.gds_write_endel();
//                  gw.gds_flush();
//              }

//          }
       
//     }


//   if(includeBlock){
//     //cout<<"start wrting sref"<<endl;
//     int bOrient;
//     for(int i=0;i<node.Blocks.size();i++){
//          int index=gdsMap2strBlock[node.Blocks[i].instance.gdsFile];
//          //cout<<"block index "<<index<<endl;
//          gw.gds_write_sref();
//          gw.gds_write_sname(strBlocks_Top[index].c_str());
//          gw.gds_flush();

//          if(node.Blocks[i].instance.orient==PnRDB::N) { bOrient=0;
//            }else if(node.Blocks[i].instance.orient==PnRDB::S) {bOrient=1;
//            }else if(node.Blocks[i].instance.orient==PnRDB::E) {bOrient=2;
//            } else if(node.Blocks[i].instance.orient==PnRDB::W) {bOrient=3;
//            } else if(node.Blocks[i].instance.orient==PnRDB::FN) {bOrient=4;
//            } else if(node.Blocks[i].instance.orient==PnRDB::FS) {bOrient=5;
//            } else if(node.Blocks[i].instance.orient==PnRDB::FE) {bOrient=6;
//            } else if(node.Blocks[i].instance.orient==PnRDB::FW) {bOrient=7;
//            } else { bOrient=8; }
//          //cout<<bOrient<<endl;
//          switch(bOrient){
//                    case 0: gw.gds_write_strans(false,false,false);
//                            gw.gds_write_angle(0);//N 
//                            gw.gds_flush();
//                            x[0]=2*node.Blocks[i].instance.placedBox.LL.x;
//                            y[0]=2*node.Blocks[i].instance.placedBox.LL.y;
//                    break;
//                    case 1: gw.gds_write_strans(false,false,false);
//                            gw.gds_write_angle(180);//S 
//                            gw.gds_flush();
//                            x[0]=2*node.Blocks[i].instance.placedBox.UR.x+llx[index];
//                            y[0]=2*node.Blocks[i].instance.placedBox.UR.y+lly[index];
//                            break;
//                    case 2: gw.gds_write_strans(false,false,false);
//                            gw.gds_write_angle(90);//E 
//                            gw.gds_flush();
//                            x[0]=2*node.Blocks[i].instance.placedBox.UL.x-lly[index];
//                            y[0]=2*node.Blocks[i].instance.placedBox.UL.y+llx[index];
//                            break;
//                    case 3: gw.gds_write_strans(false,false,false);
//                            gw.gds_write_angle(270);//W 
//                            gw.gds_flush();
//                            x[0]=2*node.Blocks[i].instance.placedBox.LR.x-lly[index];
//                            y[0]=2*node.Blocks[i].instance.placedBox.LR.y-llx[index];
//                            break;
//                    case 4: gw.gds_write_strans(true,false,false);
//                            gw.gds_write_angle( 180 );//FN
//                            gw.gds_flush(  );
//                            x[0]=2*node.Blocks[i].instance.placedBox.LR.x+llx[index];
//                            y[0]=2*node.Blocks[i].instance.placedBox.LR.y-lly[index];
//                            break;
//                    case 5: gw.gds_write_strans(true,false,false);
//                            gw.gds_write_angle(   0 );//FS
//                            gw.gds_flush(  );
//                            x[0]=2*node.Blocks[i].instance.placedBox.UL.x-llx[index];
//                            y[0]=2*node.Blocks[i].instance.placedBox.UL.y+lly[index];
//                            break;
//                    case 6: gw.gds_write_strans(true,false,false);
//                            gw.gds_write_angle( 270 );//FE
//                            gw.gds_flush(  );
//                            x[0]=2*node.Blocks[i].instance.placedBox.UR.x+lly[index];
//                            y[0]=2*node.Blocks[i].instance.placedBox.UR.x+llx[index]; 
//                            break;
//                    case 7: gw.gds_write_strans(true,false,false);
//                            gw.gds_write_angle(  180);//FW
//                            gw.gds_flush(  );
//                            x[0]=2*node.Blocks[i].instance.placedBox.LL.x+lly[index];
//                            y[0]=2*node.Blocks[i].instance.placedBox.UL.y+llx[index]; 
//                            break;
//                    default: gw.gds_write_strans(false,false,false);
//                             gw.gds_write_angle(0) ;
//                             gw.gds_flush();
//                             x[0]=2*node.Blocks[i].instance.placedBox.LL.x;
//                             y[0]=2*node.Blocks[i].instance.placedBox.LL.y;
// 	 }
//          gw.gds_write_xy(x,y,1);
//          gw.gds_write_endel();
//          gw.gds_flush();
//        }
//     }
//   gw.gds_write_endstr();
//   gw.gds_write_endlib();
//   gw.gds_flush();
//   return topGDS_loc;
// }

// void PnRdatabase::labelTerminals(PnRDB::hierNode& node, GdsParser::GdsWriter& gw, PnRDB::Drc_info& drc_info)
// {

//   cout<<"Top: "<<node.isTop<<endl;
//   cout<<"#terminals print"<<endl;
//   cout<<"#size: "<<node.Terminals.size()<<endl;
//   for(int i=0;i<node.Terminals.size();i++){
// 	 cout<<"#name: "<<node.Terminals[i].name<<endl; 
//      cout<<"#type: "<<node.Terminals[i].type<<endl; 
//      cout<<"#netIter: "<<node.Terminals[i].netIter<<endl; 
//      cout<<"#termContact size: "<<node.Terminals[i].termContacts.size()<<endl;
//      for(int j=0;j<node.Terminals[i].termContacts.size();j++){
//         cout<<"#contact-metal: "<<node.Terminals[i].termContacts[j].metal<<endl;
//         cout<<"#contact-placedCenter(x,y): "<<node.Terminals[i].termContacts[j].placedCenter.x<<" "
//         <<node.Terminals[i].termContacts[j].placedCenter.y<<endl;
//      }
//   }
//   int test_layer;//
//   int test_font=1,test_vp=1,test_hp=1;
//   int test_texttype=251;//pin purpose
//   double test_mag=0.03; 
//   int center_x[1],center_y[1];
//   string tmpstring;
//   if(node.isTop==1){
//     for(int i=0;i<node.Terminals.size();i++){
//        gw.gds_write_text(  );
//        int write = 0;
//        for(int j=0;j<node.Terminals[i].termContacts.size();j++){
           
// 		  //if(node.Terminals[i].termContacts[j].metal.compare(NULL)==0){
// 		  if(!node.Terminals[i].termContacts[j].metal.empty()){
//             tmpstring=node.Terminals[i].termContacts[j].metal;
// 			cout<<"#test metal string: "<<tmpstring<<endl;
// 		  }
//           if(write ==0){
//           test_layer = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[node.Terminals[i].termContacts[j].metal]]);
//   	    //cout<<"#test print:"<<node.Terminals[i].termContacts[j].placedCenter.x<<endl;
//   	    //cout<<"#test print:"<<node.Terminals[i].termContacts[j].placedCenter.y<<endl;
//           center_x[0]=2*node.Terminals[i].termContacts[j].placedCenter.x;
//           center_y[0]=2*node.Terminals[i].termContacts[j].placedCenter.y;
//         //cout<<"#test print:"<<tmp_x[j]<<" "<<tmp_y[j]<<endl;
//           gw.gds_write_layer( test_layer );
//           gw.gds_write_texttype( test_texttype  );
//           gw.gds_write_presentation( test_font,test_vp,test_hp );
//           gw.gds_write_strans( false,false,false  );
//           gw.gds_write_mag(test_mag);
//   	   //center_x[0]=2*(tmp_x[0]+tmp_x[1])/2;
//   	   //center_y[0]=2*(tmp_y[0]+tmp_y[1])/2;
//   	   //center_x[0]=tmp_x[j];
//   	   //center_y[0]=tmp_y[j];
//           cout<<"#test print center:"<<center_x[0]<<" "<<center_y[0]<<endl;
//           gw.gds_write_xy(center_x,center_y,1);
//           gw.gds_write_string(node.Terminals[i].name.c_str());
//           gw.gds_write_endel();
//           gw.gds_flush();
//           write = 1;
//            }
// 	   }
// 	}
//   }
// }


void PnRdatabase::PrintHierNode(PnRDB::hierNode& node) {
  std::cout<<"Hier Node Printing"<<std::endl;
  std::cout<<"Name: "<<node.name<<" ; isTop: "<<node.isTop<<" ; isCompeted: "<<node.isCompleted<<" ; width: "<<node.width<<" ; height: "<<node.height<<" ; gdsFile: "<<node.gdsFile<<" ; parent: ";
  for(vector<int>::iterator it=node.parent.begin(); it!=node.parent.end(); it++) {
    std::cout<<*it;
  }
  std::cout<<std::endl<<"Blocks"<<std::endl;
  for(vector<PnRDB::blockComplex>::iterator it=node.Blocks.begin(); it!=node.Blocks.end(); ++it) {
    PrintBlock(*it);
  }
  std::cout<<std::endl<<"Nets"<<std::endl;
  for(vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
    PrintNet(*it);
  }
  std::cout<<std::endl<<"Terminals"<<std::endl;
  for(vector<PnRDB::terminal>::iterator it=node.Terminals.begin(); it!=node.Terminals.end(); ++it) {
    PrintTerminal(*it);
  }
  std::cout<<std::endl<<"Node blockpins"<<std::endl;
  for(vector<PnRDB::pin>::iterator it=node.blockPins.begin(); it!=node.blockPins.end(); ++it) {
    PrintBlockPin(*it);
  }
  std::cout<<std::endl<<"Node internal metals"<<std::endl;
  for(vector<PnRDB::contact>::iterator it=node.interMetals.begin(); it!=node.interMetals.end(); ++it) {
    PrintContact(*it);
  }
  std::cout<<std::endl<<"Node internal vias"<<std::endl;
  for(vector<PnRDB::Via>::iterator it=node.interVias.begin(); it!=node.interVias.end(); ++it) {
    PrintVia(*it);
  }
  std::cout<<std::endl<<"Node symmetry nets"<<std::endl;
  for(std::vector<PnRDB::SymmNet>::iterator it=node.SNets.begin(); it!=node.SNets.end(); ++it) {
    PrintSymmNet(*it);
  }
}

void PnRdatabase::PrintSymmNet(PnRDB::SymmNet& t) {
  std::cout<<"@Symmetry net"<<std::endl;
  std::cout<<" net1:"<<t.net1.name<<" ; iter: "<<t.iter1<<std::endl;
  for(std::vector<PnRDB::connectNode>::iterator it=t.net1.connected.begin(); it!=t.net1.connected.end(); ++it) {
    std::cout<<" {"<<it->type<<":"<<it->iter<<","<<it->iter2<<"}";
  }
  std::cout<<endl;
  std::cout<<" net2:"<<t.net2.name<<" ; iter: "<<t.iter2<<std::endl;
  for(std::vector<PnRDB::connectNode>::iterator it=t.net2.connected.begin(); it!=t.net2.connected.end(); ++it) {
    std::cout<<" {"<<it->type<<":"<<it->iter<<","<<it->iter2<<"}";
  }
  std::cout<<endl;
}

void PnRdatabase::PrintTerminal(PnRDB::terminal& t) {
  std::cout<<"@Terminal"<<std::endl;
  std::cout<<" name: "<<t.name<<" ; type: "<<t.type<<" ; netiter: "<<t.netIter<<std::endl;
  for(vector<PnRDB::contact>::iterator it=t.termContacts.begin(); it!=t.termContacts.end(); ++it) {
    PrintContact(*it);
  }
}


void PnRdatabase::PrintNet(PnRDB::net& n) {
  std::cout<<"@Net"<<std::endl;
  std::cout<<"name: "<<n.name<<" ; shielding: "<<n.shielding<<" ; sin2Terminal: "<<n.sink2Terminal<<" ; degree: "<<n.degree<<" ; symCounterpart: "<<n.symCounterpart<<" ; iter2SNetLsit: "<<n.iter2SNetLsit<<" ; priority: "<<n.priority<<" ; symmetry axis direction:"<<n.axis_dir<<" ; symmetry axis coor: "<<n.axis_coor<<std::endl;
  std::cout<<"connected ";
  for(vector<PnRDB::connectNode>::iterator it=n.connected.begin(); it!=n.connected.end(); ++it) {
    std::cout<<" {"<<it->type<<","<<it->iter<<","<<it->iter2<<"} ";
  }
  std::cout<<std::endl;
  for(vector<PnRDB::Metal>::iterator it=n.path_metal.begin(); it!=n.path_metal.end(); ++it) {
    PrintMetal(*it);
  }
  for(vector<PnRDB::Via>::iterator it=n.path_via.begin(); it!=n.path_via.end(); ++it) {
    PrintVia(*it);
  }
}

void PnRdatabase::PrintBlock(PnRDB::blockComplex& bc) {
  PnRDB::blockComplex *it=&bc;
  std::cout<<"@Block"<<std::endl;
    std::cout<<"Child: "<<it->child<<" ; instNum: "<<it->instNum<<" ; selectedInstance: "<<it->selectedInstance<<std::endl;
    for(int w=0;w<bc.instance.size();++w) {
    std::cout<<"Choice "<<w<<" -> name: "<<it->instance.at(w).name<<" ; master: "<<it->instance.at(w).master<<" ; type: "<<it->instance.at(w).type<<" ; width: "<<it->instance.at(w).width<<" ; height: "<<it->instance.at(w).height<<" ; isLeaf: "<<it->instance.at(w).isLeaf<<" ; gds: "<<it->instance.at(w).gdsFile<<" ; orient: "<<it->instance.at(w).orient<<" ; originCenter: {"<<it->instance.at(w).originCenter.x<<","<<it->instance.at(w).originCenter.y<<"}; placedCenter: {"<<it->instance.at(w).placedCenter.x<<","<<it->instance.at(w).placedCenter.y<<"}"<<std::endl;
    std::cout<<"originBox: LL"<<it->instance.at(w).originBox.LL.x<<","<<it->instance.at(w).originBox.LL.y<<" LR"<<it->instance.at(w).originBox.LR.x<<","<<it->instance.at(w).originBox.LR.y<<" UR"<<it->instance.at(w).originBox.UR.x<<","<<it->instance.at(w).originBox.UR.y<<" UL"<<it->instance.at(w).originBox.UL.x<<","<<it->instance.at(w).originBox.UL.y<<" poly ";
    for(vector<PnRDB::point>::iterator it2=it->instance.at(w).originBox.polygon.begin(); it2!=it->instance.at(w).originBox.polygon.end(); ++it2) {
      std::cout<<"{"<<it2->x<<","<<it2->y<<"} ";
    }
    std::cout<<std::endl;
    std::cout<<"placedBox: LL"<<it->instance.at(w).placedBox.LL.x<<","<<it->instance.at(w).placedBox.LL.y<<" LR"<<it->instance.at(w).placedBox.LR.x<<","<<it->instance.at(w).placedBox.LR.y<<" UR"<<it->instance.at(w).placedBox.UR.x<<","<<it->instance.at(w).placedBox.UR.y<<" UL"<<it->instance.at(w).placedBox.UL.x<<","<<it->instance.at(w).placedBox.UL.y<<" poly ";
    for(vector<PnRDB::point>::iterator it2=it->instance.at(w).placedBox.polygon.begin(); it2!=it->instance.at(w).placedBox.polygon.end(); ++it2) {
      std::cout<<"{"<<it2->x<<","<<it2->y<<"} ";
    }
    std::cout<<std::endl;
    std::cout<<"Blockpins"<<std::endl;
    for(vector<PnRDB::pin>::iterator it2=it->instance.at(w).blockPins.begin(); it2!=it->instance.at(w).blockPins.end(); it2++) {
      std::cout<<"name: "<<it2->name<<" ; type: "<<it2->type<<" ; use: "<<it2->use<<" ; netIter: "<<it2->netIter<<std::endl;
      std::cout<<"pinContact "<<std::endl;
      for(vector<PnRDB::contact>::iterator it3=it2->pinContacts.begin(); it3!=it2->pinContacts.end(); ++it3) {
        PrintContact(*it3);
      }
      for(vector<PnRDB::Via>::iterator it3=it2->pinVias.begin(); it3!=it2->pinVias.end(); ++it3) {
        PrintVia(*it3);
      }
    }
    std::cout<<"Internal Metals"<<std::endl;
    for(vector<PnRDB::contact>::iterator it2=it->instance.at(w).interMetals.begin(); it2!=it->instance.at(w).interMetals.end(); it2++) {
      PrintContact(*it2);
    }
    std::cout<<"Internal Vias"<<std::endl;
    for(vector<PnRDB::Via>::iterator it2=it->instance.at(w).interVias.begin(); it2!=it->instance.at(w).interVias.end(); it2++) {
      PrintVia(*it2);
    }
    }
}

void PnRdatabase::PrintBlockPin(PnRDB::pin& p) {
      PnRDB::pin *it2=&p;
      std::cout<<"@Blockpin"<<std::endl;
      std::cout<<"name: "<<it2->name<<" ; type: "<<it2->type<<" ; use: "<<it2->use<<" ; netIter: "<<it2->netIter<<std::endl;
      std::cout<<"pinContact "<<std::endl;
      for(vector<PnRDB::contact>::iterator it3=it2->pinContacts.begin(); it3!=it2->pinContacts.end(); ++it3) {
        PrintContact(*it3);
      }
      for(vector<PnRDB::Via>::iterator it3=it2->pinVias.begin(); it3!=it2->pinVias.end(); ++it3) {
        PrintVia(*it3);
      }
}

void PnRdatabase::PrintMetal(PnRDB::Metal& m) {
  std::cout<<"@Metal index: "<<m.MetalIdx<<" ; wdith:"<<m.width<<std::endl;
  for(vector<PnRDB::point>::iterator it=m.LinePoint.begin(); it!=m.LinePoint.end(); ++it) {
    std::cout<<" {"<<it->x<<","<<it->y<<"} ";
  }
  std::cout<<std::endl;
  PrintContact(m.MetalRect);
}

void PnRdatabase::PrintVia(PnRDB::Via& v) {
  std::cout<<"@Via ";
  std::cout<<" model:"<<v.model_index<<" ; originpos: {"<<v.originpos.x<<","<<v.originpos.y<<"}; placedpos: {"<<v.placedpos.x<<","<<v.placedpos.y<<"}"<<std::endl;
  PrintContact(v.UpperMetalRect);
  PrintContact(v.LowerMetalRect);
  PrintContact(v.ViaRect);
}

void PnRdatabase::PrintContact(PnRDB::contact& cont) {
        std::cout<<"@Contact ";
        PnRDB::contact *it3=&cont;
        std::cout<<" metal: "<<it3->metal<<" ; originCenter: {"<<it3->originCenter.x<<","<<it3->originCenter.y<<"} ; placedCenter: {"<<it3->placedCenter.x<<","<<it3->placedCenter.y<<"}"<<std::endl;
        std::cout<<"originBox: LL"<<it3->originBox.LL.x<<","<<it3->originBox.LL.y<<" LR"<<it3->originBox.LR.x<<","<<it3->originBox.LR.y<<" UR"<<it3->originBox.UR.x<<","<<it3->originBox.UR.y<<" UL"<<it3->originBox.UL.x<<","<<it3->originBox.UL.y<<" poly ";
        for(vector<PnRDB::point>::iterator it4=it3->originBox.polygon.begin(); it4!=it3->originBox.polygon.end(); ++it4) {
          std::cout<<"{"<<it4->x<<","<<it4->y<<"} ";
        }
        std::cout<<std::endl;
        std::cout<<"placedBox: LL"<<it3->placedBox.LL.x<<","<<it3->placedBox.LL.y<<" LR"<<it3->placedBox.LR.x<<","<<it3->placedBox.LR.y<<" UR"<<it3->placedBox.UR.x<<","<<it3->placedBox.UR.y<<" UL"<<it3->placedBox.UL.x<<","<<it3->placedBox.UL.y<<" poly ";
        for(vector<PnRDB::point>::iterator it4=it3->placedBox.polygon.begin(); it4!=it3->placedBox.polygon.end(); ++it4) {
          std::cout<<"{"<<it4->x<<","<<it4->y<<"} ";
        }
        std::cout<<std::endl;
}
// Local Variables:
// c-basic-offset: 4
// End:

std::map<string, PnRDB::lefMacro> PnRdatabase::checkoutSingleLEF() {
  std::map<string, PnRDB::lefMacro> mm;
  for(std::map<string, std::vector<PnRDB::lefMacro> >::iterator it=this->lefData.begin(); it!=this->lefData.end(); ++it) {
    mm[it->first]=it->second.back();
  }
  return mm;
}
