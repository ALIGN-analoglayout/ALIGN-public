#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <time.h>

using namespace nlohmann;

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

void PnRdatabase::ReadPDKJSON(std::string drfile) {
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
        for(unsigned int i=0;i<DRC_info.Metal_info.size();i++){
             DRC_info.metal_weight.push_back(1);
        }
        // 4. Add Via model
        for(unsigned int i=0;i<DRC_info.Via_info.size();i++){
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
        for(unsigned int i=0;i<(int)DRC_info.Metal_info.size();++i) {
          DRC_info.MaskID_Metal.push_back(std::to_string( DRC_info.Metal_info.at(i).layerNo ));
        }
        for(unsigned int i=0;i<(int)DRC_info.Via_info.size();++i) {
          DRC_info.MaskID_Via.push_back(std::to_string( DRC_info.Via_info.at(i).layerNo ));
        }
    }
}

void PnRdatabase::ReadDesignRule_jason(string drfile){

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
