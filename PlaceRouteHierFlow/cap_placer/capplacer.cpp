#include "capplacer.h"
#include <iomanip>
#include <nlohmann/json.hpp>

using namespace std;
using namespace nlohmann;

// These are in PnRDB
extern unsigned short JSON_Presentation (int font, int vp, int hp);
extern unsigned short JSON_STrans (bool reflect, bool abs_angle, bool abs_mag);
extern json JSON_TimeTime ();

Placer_Router_Cap::Placer_Router_Cap(){
  unit_cap_demension.first = 4428;
  unit_cap_demension.second = 4428;
  span_distance.first = 25;
  span_distance.second = 1000;
  offset_x = 0;
  offset_y = 0;
}

Placer_Router_Cap::Placer_Router_Cap(string opath, string fpath, PnRDB::hierNode & current_node, PnRDB::Drc_info &drc_info, map<string, PnRDB::lefMacro> &lefData, bool dummy_flag, bool aspect_ratio, int num_aspect){
  cout<<"Enter"<<endl;
  Common_centroid_capacitor_aspect_ratio(opath, fpath, current_node, drc_info, lefData, dummy_flag, aspect_ratio, num_aspect);
  cout<<"Out"<<endl;
}

void Placer_Router_Cap::Placer_Router_Cap_clean(){

  std::cout<<"Enter clean 1"<<std::endl;

  PnRDB::block temp_block;
  temp_block.blockPins.clear(); temp_block.interMetals.clear(); temp_block.interVias.clear(); temp_block.dummy_power_pin.clear();
  std::cout<<"Enter clean 2"<<std::endl;
  CheckOutBlock = temp_block;

  std::cout<<"Enter clean 3"<<std::endl;
  metal_width.clear();

  std::cout<<"Enter clean 4"<<std::endl;
  metal_direct.clear();

  std::cout<<"Enter clean 5"<<std::endl;
  metal_distance_ss.clear();

  std::cout<<"Enter clean 6"<<std::endl;
  via_width_x.clear();

  std::cout<<"Enter clean 7"<<std::endl;
  via_width_y.clear();

  std::cout<<"Enter clean 8"<<std::endl;
  via_cover_l.clear();

  std::cout<<"Enter clean 9"<<std::endl;
  via_cover_u.clear();

  std::cout<<"Enter clean 10"<<std::endl;
  Caps.clear();

  std::cout<<"Enter clean 11"<<std::endl;
  cap_pair_sequence.clear();

  std::cout<<"Enter clean 12"<<std::endl;
  net_sequence.clear();

  std::cout<<"Enter clean 13"<<std::endl;
  num_router_net_v.clear();

  std::cout<<"Enter clean 14"<<std::endl;
  num_router_net_h.clear();

  std::cout<<"Enter clean 15"<<std::endl;

  vector<net> temp_net;

  std::cout<<"Enter clean 16"<<std::endl;

  Nets_pos = temp_net;
  
  //this->Nets_pos.clear();

  std::cout<<"Enter clean 17"<<std::endl;
  Nets_neg = temp_net;

  

}




void Placer_Router_Cap::Placer_Router_Cap_function(vector<int> & ki, vector<pair<string, string> > &cap_pin, string fpath, string unit_capacitor, string final_gds, bool cap_ratio, int cap_r, int cap_s, PnRDB::Drc_info drc_info, map<string, PnRDB::lefMacro> lefData, bool dummy_flag, string opath){

//dummy_flag is 1, dummy capacitor is added; Else, dummy capacitor do not exist.
//not added, needed to be added 

//initial DRC router

  //from lef file readin cap demension
  
  cout<<"step1"<<endl;
  string H_metal;
  int H_metal_index=-1;
  string V_metal;
  int V_metal_index=-1;

  string HV_via_metal;
  int HV_via_metal_index;

  vector<string> obs;

  if(lefData.find(unit_capacitor)==lefData.end()){
  cerr<<"CCCap-Error: unit capacitor not exist in map:"<<" "<<unit_capacitor<<endl;
  }else{

  
  for(int i=0;i<lefData[unit_capacitor].interMetals.size();i++){
       int found = 0;
       for(int j=0;j<obs.size();j++){
          if(obs[j]==lefData[unit_capacitor].interMetals[i].metal){
             found = 1;
            }
         }
       if(found == 0){obs.push_back(lefData[unit_capacitor].interMetals[i].metal);}
      }

  unit_cap_demension.first = lefData[unit_capacitor].width;
  unit_cap_demension.second= lefData[unit_capacitor].height;
  int pin_minx = INT_MAX;
  int pin_miny = INT_MAX;
  string pin_metal;
  for(int i=0;i<lefData[unit_capacitor].macroPins.size();i++){
       for(int j=0;j<lefData[unit_capacitor].macroPins[i].pinContacts.size();j++){
           if(lefData[unit_capacitor].macroPins[i].pinContacts[j].originBox.LL.x<=pin_minx and lefData[unit_capacitor].macroPins[i].pinContacts[j].originBox.LL.y<=pin_miny){
               pin_minx = lefData[unit_capacitor].macroPins[i].pinContacts[j].originBox.LL.x;
               pin_miny = lefData[unit_capacitor].macroPins[i].pinContacts[j].originBox.LL.y;
               pin_metal = lefData[unit_capacitor].macroPins[i].pinContacts[j].metal;
              }
          }
     }
	  
   //determine which three layer are used for routing metal
	  
   if(drc_info.Metal_info[drc_info.Metalmap[pin_metal]].direct == 1){ // metal pin is H
         H_metal = pin_metal;
         H_metal_index = drc_info.Metalmap[pin_metal];
       if(drc_info.Metalmap[pin_metal]>0){ // metal pin has metal - 1 and
           V_metal = drc_info.Metal_info[drc_info.Metalmap[pin_metal]-1].name;
           V_metal_index = drc_info.Metalmap[pin_metal]-1;
         }else{
           V_metal = drc_info.Metal_info[drc_info.Metalmap[pin_metal]+1].name;
           V_metal_index = drc_info.Metalmap[pin_metal]-1;
         }
       
     }else{
         V_metal = pin_metal;
         V_metal_index = drc_info.Metalmap[pin_metal];
       if(drc_info.Metalmap[pin_metal]>0){ // metal pin has metal - 1 and
           H_metal = drc_info.Metal_info[drc_info.Metalmap[pin_metal]-1].name;
           H_metal_index = drc_info.Metalmap[pin_metal]-1;
         }else{
           H_metal = drc_info.Metal_info[drc_info.Metalmap[pin_metal]+1].name;
           H_metal_index = drc_info.Metalmap[pin_metal]+1;
         }
     }
	  
  if(H_metal_index>V_metal_index){
      HV_via_metal = V_metal;
      HV_via_metal_index = V_metal_index;
    }else{
      HV_via_metal = H_metal;
      HV_via_metal_index = H_metal_index;
    }

   shifting_x = pin_minx-drc_info.Via_model[drc_info.Metalmap[HV_via_metal]].LowerRect[0].x;
   shifting_y = pin_miny-drc_info.Via_model[drc_info.Metalmap[HV_via_metal]].LowerRect[0].y;
   //cout<<"pin_minx "<<pin_minx<<" pin_miny "<<pin_miny<<endl;
   //cout<<"pin_miny "<<pin_miny<<endl;
   //cout<<"rec x "<<drc_info.Via_model[drc_info.Metalmap[HV_via_metal]].LowerRect[0].x<<" rec y "<<drc_info.Via_model[drc_info.Metalmap[HV_via_metal]].LowerRect[0].y<<endl;
   //cout<<"shifting_x "<<shifting_x<<" shifting_y "<<shifting_y<<endl;
   //cout<<"shifting_y "<<shifting_y<<endl;
	  
  }

  cout<<"step2"<<endl;

  offset_x = 0;
  offset_y = 0;
  
  for(int i=0;i<drc_info.Metal_info.size();i++){
      metal_width.push_back(drc_info.Metal_info[i].width); //change 
      metal_width[i] = metal_width[i] / 2;
      metal_distance_ss.push_back(drc_info.Metal_info[i].dist_ss); //change //72
      metal_distance_ss[i] = metal_distance_ss[i]/2;
      metal_direct.push_back(drc_info.Metal_info[i].direct);
  }

  cout<<"step2.1"<<endl;
/*
  for(int i=0;i<drc_info.Via_info.size();i++){
      via_width_x.push_back(drc_info.Via_info[i].width);
      via_width_x[i]=via_width_x[i]/2;
      via_width_y.push_back(drc_info.Via_info[i].width_y);
      via_width_y[i]=via_width_y[i]/2;
      via_cover_l.push_back(drc_info.Via_info[i].cover_l); //change
      via_cover_l[i]=via_cover_l[i]/2;
      via_cover_u.push_back(drc_info.Via_info[i].cover_u); //change
      via_cover_u[i]=via_cover_u[i]/2;
  }
*/
//initial demension

  //min_dis = 2*metal_width[0]+metal_distance_ss[0];

  min_dis_x = drc_info.Metal_info[V_metal_index].width+drc_info.Metal_info[V_metal_index].dist_ss;
  min_dis_y = drc_info.Metal_info[H_metal_index].width+drc_info.Metal_info[H_metal_index].dist_ss;

  //need two min_dis?? min_dis_x, min_di

//readin cap scale from lef file

  //this is from gds
/*
  string gds_unit_capacitor = fpath+"/"+unit_capacitor+".gds";
  vector<string> strBlocks;
  vector<int> llx, lly, urx, ury;
  long int rndnum=111;
  json js;
  JSONReaderWrite_subcells (gds_unit_capacitor, rndnum, strBlocks, llx,lly,urx,ury, js);
  unit_cap_demension.first = llx[0];
  unit_cap_demension.second = lly[0];
*/
  

  cout<<"step2.2"<<endl;
  span_distance.first = min_dis_x;
  span_distance.second = 3*min_dis_y; //m1 distance
  cout<<span_distance.first<<endl;

//initial cap information
  int net_size = ki.size();
  double sum = 0;
  double r;
  double s;
  for(int i=0;i<net_size;i++){
     sum = sum + ki[i];
    }
   r = ceil(sqrt(sum));
   s = ceil(sum/r);

  if(cap_ratio==1){ //cap_ratio = 1, pass the ratio by user otherwise calculate it by the code
    r = cap_r;
    s = cap_s;
    }    

//for dummy caps
   if(dummy_flag){
   r= r+2;
   s= s+2;
   }

  cout<<"step2.3"<<endl;
  for(int i=0;i<(int) r;i++){
     for(int j=0;j<(int) s;j++){
         cap temp_cap;
         temp_cap.index_x=(double) i;
         temp_cap.index_y=(double) j;
         temp_cap.x=unit_cap_demension.first/2 +  i* (unit_cap_demension.first+span_distance.first);
         temp_cap.y=unit_cap_demension.second/2 +  j* (unit_cap_demension.second+span_distance.second);
         temp_cap.net_index = -1;
         temp_cap.access = 0;
         Caps.push_back(temp_cap);
       }
    }
  

  cout<<"step2.4"<<endl;
//initial cap_pair_sequence
  double Cx = (r-1)/2;
  double Cy = (s-1)/2;
  vector<double> dis;
  vector<int> index;
  double distance;
  for(int i=0;i<Caps.size();i++){
        distance = sqrt((Caps[i].index_x-Cx)*(Caps[i].index_x-Cx)+(Caps[i].index_y-Cy)*(Caps[i].index_y-Cy));
        dis.push_back(distance);
        index.push_back(i);
    }
  //sort the distance
  int temp_index;
  double temp_dis;
  for(int i=0;i<(int)dis.size();i++){
     for(int j=i+1;j<(int) dis.size();j++){
        if(dis[index[i]]>dis[index[j]]){
           temp_index = index[i];
           index[i]=index[j];
           index[j]=temp_index;
          }
        }
     }
  cout<<"step2.5"<<endl;
  //generate the cap pair sequence
  pair<int,int> temp_pair;

  if(index.size()==1){
      temp_pair.first = index[0];
      temp_pair.second = -1;
      cap_pair_sequence.push_back(temp_pair);
    }else{
    

  if(dis[index[0]]<dis[index[1]]){
      temp_pair.first = index[0];
      temp_pair.second = -1;
      cap_pair_sequence.push_back(temp_pair);
      //inital the rest pair sequence based on counterclockwise
      for(int i=1;i<dis.size();i++){
         for(int j=i+1;j<dis.size();j++){
            if(dis[index[i]]!=dis[index[j]]){
                   break;
              }
            if(Caps[index[i]].index_x+Caps[index[j]].index_x==2*Cx and Caps[index[i]].index_y+Caps[index[j]].index_y==2*Cy){
                if(index[i]<index[j]){
                  temp_pair.first = index[i];
                  temp_pair.second = index[j];
                  }else{
                  temp_pair.first = index[j];
                  temp_pair.second = index[i];
                  }
                 cap_pair_sequence.push_back(temp_pair);
                 break;
               }
            }
         }
    }else{
    //initial the rest pair sequence based on counterclockwise
      for(int i=0;i<dis.size();i++){
         for(int j=i+1;j<dis.size();j++){
            if(dis[index[i]]!=dis[index[j]]){
                   break;
              }
            if(Caps[index[i]].index_x+Caps[index[j]].index_x==2*Cx and Caps[index[i]].index_y+Caps[index[j]].index_y==2*Cy){
                if(index[i]<index[j]){
                  temp_pair.first = index[i];
                  temp_pair.second = index[j];
                  }else{
                  temp_pair.first = index[j];
                  temp_pair.second = index[i];
                  }
                 cap_pair_sequence.push_back(temp_pair);
                 break;
               }
            }
         }
    }

    
    }


  cout<<"step2.6"<<endl;  

  if(dummy_flag){
  vector<pair<int,int> > temp_cap_pair_sequence;
  for(int i=0;i<cap_pair_sequence.size();i++){
      if(cap_pair_sequence[i].second!=-1){
        if(Caps[cap_pair_sequence[i].first].index_x!=0 and Caps[cap_pair_sequence[i].first].index_x!=r-1 and Caps[cap_pair_sequence[i].first].index_y!=0 and Caps[cap_pair_sequence[i].first].index_y!=s-1 and Caps[cap_pair_sequence[i].second].index_x!=0 and Caps[cap_pair_sequence[i].second].index_x!=r-1 and Caps[cap_pair_sequence[i].second].index_y!=0 and Caps[cap_pair_sequence[i].second].index_y!=s-1){
         temp_cap_pair_sequence.push_back(cap_pair_sequence[i]);
         }
       }else{
        if(Caps[cap_pair_sequence[i].first].index_x!=0 and Caps[cap_pair_sequence[i].first].index_x!=r-1 and Caps[cap_pair_sequence[i].first].index_y!=0 and Caps[cap_pair_sequence[i].first].index_y!=s-1){
         temp_cap_pair_sequence.push_back(cap_pair_sequence[i]);
         }
       }
     }
  int num_pair= cap_pair_sequence.size();
  for(int i=0;i<num_pair;i++){
     cap_pair_sequence.pop_back();
    }
  cap_pair_sequence= temp_cap_pair_sequence; //remove dummy capacitors
  }

// to be continued here.
  cout<<"step2.7"<<endl;
  initial_net_pair_sequence(ki,cap_pin);
  cout<<"step2.8"<<endl;
  string outfile=final_gds+".plt";
  cout<<"step2.9"<<endl;
  Router_Cap(ki,cap_pin, dummy_flag, cap_ratio, cap_r, cap_s);
  cout<<"step3"<<endl;
  GetPhsicalInfo_router( H_metal, H_metal_index, V_metal, V_metal_index, drc_info);
  cout<<"step4"<<endl;
  cal_offset(drc_info, H_metal_index, V_metal_index, HV_via_metal_index);
  cout<<"step5"<<endl;
  ExtractData(fpath ,unit_capacitor, final_gds, obs, drc_info, H_metal_index, V_metal_index, HV_via_metal_index, opath);
  cout<<"step6"<<endl;
  WriteJSON (fpath ,unit_capacitor, final_gds, drc_info, opath);
  cout<<"step7"<<endl;
  //PrintPlacer_Router_Cap(outfile);
  cout<<"step8"<<endl;


}


// DAK: General methods needed for layer mapping:  we should be using
// stoi(PnRDatabase::DRC_info.MaskID_Metal[layer])
int
getLayerMask (const std::string & layer, PnRDB::Drc_info & drc_info) {
    // DAK: These should be defined in a method that can load this map from a file / PDK
    int index = drc_info.Metalmap[layer];
    int mask = stoi(drc_info.MaskID_Metal[index]);
    return mask;
}
int
getLayerViaMask (const std::string & layer, PnRDB::Drc_info & drc_info) {
    // DAK: These should be defined in a method that can load this map from a file / PDK
    int index = drc_info.Metalmap[layer];
    //string via_name = drc_info.ViaModel[index].name;
    int mask = stoi(drc_info.MaskID_Via[index]);
    return mask;
}

// DAK: Fills a contact with a 4 point rectangle
void
fillContact (PnRDB::contact& con, int* x, int*y) {
    for (int i = 0; i < 4; i++) {
	PnRDB::point temp_point;
	temp_point.x = x[i];
	temp_point.y = y[i];
	con.originBox.polygon.push_back (temp_point);
	switch (i) {
	case 0: con.originBox.LL = temp_point; break;
	case 1: con.originBox.UL = temp_point; break;
	case 2: con.originBox.UR = temp_point; break;
	case 3: con.originBox.LR = temp_point; break;
	}
    }
    con.originCenter.x = (x[0]+x[2])/2;
    con.originCenter.y = (y[0]+y[2])/2;
}

void
Placer_Router_Cap::ExtractData (string fpath, string unit_capacitor, string final_gds, vector<string> & obs, PnRDB::Drc_info & drc_info, int H_metal, int V_metal, int HV_via_index, string opath) {
    string topGDS_loc = opath+final_gds+".gds";
    int gds_unit = 20;
    //writing metals
    int x[5], y[5];
  
//    int width = metal_width[0];
    int Min_x = INT_MAX;
    int Min_y = INT_MAX;
    int Max_x = INT_MIN;
    int Max_y = INT_MIN;
    //for positive nets
    cout<<"Extract Data Step 1"<<endl;
    for (int i = 0; i < Nets_pos.size(); i++) {//for each net
	PnRDB::pin temp_Pins;
	for (int j = 0; j < Nets_pos[i].start_conection_coord.size(); j++) { //for segment

            int width = drc_info.Metal_info[drc_info.Metalmap[Nets_pos[i].metal[j]]].width/2;

	    fillPathBoundingBox (x, y, Nets_pos[i].start_conection_coord[j],
				 Nets_pos[i].end_conection_coord[j], width);
	    if (x[0]<Min_x) Min_x = x[0];
	    if (x[2]>Max_x) Max_x = x[2];
	    if (y[0]<Min_y) Min_y = y[0];
	    if (y[2]>Max_y) Max_y = y[2];

	    PnRDB::contact temp_contact;
            fillContact (temp_contact, x, y);

	    for (int i = 0; i < 5; i++) {
		x[i] *= gds_unit;
		y[i] *= gds_unit;
	    }
	    temp_contact.metal = Nets_pos[i].metal[j];
	    if (Nets_pos[i].Is_pin[j] == 1) {
		temp_Pins.name = Nets_pos[i].name;
		temp_Pins.pinContacts.push_back(temp_contact);
	    }
	    CheckOutBlock.interMetals.push_back(temp_contact);
	}   
	CheckOutBlock.blockPins.push_back(temp_Pins);
    }
    cout<<"Extract Data Step 2"<<endl;
    //for neg nets
    for (int i = 0; i < Nets_neg.size(); i++) {//for each net
	PnRDB::pin temp_Pins_neg;
	for (int j = 0; j < Nets_neg[i].start_conection_coord.size(); j++) { //for segment

            int width = drc_info.Metal_info[drc_info.Metalmap[Nets_neg[i].metal[j]]].width/2;

	    fillPathBoundingBox (x, y, Nets_neg[i].start_conection_coord[j],
				 Nets_neg[i].end_conection_coord[j], width);
            
            if (x[0]<Min_x) Min_x = x[0];
            if (x[2]>Max_x) Max_x = x[2];
            if (y[0]<Min_y) Min_y = y[0];
            if (y[2]>Max_y) Max_y = y[2];

            PnRDB::contact temp_contact;
	    fillContact (temp_contact, x, y);

	    for (int i = 0; i < 5; i++) {
		x[i] *= gds_unit;
		y[i] *= gds_unit;
	    }
            temp_contact.metal = Nets_neg[i].metal[j];
	    if (Nets_neg[i].Is_pin[j] == 1) {
                temp_Pins_neg.name = Nets_neg[i].name;
                temp_Pins_neg.pinContacts.push_back(temp_contact);
	    }
	    CheckOutBlock.interMetals.push_back(temp_contact);
	}
	CheckOutBlock.blockPins.push_back(temp_Pins_neg);
    }
    cout<<"Extract Data Step 3"<<endl;
    //wirting vias
    //for positive net
    //width = via_width[0];
    for (int i = 0; i < Nets_pos.size(); i++) {
	for (int j = 0; j < Nets_pos[i].via.size(); j++) {//the size of via needs to be modified according to different PDK
            cout<<"Extract Data Step 3.1"<<endl;
            int width = drc_info.Via_model[drc_info.Metalmap[Nets_pos[i].via_metal[j]]].ViaRect[1].x;

 	    x[0]=Nets_pos[i].via[j].first - width+offset_x;
	    x[1]=Nets_pos[i].via[j].first - width+offset_x;
	    x[2]=Nets_pos[i].via[j].first + width+offset_x;
	    x[3]=Nets_pos[i].via[j].first + width+offset_x;
	    x[4]=x[0];

            width = drc_info.Via_model[drc_info.Metalmap[Nets_pos[i].via_metal[j]]].ViaRect[1].y;
        
	    y[0]=Nets_pos[i].via[j].second - width+offset_y;
	    y[1]=Nets_pos[i].via[j].second + width+offset_y;
	    y[2]=Nets_pos[i].via[j].second + width+offset_y;
	    y[3]=Nets_pos[i].via[j].second - width+offset_y;
	    y[4]=y[0];
        
	    if (x[0]<Min_x) Min_x = x[0];
	    if (x[2]>Max_x) Max_x = x[2];
	    if (y[0]<Min_y) Min_y = y[0];
	    if (y[2]>Max_y) Max_y = y[2];

	    PnRDB::contact temp_contact;
	    fillContact (temp_contact, x, y);
	    for (int i = 0; i < 5; i++) {
		x[i] *= gds_unit;
		y[i] *= gds_unit;
	    }

//this part needs modify 2019/6/3
            cout<<"Extract Data Step 3.2"<<endl;
	    PnRDB::Via temp_via;
	    PnRDB::contact upper_contact;
	    PnRDB::contact lower_contact;
	    upper_contact.placedCenter = temp_contact.placedCenter;
	    lower_contact.placedCenter = temp_contact.placedCenter;
            cout<<"Extract Data Step 3.3"<<endl;
	    PnRDB::contact h_contact;
            int via_model_index;
            via_model_index = drc_info.Metalmap[Nets_pos[i].via_metal[j]];
            temp_contact.metal = drc_info.Via_model[via_model_index].name;
            h_contact.originBox.LL = drc_info.Via_model[via_model_index].UpperRect[0];
            h_contact.originBox.UR = drc_info.Via_model[via_model_index].UpperRect[1];
            //cout<<"Extract Data Step 3.31"<<endl;
            h_contact.originBox.LL.x = h_contact.originBox.LL.x + temp_contact.placedCenter.x;
            h_contact.originBox.LL.y = h_contact.originBox.LL.y + temp_contact.placedCenter.y;

            h_contact.originBox.UR.x = h_contact.originBox.UR.x + temp_contact.placedCenter.x;
            h_contact.originBox.UR.y = h_contact.originBox.UR.y + temp_contact.placedCenter.y;
            //cout<<"Extract Data Step 3.32"<<endl;
	    h_contact.originBox.UL.x = h_contact.originBox.LL.x;
            h_contact.originBox.UL.y = h_contact.originBox.UR.y;

	    h_contact.originBox.LR.x = h_contact.originBox.UR.x;
            h_contact.originBox.LR.y = h_contact.originBox.LL.y;
            //cout<<"Extract Data Step 3.33"<<endl;
	    h_contact.originBox.polygon.push_back(h_contact.originBox.LL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UR);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.LR);
            cout<<"Extract Data Step 3.4"<<endl;
	    PnRDB::contact v_contact;
            v_contact.originBox.LL = drc_info.Via_model[via_model_index].LowerRect[0];
            v_contact.originBox.UR = drc_info.Via_model[via_model_index].LowerRect[1];

            v_contact.originBox.LL.x = v_contact.originBox.LL.x + temp_contact.placedCenter.x;
            v_contact.originBox.LL.y = v_contact.originBox.LL.y + temp_contact.placedCenter.y;

            v_contact.originBox.UR.x = v_contact.originBox.UR.x + temp_contact.placedCenter.x;
            v_contact.originBox.UR.y = v_contact.originBox.UR.y + temp_contact.placedCenter.y;

	    v_contact.originBox.UL.x = v_contact.originBox.LL.x;
            v_contact.originBox.UL.y = v_contact.originBox.UR.y;

	    v_contact.originBox.LR.x = v_contact.originBox.UR.x;
            v_contact.originBox.LR.y = v_contact.originBox.LL.y;

	    v_contact.originBox.polygon.push_back(v_contact.originBox.LL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UR);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.LR);
            cout<<"Extract Data Step 3.5"<<endl;
            lower_contact.metal = drc_info.Metal_info[drc_info.Via_model[via_model_index].LowerIdx].name;
            upper_contact.metal = drc_info.Metal_info[drc_info.Via_model[via_model_index].UpperIdx].name;
            lower_contact.originBox = v_contact.originBox;
            upper_contact.originBox = h_contact.originBox;
            temp_via.model_index = via_model_index;
            cout<<"Extract Data Step 3.6"<<endl;
	    temp_via.placedpos = temp_contact.originCenter;
	    temp_via.ViaRect = temp_contact;
	    temp_via.LowerMetalRect = lower_contact;
	    temp_via.UpperMetalRect = upper_contact;
	    CheckOutBlock.interVias.push_back(temp_via);
	}
    }
    cout<<"Extract Data Step 4"<<endl;
    //for negative net
    for (int i = 0; i < Nets_neg.size(); i++) {
	for (int j = 0; j <Nets_neg[i].via.size(); j++) {//the size of via needs to be modified according to different PDK
            cout<<"Extract Data Step 4.1"<<endl;
            int width = drc_info.Via_model[drc_info.Metalmap[Nets_neg[i].via_metal[j]]].ViaRect[1].x;

	    x[0]=Nets_neg[i].via[j].first - width+offset_x;
	    x[1]=Nets_neg[i].via[j].first - width+offset_x;
	    x[2]=Nets_neg[i].via[j].first + width+offset_x;
	    x[3]=Nets_neg[i].via[j].first + width+offset_x;
	    x[4]=x[0];

            width = drc_info.Via_model[drc_info.Metalmap[Nets_neg[i].via_metal[j]]].ViaRect[1].y;        
	    y[0]=Nets_neg[i].via[j].second - width+offset_y;
	    y[1]=Nets_neg[i].via[j].second + width+offset_y;
	    y[2]=Nets_neg[i].via[j].second + width+offset_y;
	    y[3]=Nets_neg[i].via[j].second - width+offset_y;
	    y[4]=y[0];
        
	    if (x[0]<Min_x) Min_x = x[0];
	    if (x[2]>Max_x) Max_x = x[2];
	    if (y[0]<Min_y) Min_y = y[0];
	    if (y[2]>Max_y) Max_y = y[2];

	    PnRDB::contact temp_contact;
	    fillContact (temp_contact, x, y);

	    for (int i = 0; i < 5; i++) {
		x[i] *= gds_unit;
		y[i] *= gds_unit;
	    }
            cout<<"Extract Data Step 4.2"<<endl;
	    PnRDB::Via temp_via;
	    PnRDB::contact upper_contact;
	    PnRDB::contact lower_contact;
	    upper_contact.placedCenter = temp_contact.placedCenter;
	    lower_contact.placedCenter = temp_contact.placedCenter;

//this part needs to be modify


	    PnRDB::contact h_contact;
            int via_model_index;
            via_model_index = drc_info.Metalmap[Nets_neg[i].via_metal[j]];
            temp_contact.metal = drc_info.Via_model[via_model_index].name;
            h_contact.originBox.LL = drc_info.Via_model[via_model_index].UpperRect[0];
            h_contact.originBox.UR = drc_info.Via_model[via_model_index].UpperRect[1];

            h_contact.originBox.LL.x = h_contact.originBox.LL.x + temp_contact.placedCenter.x;
            h_contact.originBox.LL.y = h_contact.originBox.LL.y + temp_contact.placedCenter.y;

            h_contact.originBox.UR.x = h_contact.originBox.UR.x + temp_contact.placedCenter.x;
            h_contact.originBox.UR.y = h_contact.originBox.UR.y + temp_contact.placedCenter.y;

	    h_contact.originBox.UL.x = h_contact.originBox.LL.x;
            h_contact.originBox.UL.y = h_contact.originBox.UR.y;

	    h_contact.originBox.LR.x = h_contact.originBox.UR.x;
            h_contact.originBox.LR.y = h_contact.originBox.LL.y;

	    h_contact.originBox.polygon.push_back(h_contact.originBox.LL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UR);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.LR);
            cout<<"Extract Data Step 4.25"<<endl;
	    PnRDB::contact v_contact;
            v_contact.originBox.LL = drc_info.Via_model[via_model_index].LowerRect[0];
            v_contact.originBox.UR = drc_info.Via_model[via_model_index].LowerRect[1];

            v_contact.originBox.LL.x = v_contact.originBox.LL.x + temp_contact.placedCenter.x;
            v_contact.originBox.LL.y = v_contact.originBox.LL.y + temp_contact.placedCenter.y;

            v_contact.originBox.UR.x = v_contact.originBox.UR.x + temp_contact.placedCenter.x;
            v_contact.originBox.UR.y = v_contact.originBox.UR.y + temp_contact.placedCenter.y;

	    v_contact.originBox.UL.x = v_contact.originBox.LL.x;
            v_contact.originBox.UL.y = v_contact.originBox.UR.y;

	    v_contact.originBox.LR.x = v_contact.originBox.UR.x;
            v_contact.originBox.LR.y = v_contact.originBox.LL.y;

	    v_contact.originBox.polygon.push_back(v_contact.originBox.LL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UR);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.LR);
            cout<<"Extract Data Step 4.3"<<endl;
            lower_contact.metal = drc_info.Metal_info[drc_info.Via_model[via_model_index].LowerIdx].name;
            upper_contact.metal = drc_info.Metal_info[drc_info.Via_model[via_model_index].UpperIdx].name;
            lower_contact.originBox = v_contact.originBox;
            upper_contact.originBox = h_contact.originBox;
            temp_via.model_index = via_model_index;
            cout<<"Extract Data Step 4.4"<<endl;
	    temp_via.placedpos = temp_contact.originCenter;
	    temp_via.ViaRect = temp_contact;
	    temp_via.LowerMetalRect = lower_contact;
	    temp_via.UpperMetalRect = upper_contact;
	    CheckOutBlock.interVias.push_back(temp_via);
	}
    }
    CheckOutBlock.orient = PnRDB::Omark(0); //need modify
    cout<<"Extract Data Step 5"<<endl;
    for (int i = 0; i < Caps.size(); i++) {
	x[0]=Caps[i].x - unit_cap_demension.first/2+offset_x;
	x[1]=Caps[i].x - unit_cap_demension.first/2+offset_x;
	x[2]=Caps[i].x + unit_cap_demension.first/2+offset_x;
	x[3]=Caps[i].x + unit_cap_demension.first/2+offset_x;
	x[4]=x[0];
       
	y[0]=Caps[i].y - unit_cap_demension.second/2+offset_y;
	y[1]=Caps[i].y + unit_cap_demension.second/2+offset_y;
	y[2]=Caps[i].y + unit_cap_demension.second/2+offset_y;
	y[3]=Caps[i].y - unit_cap_demension.second/2+offset_y;
	y[4]=y[0];
     
	if (x[0]<Min_x) Min_x = x[0];
	if (x[2]>Max_x) Max_x = x[2];
	if (y[0]<Min_y) Min_y = y[0];
	if (y[2]>Max_y) Max_y = y[2];

//this part need modify, here the 
	PnRDB::point temp_point;
	PnRDB::contact temp_contact;
	fillContact (temp_contact, x, y);

        for(int i=0;i<obs.size();i++){
            temp_contact.metal = obs[i];
            CheckOutBlock.interMetals.push_back(temp_contact);
           }
    }
    cout<<"Extract Data Step 7"<<endl;


    int coverage_x;
    int coverage_y;
  
    if(drc_info.Via_model[HV_via_index].LowerIdx == V_metal){
       coverage_y = drc_info.Via_model[HV_via_index].ViaRect[0].y - drc_info.Via_model[HV_via_index].LowerRect[0].y;
       coverage_x = drc_info.Via_model[HV_via_index].ViaRect[0].x - drc_info.Via_model[HV_via_index].UpperRect[0].x;
    }else{
       coverage_y = drc_info.Via_model[HV_via_index].ViaRect[0].y - drc_info.Via_model[HV_via_index].UpperRect[0].y;
       coverage_x = drc_info.Via_model[HV_via_index].ViaRect[0].x - drc_info.Via_model[HV_via_index].LowerRect[0].x;
    }

    Min_x = Min_x - drc_info.Metal_info[V_metal].grid_unit_x + drc_info.Metal_info[V_metal].width/2+coverage_x;
    Min_y = Min_y - drc_info.Metal_info[H_metal].grid_unit_y + drc_info.Metal_info[H_metal].width/2+coverage_y;
    //Min_x = 0;
    //Min_y = 0;
    Max_x = Max_x + drc_info.Metal_info[V_metal].grid_unit_x - drc_info.Metal_info[V_metal].width/2-coverage_x;
    Max_x = ceil(Max_x/drc_info.Metal_info[V_metal].grid_unit_x)*drc_info.Metal_info[V_metal].grid_unit_x;
    Max_y = Max_y + drc_info.Metal_info[H_metal].grid_unit_y - drc_info.Metal_info[H_metal].width/2-coverage_y;
    


    CheckOutBlock.gdsFile = topGDS_loc;
    PnRDB::point temp_point;
    temp_point.x = Min_x;
    temp_point.y = Min_y;
    CheckOutBlock.originBox.polygon.push_back(temp_point);
    CheckOutBlock.originBox.LL = temp_point;
    temp_point.x = Min_x;
    temp_point.y = Max_y;
    CheckOutBlock.originBox.polygon.push_back(temp_point);
    CheckOutBlock.originBox.UL = temp_point;
    temp_point.x = Max_x;
    temp_point.y = Max_y;
    CheckOutBlock.originBox.polygon.push_back(temp_point);
    CheckOutBlock.originBox.UR = temp_point;
    temp_point.x = Max_x;
    temp_point.y = Min_y;
    CheckOutBlock.originBox.polygon.push_back(temp_point);
    CheckOutBlock.originBox.LR = temp_point;
    CheckOutBlock.originCenter.x = (CheckOutBlock.originBox.LL.x + CheckOutBlock.originBox.UR.x)/2;
    CheckOutBlock.originCenter.y = (CheckOutBlock.originBox.LL.y + CheckOutBlock.originBox.UR.y)/2;
    CheckOutBlock.width = CheckOutBlock.originBox.UR.x-CheckOutBlock.originBox.LL.x;
    CheckOutBlock.height = CheckOutBlock.originBox.UR.y-CheckOutBlock.originBox.LL.y;
}

void
Placer_Router_Cap::cal_offset(PnRDB::Drc_info &drc_info, int H_metal, int V_metal, int HV_via_index) {
    int x[5], y[5];
    int sx[5], sy[5];
    //int width = metal_width[0];
    int Min_x = INT_MAX;
    int Min_y = INT_MAX;
    int Max_x = INT_MIN;
    int Max_y = INT_MIN;
    //for positive nets
    // vector<pair<double,double> f, s;  int width
  
    for (int i = 0; i< Nets_pos.size(); i++) {//for each net
	for (int j = 0; j< Nets_pos[i].start_conection_coord.size();j++) { //for segment
            int width = drc_info.Metal_info[drc_info.Metalmap[Nets_pos[i].metal[j]]].width/2;
	    fillPathBoundingBox (x, y, Nets_pos[i].start_conection_coord[j],
				 Nets_pos[i].end_conection_coord[j], width);

            if (x[0] < Min_x) Min_x = x[0];
            if (x[2] > Max_x) Max_x = x[2];
            if (y[0] < Min_y) Min_y = y[0];
            if (y[2] > Max_y) Max_y = y[2];
        }
    }
  
    //for neg nets
    for (int i = 0; i <  Nets_neg.size(); i++) {//for each net
	for (int j = 0; j <  Nets_neg[i].start_conection_coord.size();j++) { //for segment
            int width = drc_info.Metal_info[drc_info.Metalmap[Nets_neg[i].metal[j]]].width/2;
	    fillPathBoundingBox (x, y, Nets_neg[i].start_conection_coord[j],
				 Nets_neg[i].end_conection_coord[j], width);

            if (x[0] < Min_x) Min_x = x[0];
            if (x[2] > Max_x) Max_x = x[2];
            if (y[0] < Min_y) Min_y = y[0];
            if (y[2] > Max_y) Max_y = y[2];
        }
    }
  
    //wirting vias
    //for positive net
    //width  =  via_width[0];
    for (int i = 0; i < Nets_pos.size(); i++) {
	for (int j = 0; j < Nets_pos[i].via.size(); j++) {//the size of via needs to be modified according to different PDK

            int width = drc_info.Via_model[drc_info.Metalmap[Nets_pos[i].via_metal[j]]].ViaRect[1].x;

	    x[0] = Nets_pos[i].via[j].first - width;
	    x[1] = Nets_pos[i].via[j].first - width;
	    x[2] = Nets_pos[i].via[j].first + width;
	    x[3] = Nets_pos[i].via[j].first + width;
	    x[4] = x[0];

            width = drc_info.Via_model[drc_info.Metalmap[Nets_pos[i].via_metal[j]]].ViaRect[1].y;        
	    y[0] = Nets_pos[i].via[j].second - width;
	    y[1] = Nets_pos[i].via[j].second + width;
	    y[2] = Nets_pos[i].via[j].second + width;
	    y[3] = Nets_pos[i].via[j].second - width;
	    y[4] = y[0];

	    if (x[0] < Min_x) Min_x = x[0];
	    if (x[2] > Max_x) Max_x = x[2];
	    if (y[0] < Min_y) Min_y = y[0];
	    if (y[2] > Max_y) Max_y = y[2];
	}
    }
    
    //for negative net
    for (int i = 0;i < Nets_neg.size(); i++) {
	for (int j = 0; j < Nets_neg[i].via.size(); j++) {//the size of via needs to be modified according to different PDK
 
            int width = drc_info.Via_model[drc_info.Metalmap[Nets_neg[i].via_metal[j]]].ViaRect[1].x;

	    x[0] = Nets_neg[i].via[j].first - width;
	    x[1] = Nets_neg[i].via[j].first - width;
	    x[2] = Nets_neg[i].via[j].first + width;
	    x[3] = Nets_neg[i].via[j].first + width;
	    x[4] = x[0];

            width = drc_info.Via_model[drc_info.Metalmap[Nets_neg[i].via_metal[j]]].ViaRect[1].y;
        
	    y[0] = Nets_neg[i].via[j].second - width;
	    y[1] = Nets_neg[i].via[j].second + width;
	    y[2] = Nets_neg[i].via[j].second + width;
	    y[3] = Nets_neg[i].via[j].second - width;
	    y[4] = y[0];
        
	    if (x[0] < Min_x) Min_x = x[0];
	    if (x[2] > Max_x) Max_x = x[2];
	    if (y[0] < Min_y) Min_y = y[0];
	    if (y[2] > Max_y) Max_y = y[2];
	}
    }
  
    for (int i = 0; i < Caps.size(); i++) {
	x[0] = Caps[i].x - unit_cap_demension.first/2;
	x[1] = Caps[i].x - unit_cap_demension.first/2;
	x[2] = Caps[i].x + unit_cap_demension.first/2;
	x[3] = Caps[i].x + unit_cap_demension.first/2;
	x[4] = x[0];
       
	y[0] = Caps[i].y - unit_cap_demension.second/2;
	y[1] = Caps[i].y + unit_cap_demension.second/2;
	y[2] = Caps[i].y + unit_cap_demension.second/2;
	y[3] = Caps[i].y - unit_cap_demension.second/2;
	y[4] = y[0];

	if (x[0] < Min_x) Min_x = x[0];
	if (x[2] > Max_x) Max_x = x[2];
	if (y[0] < Min_y) Min_y = y[0];
	if (y[2] > Max_y) Max_y = y[2];
    }

    int coverage_x;
    int coverage_y;
  
    if(drc_info.Via_model[HV_via_index].LowerIdx == V_metal){
       coverage_y = drc_info.Via_model[HV_via_index].ViaRect[0].y - drc_info.Via_model[HV_via_index].LowerRect[0].y;
       coverage_x = drc_info.Via_model[HV_via_index].ViaRect[0].x - drc_info.Via_model[HV_via_index].UpperRect[0].x;
    }else{
       coverage_y = drc_info.Via_model[HV_via_index].ViaRect[0].y - drc_info.Via_model[HV_via_index].UpperRect[0].y;
       coverage_x = drc_info.Via_model[HV_via_index].ViaRect[0].x - drc_info.Via_model[HV_via_index].LowerRect[0].x;
    }

    //int detal_x;
    //detal_x = Max_x -Min_x;
    //detal_x = ceil(detal_x/drc_info.Metal_info[V_metal].grid_unit_x)*drc_info.Metal_info[V_metal].grid_unit_x;
    

    offset_x = 0-Min_x;
    offset_x = offset_x + drc_info.Metal_info[V_metal].grid_unit_x - drc_info.Metal_info[V_metal].width/2 - coverage_x;
    //offset_x = offset_x + (detal_x - (Max_x-Min_x))/2;
    offset_y = 0-Min_y;
    offset_y = offset_y + drc_info.Metal_info[H_metal].grid_unit_y - drc_info.Metal_info[H_metal].width/2 - coverage_y;
    
}

void Placer_Router_Cap::initial_net_pair_sequence(vector<int> & ki, vector<pair<string, string> > & cap_pin){
//initial net pair sequence
  cout<<"test case 1"<<endl;
  vector<pair<int,int> > S_unique;
  vector<pair<int,int> > S_unit_unit;
  vector<pair<int,int> > S_unit_odd;
  vector<pair<int,int> > S_odd_odd;
  vector<pair<int,int> > S;
  pair<int,int> temp_pair;
  vector<int> C_unit;
  vector<int> C_odd;
  vector<int> C_even;
  for(int i=0;i<ki.size();i++){
       if(ki[i]==1){
           C_unit.push_back(i);
         }else if(ki[i]%2==1){
           C_odd.push_back(i);
         }else{
           C_even.push_back(i);
         }
     }
  //initial net pair sequence for pair
  cout<<"test case 2"<<endl;
  int size;
  for(int i=0;i<C_even.size();i++){
     size = ki[C_even[i]];
     while(size>1){
         temp_pair.first=C_even[i];
         temp_pair.second=C_even[i];
         size=size-2;
         S.push_back(temp_pair);
        }
     }
  for(int i=0;i<C_odd.size();i++){
     size = ki[C_odd[i]];
     while(size>1){
         temp_pair.first=C_odd[i];
         temp_pair.second=C_odd[i];
         size=size-2;
         S.push_back(temp_pair);
        }
     }

  cout<<"test case 3"<<endl;
/*
  for(int i=0;i<ki.size();i++){
       while(ki[i]>1){
         temp_pair.first=i;
         temp_pair.second=i;
         ki[i]=ki[i]-2;
         S.push_back(temp_pair);
        }
     }
*/
  //initial net pair sequence for odd 
  int num_unit = C_unit.size();
  int num_odd = C_odd.size();
  while(num_odd>1){
     temp_pair.first = C_odd[num_odd-1];
     temp_pair.second = C_odd[num_odd-2];
     C_odd.pop_back();
     C_odd.pop_back();
     num_odd = num_odd -2;
     S_odd_odd.push_back(temp_pair);
  }
  if(num_odd==1 and num_unit>0){
     temp_pair.first = C_odd[num_odd-1];
     temp_pair.second = C_unit[num_unit-1];
     C_unit.pop_back();
     num_unit = num_unit -1;
     num_odd = num_odd -1;
     S_unit_odd.push_back(temp_pair);
  }else if(num_odd==1 and num_unit ==0){
     temp_pair.first = C_odd[num_odd-1];
     temp_pair.second = -1;
     num_odd = num_odd -1;
     S_unique.push_back(temp_pair);
  }
  ////initial net pair sequence for unit
  while(num_unit>1){
     temp_pair.first = C_unit[num_unit-1];
     temp_pair.second = C_unit[num_unit-2];
     C_unit.pop_back();
     C_unit.pop_back();
     num_unit = num_unit -2;
     S_unit_unit.push_back(temp_pair);
  }
  if(num_unit==1){
    temp_pair.first = C_unit[num_unit-1];
     temp_pair.second = -1;
     num_unit = num_unit -1;
     S_unique.push_back(temp_pair);
  }
  if(S_unique.size()>1){
     std::cout<<"Error in S_unique"<<std::endl;
    }
  for(int i=0;i<S_unique.size();i++){
      net_sequence.push_back(S_unique[i]);
    }
  for(int i=0;i<S_unit_unit.size();i++){
      net_sequence.push_back(S_unit_unit[i]);
    }
  for(int i=0;i<S_unit_odd.size();i++){
      net_sequence.push_back(S_unit_odd[i]);
    }
  for(int i=0;i<S_odd_odd.size();i++){
      net_sequence.push_back(S_odd_odd[i]);
    }
  for(int i=0;i<S.size();i++){
      net_sequence.push_back(S[i]);
    }
  cout<<"test case 4"<<endl;
  net temp_net;

  for(int i=0;i<ki.size()+1;i++){
     if(i<ki.size()){
       temp_net.name = cap_pin[i].second;
     }else{
       temp_net.name = "dummy_gnd";
     }
     Nets_pos.push_back(temp_net);
   }

  cout<<"test case 4.5"<<endl;
  int start_index=0;
  for(int i=0;i<net_sequence.size();i++){
     if(net_sequence[i].second==-1){
        cout<<"test case 4.51"<<endl;
        cout<<net_sequence[i].first<<endl;
        cout<<cap_pair_sequence[start_index].first<<endl;
        Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
        cout<<"1"<<endl;
        Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
        cout<<"2"<<endl;
        start_index = start_index+1;
        cout<<"test case 4.52"<<endl;
       }else if(net_sequence[i].second!=-1 and cap_pair_sequence[start_index].second == -1){
        cout<<"test case 4.53"<<endl;
        start_index = start_index+1;
        Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
        cout<<"1"<<endl;
        Nets_pos[net_sequence[i].second].cap_index.push_back(cap_pair_sequence[start_index].second);
        cout<<"2"<<endl;
        Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
        cout<<"3"<<endl;
        Caps[cap_pair_sequence[start_index].second].net_index = net_sequence[i].second;
        start_index = start_index+1;
        cout<<"test case 4.54"<<endl;
       }else if(net_sequence[i].second!=-1 and cap_pair_sequence[start_index].second != -1){
        cout<<"test case 4.55"<<endl;
        Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
        cout<<"1"<<endl;
        Nets_pos[net_sequence[i].second].cap_index.push_back(cap_pair_sequence[start_index].second);
        cout<<"2"<<endl;
        Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
        cout<<"3"<<endl;
        Caps[cap_pair_sequence[start_index].second].net_index = net_sequence[i].second;
        start_index = start_index+1;
        cout<<"test case 4.56"<<endl;
      }
     }
  //add a net for dummy capacitor


  // a dummy net is added for dummy capacitor
  cout<<"test case 5"<<endl;

/*
  int addition_dummy = 0;
  //int dummy_cap = Nets_pos.size();
  for(int i=0;i<Caps.size();i++){
      if(Caps[i].net_index==-1 and addition_dummy ==0){
         addition_dummy = 1;
         temp_net.name = "dummy_gnd";
         Nets_pos.push_back(temp_net);
         int dummy_cap = Nets_pos.size();
         Nets_pos[dummy_cap-1].cap_index.push_back(i);
        } else if(Caps[i].net_index==-1 and addition_dummy ==1){
         int dummy_cap = Nets_pos.size();
         Nets_pos[dummy_cap-1].cap_index.push_back(i);
        }
     }
*/
  //int addition_dummy = 0;
  int dummy_cap = Nets_pos.size();
  for(int i=0;i<Caps.size();i++){
      if(Caps[i].net_index==-1){
         Nets_pos[dummy_cap-1].cap_index.push_back(i);
        }
     }

  
}


void Placer_Router_Cap::perturbation_pair_sequence(){
//perturbate pair sequence

}

void Placer_Router_Cap::Placer_Cap(vector<int> & ki){
  
}

void Placer_Router_Cap::Router_Cap(vector<int> & ki, vector<pair<string, string> > &cap_pin, bool dummy_flag, bool cap_ratio, int cap_r, int cap_s){

  cout<<"broken down 1"<<endl;
//route for cap
  for(int i=0;i<Nets_pos.size();i++){ // for each net
     for(int j=0;j<Nets_pos[i].cap_index.size();j++){ //for each unaccessed cap
        if(Caps[Nets_pos[i].cap_index[j]].access==0){
           connection_set temp_set;
           temp_set.cap_index.push_back(Nets_pos[i].cap_index[j]); //new set & marked accessed
           Caps[Nets_pos[i].cap_index[j]].access = 1;
           //found its neighbor recursively
           int found=found_neighbor(j,Nets_pos[i],temp_set);
           Nets_pos[i].Set.push_back(temp_set);
          }
        } 
    }
  cout<<"broken down 2"<<endl;
  int net_size = ki.size();
  double sum = 0;
  double r;
  double s;
  for(int i=0;i<net_size;i++){
     sum = sum + ki[i];
    }
  cout<<"broken down 3"<<endl;

   r = ceil(sqrt(sum));
   s = ceil(sum/r);

   if(cap_ratio){
   r = cap_r;
   s = cap_s;
   }

   if(dummy_flag){
   r= r+2;
   s= s+2;
   }

   double Cx = (r)/2; //note this is different
   double Cy = (s)/2; //note this is different
//create router line for each net (cap) vertical 

  cout<<"broken down 3.1"<<endl;
  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<Nets_pos[i].Set.size();j++){
         cout<<"broken down 3.11"<<endl;
         connection_set temp_router_line;
         //initial temp_router_line
         for(int k=0;k<=r;k++){
             temp_router_line.cap_index.push_back(0);
            }
         cout<<"broken down 3.2"<<endl;
         for(int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
             cout<<"broken down 3.3"<<endl;
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x+1]=1;
             cout<<"broken down 3.4"<<endl;
             temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
             cout<<"broken down 3.5"<<endl;
             temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x-1]=1;//-1
            }
         cout<<"broken down 3.6"<<endl;
         Nets_pos[i].router_line_v.push_back(temp_router_line);
         cout<<"broken down 3.7"<<endl;
        }
     }

  cout<<"broken down 4"<<endl;
//common overlap checking vertical
  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<=r;j++){
          Nets_pos[i].routable_line_v.push_back(1);
        }
     for(int k=0;k<Nets_pos[i].router_line_v.size();k++){
          for(int l=0;l<Nets_pos[i].router_line_v[k].cap_index.size();l++){
             Nets_pos[i].routable_line_v[l] =(int) Nets_pos[i].routable_line_v[l] and Nets_pos[i].router_line_v[k].cap_index[l];
             }
        }
     }

  cout<<"broken down 5"<<endl;
//create router line for each net (cap) horizontal
  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<Nets_pos[i].Set.size();j++){
         connection_set temp_router_line;
         //initial temp_router_line
         for(int k=0;k<=s;k++){
             temp_router_line.cap_index.push_back(0);
            }
         for(int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_y]=1;
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_y+1]=1;
             temp_router_line.cap_index[2*Cy-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y]=1;
             temp_router_line.cap_index[2*Cy-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y-1]=1;//-1
            }
         Nets_pos[i].router_line_h.push_back(temp_router_line);
        }
     }

  cout<<"broken down 6"<<endl;
//common overlap checking horizontal
  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<=s;j++){
          Nets_pos[i].routable_line_h.push_back(1);
        }
     for(int k=0;k<Nets_pos[i].router_line_h.size();k++){
          for(int l=0;l<Nets_pos[i].router_line_h[k].cap_index.size();l++){
             Nets_pos[i].routable_line_h[l] =(int) Nets_pos[i].routable_line_h[l] and Nets_pos[i].router_line_h[k].cap_index[l];
             }
        }
     }


  cout<<"broken down 7"<<endl;
//create router line for each net (cap) half vertical 
  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<Nets_pos[i].Set.size();j++){
         connection_set temp_router_line;
         //initial temp_router_line
         for(int k=0;k<=r;k++){
             temp_router_line.cap_index.push_back(0);
            }
         for(int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_x+1]=1;
             //temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
             //temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x-1]=1;
            }
         Nets_pos[i].half_router_line_v.push_back(temp_router_line);
        }
     }

  cout<<"broken down 8"<<endl;
//create router line for each net (cap) half horizontal
  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<Nets_pos[i].Set.size();j++){
         connection_set temp_router_line;
         //initial temp_router_line
         for(int k=0;k<=s;k++){
             temp_router_line.cap_index.push_back(0);
            }
         for(int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_y]=1;
             temp_router_line.cap_index[Caps[Nets_pos[i].Set[j].cap_index[l]].index_y+1]=1;
             //temp_router_line.cap_index[2*Cy-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y]=1;
             //temp_router_line.cap_index[2*Cy-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y-1]=1;
            }
         Nets_pos[i].half_router_line_h.push_back(temp_router_line);
        }
     }
  

  cout<<"broken down 9"<<endl;
  //initial num_router_net_v
  for(int i=0;i<=r;i++){num_router_net_v.push_back(0);}
  //initial num_router_net_h
  for(int i=0;i<=s;i++){num_router_net_h.push_back(0);}
  
  //Nets_neg = Nets_pos;

  Nets_neg = Nets_pos;
  for(int i=0;i<Nets_pos.size();i++){
       if(i!=Nets_pos.size()-1){
           Nets_neg[i].name = cap_pin[i].first;
         }else{
           Nets_neg[i].name = "dummy_gnd";
         }
     }
  
  cout<<"broken down 10"<<endl;
//Next work for good router
//sample route methodology just for v pos
  for(int i=0;i<Nets_pos.size();i++){
      for(int k=0;k<=r;k++){Nets_pos[i].line_v.push_back(0);}
      int sum=0;
      for(int k=0;k<Nets_pos[i].routable_line_v.size();k++){sum=sum+Nets_pos[i].routable_line_v[k];}
      if(sum>0){
         //use the information of routable_line_v
         int router_num=Nets_pos.size();
         int choosed_router=-1;
         for(int j=0;j<=Cx;j++){
              if(Nets_pos[i].routable_line_v[j]==1){
                  if(num_router_net_v[j]<=router_num){
                     choosed_router=j;
                     router_num = num_router_net_v[j];
                    }
                }
            }
         if(1){
         Nets_pos[i].line_v[choosed_router]=1;
         Nets_pos[i].line_v[2*Cx-choosed_router]=1;
         num_router_net_v[choosed_router]=num_router_net_v[choosed_router]+1;
         num_router_net_v[2*Cx-choosed_router]=num_router_net_v[2*Cx-choosed_router]+1;
            }else{
            Nets_pos[i].line_v[choosed_router]=1;
            num_router_net_v[choosed_router]=num_router_net_v[choosed_router]+1;
            }
             
       }else{
         //use the information of half_routable_line_v
         for(int l=0;l<Nets_pos[i].half_router_line_v.size();l++){
             int found=0;
             for(int k=0;k<Nets_pos[i].half_router_line_v[l].cap_index.size();k++){
                 if(Nets_pos[i].half_router_line_v[l].cap_index[k]==1 and Nets_pos[i].line_v[k]==1){
                   found =1;
                   }
                }
             if(found ==0){
                int router_num=Nets_pos.size();
                int choosed_router=-1;
                for(int k=0;k<Nets_pos[i].half_router_line_v[l].cap_index.size();k++){
                    if(Nets_pos[i].half_router_line_v[l].cap_index[k]==1){
                       if(num_router_net_v[k]<=router_num){
                          choosed_router=k;
                          router_num = num_router_net_v[k];
                         }
                      }
                   }
                Nets_pos[i].line_v[choosed_router]=1;
               // Nets_pos[i].line_v[2*Cx-choosed_router]=1;
                num_router_net_v[choosed_router]=num_router_net_v[choosed_router]+1;
               // num_router_net_v[2*Cx-choosed_router]=num_router_net_v[2*Cx-choosed_router]+1;
               }
            }
       }
     }

  cout<<"broken down 11"<<endl;
//sample route methodology just for v neg
  for(int i=0;i<Nets_neg.size();i++){
      for(int k=0;k<=r;k++){Nets_neg[i].line_v.push_back(0);}
      int sum=0;
      for(int k=0;k<Nets_neg[i].routable_line_v.size();k++){sum=sum+Nets_neg[i].routable_line_v[k];}
      if(sum>0){
         //use the information of routable_line_v
         int router_num=2*Nets_neg.size();
         int choosed_router=-1;
         for(int j=0;j<=Cx;j++){
              if(Nets_neg[i].routable_line_v[j]==1){
                  if(num_router_net_v[j]<=router_num){
                     choosed_router=j;
                     router_num = num_router_net_v[j];
                    }
                }
            }
         if(1){
         Nets_neg[i].line_v[choosed_router]=1;
         Nets_neg[i].line_v[2*Cx-choosed_router]=1;
         num_router_net_v[choosed_router]=num_router_net_v[choosed_router]+1;
         num_router_net_v[2*Cx-choosed_router]=num_router_net_v[2*Cx-choosed_router]+1;
            }else{
            Nets_neg[i].line_v[2*Cx-choosed_router]=1;
            num_router_net_v[2*Cx-choosed_router]=num_router_net_v[2*Cx-choosed_router]+1;
            }
             
       }else{
         //use the information of half_routable_line_v
         for(int l=0;l<Nets_neg[i].half_router_line_v.size();l++){
             int found=0;
             for(int k=0;k<Nets_neg[i].half_router_line_v[l].cap_index.size();k++){
                 if(Nets_neg[i].half_router_line_v[l].cap_index[k]==1 and Nets_neg[i].line_v[k]==1){
                   found =1;
                   }
                }
             if(found ==0){
                int router_num=Nets_neg.size();
                int choosed_router=-1;
                for(int k=0;k<Nets_neg[i].half_router_line_v[l].cap_index.size();k++){
                    if(Nets_neg[i].half_router_line_v[l].cap_index[k]==1){
                       if(num_router_net_v[k]<=router_num){
                          choosed_router=k;
                          router_num = num_router_net_v[k];
                         }
                      }
                   }
                Nets_neg[i].line_v[choosed_router]=1;
               // Nets_pos[i].line_v[2*Cx-choosed_router]=1;
                num_router_net_v[choosed_router]=num_router_net_v[choosed_router]+1;
               // num_router_net_v[2*Cx-choosed_router]=num_router_net_v[2*Cx-choosed_router]+1;
               }
            }
       }
     }

  cout<<"broken down 12"<<endl;
   vector<int> num_line;
   for(int i=0;i<Nets_pos[0].line_v.size();i++){num_line.push_back(0);}
   for(int i=0;i<Nets_pos.size();i++){
       for(int j=0;j<Nets_pos[i].line_v.size();j++){
           num_line[j]=Nets_pos[i].line_v[j]+Nets_neg[i].line_v[j]+num_line[j];
          }
      }
   //int min_dis = 500; //min distance between each metal more modification
   int max_num_ =0;
   for(int i=0;i<Nets_pos[0].line_v.size();i++){
        if(num_line[i]>max_num_){
           max_num_ = num_line[i];
          }
      }

  cout<<"broken down 13"<<endl;
   span_distance.first = (max_num_+1)*min_dis_x;
  cout<<span_distance.first<<endl;

  for(int i=0;i<Caps.size();i++){
      Caps[i].x = unit_cap_demension.first/2 +  Caps[i].index_x* (unit_cap_demension.first+span_distance.first);
     }

  cout<<"broken down 14"<<endl;
//route methdology in paper just for v
  //for one routable net

//route for the rest net (the same as sample router mathodology)

//generate the route phsical information
  //determine the start point and end point
  //for common cap both positive and negative
  //for dummy just negative is fine
  //finally return the port phsical information
  //adjust a uniform margin between the caps

//write gds file
  //based on the location of unit capacitor

  //and also give out the location of generated capacitor path to the centor database

}

int Placer_Router_Cap::found_neighbor(int j, net& pos, connection_set& temp_set){
  int found = -1;
  for(int i=0;i<pos.cap_index.size();i++){
      if(Caps[pos.cap_index[i]].access==0){
         if((Caps[pos.cap_index[i]].index_x == Caps[pos.cap_index[j]].index_x and abs(Caps[pos.cap_index[i]].index_y -Caps[pos.cap_index[j]].index_y)==1) or (Caps[pos.cap_index[i]].index_y == Caps[pos.cap_index[j]].index_y and abs(Caps[pos.cap_index[i]].index_x -Caps[pos.cap_index[j]].index_x)==1)){
             Caps[pos.cap_index[i]].access = 1;
             temp_set.cap_index.push_back(pos.cap_index[i]);
             found = i;
             int num_found = found_neighbor(i, pos, temp_set);
           }
        }
     } 
  if(found = -1){
         return -1;
       }else{
         return 1;
       }
}

void Placer_Router_Cap::addVia(net &temp_net, pair<double,double> &coord, PnRDB::Drc_info &drc_info, string HV_via_metal, int HV_via_metal_index, int isPin){

  pair<double,double> via_coord;

  temp_net.via.push_back(coord);                      
  temp_net.via_metal.push_back(HV_via_metal);

  if(drc_info.Metal_info[drc_info.Via_model[HV_via_metal_index].LowerIdx].direct==1){
     //lower metal
     //start point
     via_coord.first = drc_info.Via_model[HV_via_metal_index].LowerRect[0].x;
     via_coord.second = 0;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second;
     temp_net.start_conection_coord.push_back(via_coord);
     //end point
     via_coord.first = drc_info.Via_model[HV_via_metal_index].LowerRect[1].x;
     via_coord.second = 0;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second; 
     temp_net.end_conection_coord.push_back(via_coord); 
     temp_net.Is_pin.push_back(isPin);
     temp_net.metal.push_back(drc_info.Metal_info[drc_info.Via_model[HV_via_metal_index].LowerIdx].name);
                     
     //upper metal
     //start point
     via_coord.first = 0;
     via_coord.second = drc_info.Via_model[HV_via_metal_index].UpperRect[0].y;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second;
     temp_net.start_conection_coord.push_back(via_coord);
     //end point
     via_coord.first = 0;
     via_coord.second = drc_info.Via_model[HV_via_metal_index].UpperRect[1].y;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second; 
     temp_net.end_conection_coord.push_back(via_coord); 
     temp_net.Is_pin.push_back(isPin);
     temp_net.metal.push_back(drc_info.Metal_info[drc_info.Via_model[HV_via_metal_index].UpperIdx].name); 
                                                
    }else{

     //lower metal
     //start point
     via_coord.first = 0;
     via_coord.second = drc_info.Via_model[HV_via_metal_index].LowerRect[0].y;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second;
     temp_net.start_conection_coord.push_back(via_coord);
     //end point
     via_coord.first = 0;
     via_coord.second = drc_info.Via_model[HV_via_metal_index].LowerRect[1].y;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second; 
     temp_net.end_conection_coord.push_back(via_coord); 
     temp_net.Is_pin.push_back(isPin);
     temp_net.metal.push_back(drc_info.Metal_info[drc_info.Via_model[HV_via_metal_index].LowerIdx].name);
                          
     //upper metal
     //start point
     via_coord.first = drc_info.Via_model[HV_via_metal_index].UpperRect[0].x;
     via_coord.second = 0;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second;
     temp_net.start_conection_coord.push_back(via_coord);
     //end point
     via_coord.first = drc_info.Via_model[HV_via_metal_index].UpperRect[1].x;
     via_coord.second = 0;
     via_coord.first = via_coord.first + coord.first;
     via_coord.second = via_coord.second + coord.second; 
     temp_net.end_conection_coord.push_back(via_coord); 
     temp_net.Is_pin.push_back(isPin);
     temp_net.metal.push_back(drc_info.Metal_info[drc_info.Via_model[HV_via_metal_index].UpperIdx].name);                     
     }


}

void Placer_Router_Cap::GetPhsicalInfo_router(string H_metal, int H_metal_index, string V_metal, int V_metal_index, PnRDB::Drc_info &drc_info){

  int grid_offset;
  int height_cap = INT_MIN;

  for(int i=0;i<Caps.size();i++){
      if(Caps[i].y+unit_cap_demension.second/2 > height_cap){
          height_cap = Caps[i].y + unit_cap_demension.second/2;
        }
     }

  int near_grid = ceil(height_cap/drc_info.Metal_info[H_metal_index].grid_unit_y)*drc_info.Metal_info[H_metal_index].grid_unit_y;

  grid_offset = (near_grid - height_cap)/2;

//via by via model

  //for each net
    //for each connection set
    // determine the pentential longest part
    // connect the rest
    // also focus on overlap issue

/*
  Nets_neg = Nets_pos;
//update span demension
   int num_in_eachtrail = Nets_pos[0].line_v.size();
   vector<int> routed_trails;
   for(int i=0;i<num_in_eachtrail;i++){routed_trails.push_back(0);}
   for(int i=0;i<Nets_pos.size();i++){
      //Nets_pos[i].line_v_r=Nets_pos[i].line_v;
      for(int l=0;l<Nets_pos[i].line_v.size();l++){
          if(Nets_pos[i].line_v[l]==1){
              int lock_update_left = 0;
              int lock_update_right = 0;
              routed_trails[l]=routed_trails[l]+1;
              for(int k=0;k<Nets_pos[i].cap_index.size();k++){
                  if(Caps[Nets_pos[i].cap_index[k]].index_x==l){
                      
                      if(lock_update_left == 0){
                          lock_update_left = 1;
                         }
                      
                    }else if(l-Caps[Nets_pos[i].cap_index[k]].index_x==1){
                      
                      if(lock_update_right == 0){
                          lock_update_right = 1;
                         }
                    }
                 }
                if(lock_update_right==1 and lock_update_left==1){
                   Nets_neg[i].line_v[l]=1;
                   routed_trails[l]=routed_trails[l]+1;
                   }else if(lock_update_left==1){
                      Nets_neg[i].line_v[l]=0;
                      Nets_neg[i].line_v[l+1]=1;
                      routed_trails[l+1]=routed_trails[l+1]+1;
                   }else if(lock_update_right==1){
                      Nets_neg[i].line_v[l]=0;
                      Nets_neg[i].line_v[l-1]=1;
                      routed_trails[l-1]=routed_trails[l-1]+1;
                   }
                       
            }
         }
   }
  
  int max_num = 0;
  for(int i=0;i<num_in_eachtrail;i++){
      if(routed_trails[i]>max_num){
        max_num = routed_trails[i];
       }
     }
  int min_dis = 5;
  span_distance.first = (max_num+1)*min_dis;
  cout<<span_distance.first<<endl;

  for(int i=0;i<Caps.size();i++){
      Caps[i].x = unit_cap_demension.first/2 +  Caps[i].index_x* (unit_cap_demension.first+span_distance.first);
     }
*/  

  string HV_via_metal;
  int HV_via_metal_index;

  if(H_metal_index>V_metal_index){
      HV_via_metal = V_metal;
      HV_via_metal_index = V_metal_index;
    }else{
      HV_via_metal = H_metal;
      HV_via_metal_index = H_metal_index;
    }

  for(int i=0;i<Caps.size();i++){
     Caps[i].access = 0;
  }

  //int min_dis = 500;
  pair<double,double> coord;
  pair<double,double> via_coord;
//for positive net
   //connection for trails
   //int min_dis =5;
   int num_trail = Nets_pos[0].line_v.size();
   int routed_trail=0;
   vector<int> trails;
   for(int i=0;i<num_trail;i++){trails.push_back(0);}
   for(int i=0;i<Nets_pos.size();i++){
      if(Nets_pos[i].cap_index.size()==0){continue;}
      routed_trail=routed_trail+1;
      pair<double,double> first_coord;
      pair<double,double> end_coord;
      int first_lock=0;
      int end_close=0;
      //Nets_pos[i].line_v_r=Nets_pos[i].line_v;
      for(int l=0;l<Nets_pos[i].line_v.size();l++){
          if(Nets_pos[i].line_v[l]==1){
              trails[l]=trails[l]+1;
              //connect to connection set and found the end point
              int max=-1;
              int max_cap_index;
              int left_right = 0;
              int found = 0;
              for(int k=0;k<Nets_pos[i].cap_index.size();k++){

                  if(Caps[Nets_pos[i].cap_index[k]].index_x==l and Caps[Nets_pos[i].cap_index[k]].access==0){
                      found = 1;
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting_x;
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting_y;
                      // via coverage???
                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                    
                      //
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x- unit_cap_demension.first/2-shifting_x-(span_distance.first-min_dis_x*trails[l]);
                      Caps[Nets_pos[i].cap_index[k]].access = 1;
            
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      Nets_pos[i].metal.push_back(H_metal);

                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);                     
                      //
                      //Nets_neg[i].line_v[l]=0;
                      //Nets_neg[i].line_v[l+1]=1;
                      
                      //
                      
                      //
                      if(Caps[Nets_pos[i].cap_index[k]].index_y>=max){
                         max=Caps[Nets_pos[i].cap_index[k]].index_y;
                         max_cap_index = Nets_pos[i].cap_index[k];
                         left_right = 0;
                        }
                    }else if(l-Caps[Nets_pos[i].cap_index[k]].index_x==1 and Caps[Nets_pos[i].cap_index[k]].access==0){
                      found = 1;
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting_x;
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting_y;
                      
                      //
                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                    
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting_y-min_dis_y;
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      Nets_pos[i].metal.push_back(V_metal);

                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting_x+(min_dis_x*trails[l]);
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      //
                      Nets_pos[i].metal.push_back(H_metal);

                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      Caps[Nets_pos[i].cap_index[k]].access = 1;
                      //Nets_neg[i].line_v[l]=0;
                      //Nets_neg[i].line_v[l-1]=1;
                      if(Caps[Nets_pos[i].cap_index[k]].index_y>max){
                         max=Caps[Nets_pos[i].cap_index[k]].index_y;
                         max_cap_index = Nets_pos[i].cap_index[k];
                         left_right = 1;
                        }
                    }
                 }
                 if(found == 0){
                 for(int k=0;k<Nets_pos[i].cap_index.size();k++){
                  if(0){
                     
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2;
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2;
                      //
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                      //
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x- unit_cap_demension.first/2-(span_distance.first-min_dis_x*trails[l]);
                      Caps[Nets_pos[i].cap_index[k]].access = 1;
                      //
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                      //
                      //Nets_neg[i].line_v[l]=0;
                      //Nets_neg[i].line_v[l+1]=1;
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      //
                      Nets_pos[i].metal.push_back("M2");
                      //
                      if(Caps[Nets_pos[i].cap_index[k]].index_y>=max){
                         max=Caps[Nets_pos[i].cap_index[k]].index_y;
                         max_cap_index = Nets_pos[i].cap_index[k];
                         left_right = 0;
                        }
                    }else if(l-Caps[Nets_pos[i].cap_index[k]].index_x==1){
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting_x;
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting_y;
                      
                      //
                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);

                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting_y-min_dis_y;
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      Nets_pos[i].metal.push_back(V_metal);
                      
                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);

                      //
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting_x+(min_dis_x*trails[l]);
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      //
                      Nets_pos[i].metal.push_back(H_metal);

                      addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      Caps[Nets_pos[i].cap_index[k]].access = 1;
                      //Nets_neg[i].line_v[l]=0;
                      //Nets_neg[i].line_v[l-1]=1;
                      if(Caps[Nets_pos[i].cap_index[k]].index_y>max){
                         max=Caps[Nets_pos[i].cap_index[k]].index_y;
                         max_cap_index = Nets_pos[i].cap_index[k];
                         left_right = 1;
                        }
                    }
                 }
                 }

////////////////////////////////////////////// start point 2019/6/1
                 //connect from start to end for each trail 
                 //coord.second = 0 - min_dis_y*routed_trail-2*min_dis_y+shifting_y; modify 1 yaguang 2019/6/24
                 coord.second = 0 - min_dis_y*routed_trail-2*min_dis_y-grid_offset;
                 addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,1);
                 
/*
                 Nets_pos[i].via.push_back(coord);
                 Nets_pos[i].via_metal.push_back("M1");
                 Nets_pos[i].via.push_back(coord);
                 Nets_pos[i].via_metal.push_back("M2");

                 via_coord.first = coord.first;
                 via_coord.second = coord.second - via_cover[0];
                 Nets_pos[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[0];
                 Nets_pos[i].end_conection_coord.push_back(via_coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 Nets_pos[i].metal.push_back("M1");
                      
                 via_coord.first = coord.first- via_cover[1];
                 via_coord.second = coord.second;
                 Nets_pos[i].start_conection_coord.push_back(via_coord);
                 via_coord.first = coord.first + via_cover[1];
                 Nets_pos[i].end_conection_coord.push_back(via_coord);
                 Nets_pos[i].Is_pin.push_back(1);
                 Nets_pos[i].metal.push_back("M2");
                      
                 via_coord.first = coord.first;
                 via_coord.second = coord.second- via_cover[2];
                 Nets_pos[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[2];
                 Nets_pos[i].end_conection_coord.push_back(via_coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 Nets_pos[i].metal.push_back("M3");
*/                 
                 Nets_pos[i].start_conection_coord.push_back(coord);
                 //
                 coord.second = -2*min_dis_y+shifting_y;
                 Nets_pos[i].end_conection_coord.push_back(coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 Nets_pos[i].metal.push_back(V_metal);
                 //

                 //addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,1);
/*
                 Nets_pos[i].via.push_back(coord);
                 Nets_pos[i].via_metal.push_back("M1");
                 Nets_pos[i].via.push_back(coord);
                 Nets_pos[i].via_metal.push_back("M2");

                 via_coord.first = coord.first;
                 via_coord.second = coord.second - via_cover[0];
                 Nets_pos[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[0];
                 Nets_pos[i].end_conection_coord.push_back(via_coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 Nets_pos[i].metal.push_back("M1");
                      
                 via_coord.first = coord.first- via_cover[1];
                 via_coord.second = coord.second;
                 Nets_pos[i].start_conection_coord.push_back(via_coord);
                 via_coord.first = coord.first + via_cover[1];
                 Nets_pos[i].end_conection_coord.push_back(via_coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 Nets_pos[i].metal.push_back("M2");
                      
                 via_coord.first = coord.first;
                 via_coord.second = coord.second- via_cover[2];
                 Nets_pos[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[2];
                 Nets_pos[i].end_conection_coord.push_back(via_coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 Nets_pos[i].metal.push_back("M3");
*/                
                 //
                 Nets_pos[i].start_conection_coord.push_back(coord);
                 coord.second = Caps[max_cap_index].y- unit_cap_demension.second/2-left_right*min_dis_y+shifting_y;
                 Nets_pos[i].end_conection_coord.push_back(coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 //
                 Nets_pos[i].metal.push_back(V_metal);
                 //
                 if(first_lock==0){
                    first_coord.first = coord.first;
                    //first_coord.second = 0 - min_dis_y*routed_trail-2*min_dis_y+shifting_y;
                    first_coord.second = 0 - min_dis_y*routed_trail-2*min_dis_y-grid_offset;
                    first_lock=1;
                 }else{
                    end_close=1;
                    end_coord.first = coord.first;;
                    //end_coord.second = 0 - min_dis_y*routed_trail-2*min_dis_y+shifting_y;
                    end_coord.second = 0 - min_dis_y*routed_trail-2*min_dis_y-grid_offset;
                 }
            }
         }
       //connect to each trail
       if(first_lock==1 and end_close==1){
       Nets_pos[i].start_conection_coord.push_back(first_coord);
       Nets_pos[i].end_conection_coord.push_back(end_coord);
       Nets_pos[i].Is_pin.push_back(1);
       //
       Nets_pos[i].metal.push_back(H_metal);
       //
       }    
   }
/*
  for(int i=0;i<Nets_pos.size();i++){
      //connection for each connection set
      for(int j=0;j<Nets_pos[i].Set.size();j++){
                 //cout<<i<<" "<<j<<" "<<Nets_pos[i].Set.size()<<endl;
          for(int k=0;k<Nets_pos[i].Set[j].cap_index.size();k++){
               for(int l=0;l<Nets_pos[i].Set[j].cap_index.size();l++){
                 //cout<<Nets_pos[i].Set[j].cap_index[k]<< " "<<Nets_pos[i].Set[j].cap_index[l]<<endl;
   if((Caps[Nets_pos[i].Set[j].cap_index[k]].index_x==Caps[Nets_pos[i].Set[j].cap_index[l]].index_x and Caps[Nets_pos[i].Set[j].cap_index[k]].index_y-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y ==1 and !(Caps[Nets_pos[i].Set[j].cap_index[k]].access and Caps[Nets_pos[i].Set[j].cap_index[l]].access)) or (Caps[Nets_pos[i].Set[j].cap_index[k]].index_y==Caps[Nets_pos[i].Set[j].cap_index[l]].index_y and Caps[Nets_pos[i].Set[j].cap_index[k]].index_x-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x ==1) and !(Caps[Nets_pos[i].Set[j].cap_index[k]].access and Caps[Nets_pos[i].Set[j].cap_index[l]].access)){
                       //cout<<"found"<<endl;
                       coord.first = Caps[Nets_pos[i].Set[j].cap_index[k]].x + unit_cap_demension.first/2;
                       coord.second = Caps[Nets_pos[i].Set[j].cap_index[k]].y - unit_cap_demension.second/2;
                       Nets_pos[i].start_conection_coord.push_back(coord);
                       //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;
                       coord.first = Caps[Nets_pos[i].Set[j].cap_index[l]].x + unit_cap_demension.first/2;
                       coord.second = Caps[Nets_pos[i].Set[j].cap_index[l]].y - unit_cap_demension.second/2;
                       Nets_pos[i].end_conection_coord.push_back(coord);
                       //Caps[Nets_pos[i].Set[j].cap_index[l]].access = 1;
                     }
                  }
             }
         }
     }
*/
    for(int i=0;i<Nets_pos.size();i++){
      //connection for each connection set
      for(int j=0;j<Nets_pos[i].Set.size();j++){
              int end_flag = Nets_pos[i].Set[j].cap_index.size();
              int index = 0;
              while(index<end_flag){
                     if(Caps[Nets_pos[i].Set[j].cap_index[index]].access==1){
                        int found=0;
                        for(int k=0;k<end_flag;k++){
                            if((Caps[Nets_pos[i].Set[j].cap_index[k]].index_y==Caps[Nets_pos[i].Set[j].cap_index[index]].index_y and abs(Caps[Nets_pos[i].Set[j].cap_index[k]].index_x-Caps[Nets_pos[i].Set[j].cap_index[index]].index_x) ==1)and !(Caps[Nets_pos[i].Set[j].cap_index[k]].access)){
                              Caps[Nets_pos[i].Set[j].cap_index[k]].access=1;
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[k]].x + unit_cap_demension.first/2-shifting_x;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[k]].y - unit_cap_demension.second/2+shifting_y;  
                              
                              //
                              addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                              

                              //
                              Nets_pos[i].start_conection_coord.push_back(coord);
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[index]].x + unit_cap_demension.first/2-shifting_x;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[index]].y - unit_cap_demension.second/2+shifting_y;
                              Nets_pos[i].end_conection_coord.push_back(coord);
                              Nets_pos[i].Is_pin.push_back(0);
                              Nets_pos[i].metal.push_back(H_metal);
                              //

                              addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                              
                              //
                              index = 0;
                              found = 1;
                             }else if((Caps[Nets_pos[i].Set[j].cap_index[k]].index_x==Caps[Nets_pos[i].Set[j].cap_index[index]].index_x and abs(Caps[Nets_pos[i].Set[j].cap_index[k]].index_y-Caps[Nets_pos[i].Set[j].cap_index[index]].index_y) ==1) and !(Caps[Nets_pos[i].Set[j].cap_index[k]].access)){
                              Caps[Nets_pos[i].Set[j].cap_index[k]].access=1;
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[k]].x + unit_cap_demension.first/2-shifting_x;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[k]].y - unit_cap_demension.second/2+shifting_y;  
                              addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                              //
/*
                              Nets_pos[i].via.push_back(coord);
                              Nets_pos[i].via_metal.push_back("M1");
                              Nets_pos[i].via.push_back(coord);
                              Nets_pos[i].via_metal.push_back("M2");

                              via_coord.first = coord.first;
                              via_coord.second = coord.second - via_cover[0];
                              Nets_pos[i].start_conection_coord.push_back(via_coord);
                              via_coord.second = coord.second + via_cover[0];
                              Nets_pos[i].end_conection_coord.push_back(via_coord);
                              Nets_pos[i].Is_pin.push_back(0);
                              Nets_pos[i].metal.push_back("M1");
                      
                              via_coord.first = coord.first- via_cover[1];
                              via_coord.second = coord.second;
                              Nets_pos[i].start_conection_coord.push_back(via_coord);
                              via_coord.first = coord.first + via_cover[1];
                              Nets_pos[i].end_conection_coord.push_back(via_coord);
                              Nets_pos[i].Is_pin.push_back(0);
                              Nets_pos[i].metal.push_back("M2");
                              
                              via_coord.first = coord.first;
                              via_coord.second = coord.second - via_cover[2];
                              Nets_pos[i].start_conection_coord.push_back(via_coord);
                              via_coord.second = coord.second + via_cover[2];
                              Nets_pos[i].end_conection_coord.push_back(via_coord);
                              Nets_pos[i].Is_pin.push_back(0);
                              Nets_pos[i].metal.push_back("M3");
*/                              
                              //
                              Nets_pos[i].start_conection_coord.push_back(coord);
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[index]].x + unit_cap_demension.first/2-shifting_x;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[index]].y - unit_cap_demension.second/2+shifting_y;
                              Nets_pos[i].end_conection_coord.push_back(coord);
                              Nets_pos[i].Is_pin.push_back(0);
                              Nets_pos[i].metal.push_back(V_metal);
                              //
                              addVia(Nets_pos[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                              
                    
                              
                              
                              //
                              index = 0;
                              found = 1;
                             }
                           }
                           if(found==0){
                              index = index +1;
                             }
                       }else{
                        index=index+1;
                       }
                   }
              }
         }
     

//for negative net
  for(int i=0;i<Caps.size();i++){
     Caps[i].access = 0;
  }
   //connection for trails
   //int num_trail = Nets_pos[0].line_v.size();
   routed_trail=0;
   //vector<int> trails;
   //for(int i=0;i<num_trail;i++){trails.push_back(0);}
   for(int i=0;i<Nets_neg.size();i++){
      if(Nets_neg[i].cap_index.size()==0){continue;}
      routed_trail=routed_trail+1;
      pair<double,double> first_coord;
      pair<double,double> end_coord;
      int first_lock=0;
      int end_close=0;
      //Nets_neg[i].line_v_r=Nets_pos[i].line_v;
      for(int l=0;l<Nets_neg[i].line_v.size();l++){
          if(Nets_neg[i].line_v[l]==1){
              trails[l]=trails[l]+1;
              //connect to connection set and found the end point
              int min=Caps.size();
              int min_cap_index;
              int left_right = 0;
              int found = 0;
              for(int k=0;k<Nets_neg[i].cap_index.size();k++){
                  if(Caps[Nets_neg[i].cap_index[k]].index_x==l and Caps[Nets_neg[i].cap_index[k]].access==0){
                      found = 1;
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2+shifting_x;
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2-shifting_y;
                      
                      //
                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      

                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2 + shifting_x-(span_distance.first-min_dis_x*trails[l]);
                      Caps[Nets_neg[i].cap_index[k]].access = 1;
                      //
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      //
                      Nets_neg[i].metal.push_back(H_metal);

                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      //Nets_neg[i].line_v_r[k]=0;
                      //Nets_neg[i].line_v_r[k+1]=1;
                      
                      //
                      if(Caps[Nets_neg[i].cap_index[k]].index_y<=min){
                         min=Caps[Nets_neg[i].cap_index[k]].index_y;
                         min_cap_index = Nets_neg[i].cap_index[k];
                         left_right = 0;
                        }
                    }else if(l-Caps[Nets_neg[i].cap_index[k]].index_x==1 and Caps[Nets_neg[i].cap_index[k]].access==0){
                      found = 1;
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2+shifting_x;
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2-shifting_y;
                      
                      //
                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2+min_dis_y-shifting_y;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back(V_metal);
                      //
                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x+ unit_cap_demension.first/2+(min_dis_x*trails[l])+shifting_x;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back(H_metal);
                      //
                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);

                      
                      
                      
                      //
                      Caps[Nets_neg[i].cap_index[k]].access = 1;
                      //Nets_neg[i].line_v_r[k]=0;
                      //Nets_neg[i].line_v_r[k-1]=1;
                      if(Caps[Nets_neg[i].cap_index[k]].index_y<min){
                         min=Caps[Nets_neg[i].cap_index[k]].index_y;
                         min_cap_index = Nets_neg[i].cap_index[k];
                         left_right = 1;
                        }
                    }
                 }
                 if(found == 0){
                 for(int k=0;k<Nets_neg[i].cap_index.size();k++){
                  if(0){
                      
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2;
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2;
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
                      //
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2-(span_distance.first-min_dis_x*trails[l]);
                      Caps[Nets_neg[i].cap_index[k]].access = 1;
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
                      //
                      //Nets_neg[i].line_v_r[k]=0;
                      //Nets_neg[i].line_v_r[k+1]=1;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      //
                      Nets_neg[i].metal.push_back("M2");
                      //
                      if(Caps[Nets_neg[i].cap_index[k]].index_y<=min){
                         min=Caps[Nets_neg[i].cap_index[k]].index_y;
                         min_cap_index = Nets_neg[i].cap_index[k];
                         left_right = 0;
                        }
                    }else if(l-Caps[Nets_neg[i].cap_index[k]].index_x==1){
                      
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2+shifting_x;
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2-shifting_y;
                      
                      //
                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2+min_dis_y-shifting_y;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back(V_metal);
                      //
                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x+ unit_cap_demension.first/2+(min_dis_x*trails[l])+shifting_x;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back(H_metal);
                      //
                      addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      //
                      Caps[Nets_neg[i].cap_index[k]].access = 1;
                      //Nets_neg[i].line_v_r[k]=0;
                      //Nets_neg[i].line_v_r[k-1]=1;
                      if(Caps[Nets_neg[i].cap_index[k]].index_y<min){
                         min=Caps[Nets_neg[i].cap_index[k]].index_y;
                         min_cap_index = Nets_neg[i].cap_index[k];
                         left_right = 1;
                        }
                    }
                 }
                 }
                 //connect from start to end for each trail 
                 int num_cap = Caps.size();
                 //coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis_y*routed_trail+2*min_dis_y-shifting_y;//modify 2, 2019/6/24
                 coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis_y*routed_trail+2*min_dis_y + grid_offset;
                 addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,1);
                 //
/*
                 Nets_neg[i].via.push_back(coord);
                 Nets_neg[i].via_metal.push_back("M1");
                 Nets_neg[i].via.push_back(coord);
                 Nets_neg[i].via_metal.push_back("M2");
                 via_coord.first = coord.first;
                 via_coord.second = coord.second - via_cover[0];
                 Nets_neg[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[0];
                 Nets_neg[i].end_conection_coord.push_back(via_coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back("M1");
                      
                 via_coord.first = coord.first- via_cover[1];
                 via_coord.second = coord.second;
                 Nets_neg[i].start_conection_coord.push_back(via_coord);
                 via_coord.first = coord.first + via_cover[1];
                 Nets_neg[i].end_conection_coord.push_back(via_coord);
                 Nets_neg[i].Is_pin.push_back(1);
                 Nets_neg[i].metal.push_back("M2");
                      
                 via_coord.first = coord.first;
                 via_coord.second = coord.second- via_cover[2];
                 Nets_neg[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[2];
                 Nets_neg[i].end_conection_coord.push_back(via_coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back("M3");
                 //
*/
                 Nets_neg[i].start_conection_coord.push_back(coord);
                 coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2+2*min_dis_y-shifting_y;
                 Nets_neg[i].end_conection_coord.push_back(coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back(V_metal);
                 //addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                 //
/*
                 Nets_neg[i].via.push_back(coord);
                 Nets_neg[i].via_metal.push_back("M1");
                 Nets_neg[i].via.push_back(coord);
                 Nets_neg[i].via_metal.push_back("M2");
                 
                 via_coord.first = coord.first;
                 via_coord.second = coord.second - via_cover[0];
                 Nets_neg[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[0];
                 Nets_neg[i].end_conection_coord.push_back(via_coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back("M1");
                      
                 via_coord.first = coord.first- via_cover[1];
                 via_coord.second = coord.second;
                 Nets_neg[i].start_conection_coord.push_back(via_coord);
                 via_coord.first = coord.first + via_cover[1];
                 Nets_neg[i].end_conection_coord.push_back(via_coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back("M2");
                      
                 via_coord.first = coord.first;
                 via_coord.second = coord.second- via_cover[2];
                 Nets_neg[i].start_conection_coord.push_back(via_coord);
                 via_coord.second = coord.second + via_cover[2];
                 Nets_neg[i].end_conection_coord.push_back(via_coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back("M3");
                 
                 //
*/
                 Nets_neg[i].start_conection_coord.push_back(coord);
                 coord.second = Caps[min_cap_index].y+ unit_cap_demension.second/2+left_right*min_dis_y-shifting_y;
                 Nets_neg[i].end_conection_coord.push_back(coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back(V_metal);
                 if(first_lock==0){
                    first_coord.first = coord.first;
                    //first_coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis_y*routed_trail+2*min_dis_y-shifting_y;
                    first_coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis_y*routed_trail+2*min_dis_y+grid_offset;
                    first_lock=1;
                 }else{
                    end_close=1;
                    end_coord.first = coord.first;
                    //end_coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis_y*routed_trail+2*min_dis_y-shifting_y;
                    end_coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis_y*routed_trail+2*min_dis_y+grid_offset;
                 }
            }
         }
       //connect to each trail
       if(first_lock==1 and end_close==1){
       Nets_neg[i].start_conection_coord.push_back(first_coord);
       Nets_neg[i].end_conection_coord.push_back(end_coord);
       Nets_neg[i].Is_pin.push_back(1);
       //
       Nets_neg[i].metal.push_back(H_metal);
       //
       
       }    
   }
/*
  for(int i=0;i<Nets_neg.size();i++){
      //connection for each connection set
      for(int j=0;j<Nets_neg[i].Set.size();j++){
                 //cout<<i<<" "<<j<<" "<<Nets_pos[i].Set.size()<<endl;
          for(int k=0;k<Nets_neg[i].Set[j].cap_index.size();k++){
               for(int l=0;l<Nets_neg[i].Set[j].cap_index.size();l++){
                 //cout<<Nets_pos[i].Set[j].cap_index[k]<< " "<<Nets_pos[i].Set[j].cap_index[l]<<endl;
   if((Caps[Nets_neg[i].Set[j].cap_index[k]].index_x==Caps[Nets_neg[i].Set[j].cap_index[l]].index_x and Caps[Nets_neg[i].Set[j].cap_index[k]].index_y-Caps[Nets_neg[i].Set[j].cap_index[l]].index_y ==1 and !(Caps[Nets_neg[i].Set[j].cap_index[k]].access and Caps[Nets_neg[i].Set[j].cap_index[l]].access)) or (Caps[Nets_neg[i].Set[j].cap_index[k]].index_y==Caps[Nets_neg[i].Set[j].cap_index[l]].index_y and Caps[Nets_neg[i].Set[j].cap_index[k]].index_x-Caps[Nets_neg[i].Set[j].cap_index[l]].index_x ==1) and !(Caps[Nets_neg[i].Set[j].cap_index[k]].access and Caps[Nets_neg[i].Set[j].cap_index[l]].access)){
                       //cout<<"found"<<endl;
                       coord.first = Caps[Nets_neg[i].Set[j].cap_index[k]].x - unit_cap_demension.first/2;
                       coord.second = Caps[Nets_neg[i].Set[j].cap_index[k]].y + unit_cap_demension.second/2;
                       Nets_neg[i].start_conection_coord.push_back(coord);
                       //Caps[Nets_neg[i].Set[j].cap_index[k]].access = 1;
                       coord.first = Caps[Nets_neg[i].Set[j].cap_index[l]].x - unit_cap_demension.first/2;
                       coord.second = Caps[Nets_neg[i].Set[j].cap_index[l]].y + unit_cap_demension.second/2;
                       Nets_neg[i].end_conection_coord.push_back(coord);
                       //Caps[Nets_neg[i].Set[j].cap_index[l]].access = 1;
                     }
                  }
             }
         }
     }
*/
  for(int i=0;i<Nets_neg.size();i++){
      //connection for each connection set
      for(int j=0;j<Nets_neg[i].Set.size();j++){
              int end_flag = Nets_neg[i].Set[j].cap_index.size();
              int index = 0;
              while(index<end_flag){
                     if(Caps[Nets_neg[i].Set[j].cap_index[index]].access==1){
                        int found=0;
                        for(int k=0;k<end_flag;k++){
                            if((Caps[Nets_neg[i].Set[j].cap_index[k]].index_y==Caps[Nets_neg[i].Set[j].cap_index[index]].index_y and abs(Caps[Nets_neg[i].Set[j].cap_index[k]].index_x-Caps[Nets_neg[i].Set[j].cap_index[index]].index_x) ==1 and !(Caps[Nets_neg[i].Set[j].cap_index[k]].access))){
                              Caps[Nets_neg[i].Set[j].cap_index[k]].access=1;
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[k]].x - unit_cap_demension.first/2+shifting_x;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[k]].y + unit_cap_demension.second/2-shifting_y;  
                             
                              //
                              addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);

                      
                              
                              //Nets_neg[i].via.push_back(coord);
                              //Nets_neg[i].via_metal.push_back("M2");
                              //
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;

                              Nets_neg[i].start_conection_coord.push_back(coord);
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[index]].x - unit_cap_demension.first/2+shifting_x;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[index]].y + unit_cap_demension.second/2-shifting_y;
                              Nets_neg[i].end_conection_coord.push_back(coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back(H_metal);
                              //
                              addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                      
                      
                              //Nets_neg[i].via.push_back(coord);
                              //Nets_neg[i].via_metal.push_back("M2");
                              
                              //
                              index = 0;
                              found = 1;
                             }else if((Caps[Nets_neg[i].Set[j].cap_index[k]].index_x==Caps[Nets_neg[i].Set[j].cap_index[index]].index_x and abs(Caps[Nets_neg[i].Set[j].cap_index[k]].index_y-Caps[Nets_neg[i].Set[j].cap_index[index]].index_y) ==1 and !(Caps[Nets_neg[i].Set[j].cap_index[k]].access))){
                              Caps[Nets_neg[i].Set[j].cap_index[k]].access=1;
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[k]].x - unit_cap_demension.first/2+shifting_x;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[k]].y + unit_cap_demension.second/2-shifting_y;  
                              addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                              //
/*
                              Nets_neg[i].via.push_back(coord);
                              Nets_neg[i].via_metal.push_back("M1");
                              Nets_neg[i].via.push_back(coord);
                              Nets_neg[i].via_metal.push_back("M2");
                              via_coord.first = coord.first;
                              via_coord.second = coord.second - via_cover[0];
                              Nets_neg[i].start_conection_coord.push_back(via_coord);
                              via_coord.second = coord.second + via_cover[0];
                              Nets_neg[i].end_conection_coord.push_back(via_coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back("M1");
                      
                              via_coord.first = coord.first- via_cover[1];
                              via_coord.second = coord.second;
                              Nets_neg[i].start_conection_coord.push_back(via_coord);
                              via_coord.first = coord.first + via_cover[1];
                              Nets_neg[i].end_conection_coord.push_back(via_coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back("M2");
                              
                              via_coord.first = coord.first;
                              via_coord.second = coord.second - via_cover[2];
                              Nets_neg[i].start_conection_coord.push_back(via_coord);
                              via_coord.second = coord.second + via_cover[2];
                              Nets_neg[i].end_conection_coord.push_back(via_coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back("M3");
*/                              
                              //Nets_neg[i].via.push_back(coord);
                              //Nets_neg[i].via_metal.push_back("M2");
                              //
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;
                              Nets_neg[i].start_conection_coord.push_back(coord);
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[index]].x - unit_cap_demension.first/2+shifting_x;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[index]].y + unit_cap_demension.second/2-shifting_y;
                              Nets_neg[i].end_conection_coord.push_back(coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back(V_metal);
                              //
                              addVia(Nets_neg[i],coord,drc_info,HV_via_metal,HV_via_metal_index,0);
                   
                              //Nets_neg[i].via.push_back(coord);
                              //Nets_neg[i].via_metal.push_back("M2");
                              
                              //
                              index = 0;
                              found = 1;
                             }
                           }
                           if(found==0){
                              index = index +1;
                             }
                       }else{
                        index=index+1;
                       }
                   }
              }
         }

}

extern
void JSONReaderWrite_subcells (string GDSData, long int& rndnum,
			       vector<string>& strBlocks, vector<int>& llx, vector<int>& lly,
			       vector<int>& urx, vector<int>& ury, json& mjsonStrAry);

extern
void JSONExtractUit (string GDSData, int& unit);

extern 
void addOABoundaries (json& jsonElements, int width, int height);

void
Placer_Router_Cap::fillPathBoundingBox (int *x, int* y,
					pair<double,double> &start,
					pair<double,double> &end,
					double width) {
    if (start.first == end.first) {
	// NO offset for Failure2
	if (start.second < end.second) {
	    x[0] = start.first - width + offset_x;
	    x[1] = end.first - width + offset_x;
	    x[2] = end.first + width + offset_x;
	    x[3] = start.first + width +offset_x;
	    x[4] = x[0];
             
	    y[0] = start.second + offset_y;
	    y[1] = end.second + offset_y;
	    y[2] = end.second + offset_y;
	    y[3] = start.second + offset_y;
	    y[4] = y[0];
	} else {
	    x[0] = end.first - width + offset_x;
	    x[1] = start.first - width + offset_x;
	    x[2] = start.first + width + offset_x;
	    x[3] = end.first + width + offset_x;
	    x[4] = x[0];
             
	    y[0] = end.second + offset_y;
	    y[1] = start.second + offset_y;
	    y[2] = start.second + offset_y;
	    y[3] = end.second + offset_y;
	    y[4] = y[0];
	}
    } else {
	if (start.first < end.first){
	    x[0] = start.first + offset_x;
	    x[1] = start.first + offset_x;
	    x[2] = end.first + offset_x;
	    x[3] = end.first + offset_x;
	    x[4] = x[0];
             
	    y[0] = start.second - width + offset_y;
	    y[1] = start.second + width + offset_y;
	    y[2] = end.second + width + offset_y;
	    y[3] = end.second - width + offset_y;
	    y[4] = y[0];

	} else {
	    x[0] = end.first + offset_x;
	    x[1] = end.first + offset_x;
	    x[2] = start.first + offset_x;
	    x[3] = start.first + offset_x;
	    x[4] = x[0];
             
	    y[0] = end.second - width + offset_y;
	    y[1] = end.second + width + offset_y;
	    y[2] = start.second + width + offset_y;
	    y[3] = start.second - width + offset_y;
	    y[4] = y[0];
	}
    }
}

void
Placer_Router_Cap::WriteJSON (string fpath, string unit_capacitor, string final_gds, PnRDB::Drc_info & drc_info, string opath) {
    //begin to write JSON file from unit capacitor to final capacitor file
    string gds_unit_capacitor = fpath+"/"+unit_capacitor+".gds";
    string topGDS_loc = opath+final_gds+".gds";
    string TopCellName = final_gds;
    int unitScale=2;
    JSONExtractUit (gds_unit_capacitor, unitScale);
    std::cout<<"Cap unitScale "<<unitScale<<std::endl;

    std::ofstream jsonStream;
    jsonStream.open (topGDS_loc + ".json");
    json jsonTop;

    jsonTop["header"] = 600;
    json jsonLibAry = json::array();
    json jsonLib;
    jsonLib["time"] = JSON_TimeTime();
    // DAK Overwrite to match
    jsonLib["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
    double dbUnitUser=2*0.00025/unitScale;
    double dbUnitMeter=dbUnitUser/1e6;
    jsonLib["units"] = {dbUnitUser, dbUnitMeter};
    jsonLib["libname"] = "test";

    long int randnum = 111;
    //what is this
    vector<string> uniGDS;
    for(int i=0;i<1;i++){
	uniGDS.push_back(gds_unit_capacitor);
    }

    json jsonStrAry = json::array();

    vector<string> strBlocks;
    vector<int> llx, lly, urx, ury;
    map<string,int> gdsMap2strBlock;
    long int rndnum=111;
    vector<string> strBlocks_Top;
    int idx=0;
    //writing unit capacitors??? confirm with jinhyun
    std::cout << "GDS CAP SUBCELL read of " << gds_unit_capacitor << std::endl;

    for(int i=0;i<uniGDS.size();i++) {
	json js;
	cout << "CAP GDS: Using JSON for subcells for now" << endl;
	JSONReaderWrite_subcells (gds_unit_capacitor, rndnum, strBlocks, llx,lly,urx,ury, js);
	for (json::iterator str = js.begin(); str != js.end(); ++str) {
	    jsonStrAry.push_back (*str);
	}

	if (strBlocks.size())
	    strBlocks_Top.push_back(strBlocks.back());
	else
	    std::cout << "ERROR: NO blocks returned from parsing " << gds_unit_capacitor << endl;
	gdsMap2strBlock.insert(make_pair(gds_unit_capacitor,idx));
	idx++;
    }
    //writing metals
    int x[5], y[5];

    json jsonStr;
    jsonLib["time"] = JSON_TimeTime();
    // DAK: Hack to match
    jsonStr["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
    jsonStr["strname"] = TopCellName.c_str();
    json jsonElements = json::array();

    //int width = metal_width[0];
    int Min_x = INT_MAX;
    int Min_y = INT_MAX;
    int Max_x = INT_MIN;
    int Max_y = INT_MIN;
    //for positive nets

    for(int i=0; i< Nets_pos.size(); i++){//for each net
	for(int j=0; j< Nets_pos[i].start_conection_coord.size();j++){ //for segment

            int width = drc_info.Metal_info[drc_info.Metalmap[Nets_pos[i].metal[j]]].width/2;
	    fillPathBoundingBox (x, y, Nets_pos[i].start_conection_coord[j],
				 Nets_pos[i].end_conection_coord[j], width);
            
	    if(x[0]<Min_x) {Min_x = x[0];}
	    if(x[2]>Max_x) {Max_x = x[2];}
	    if(y[0]<Min_y) {Min_y = y[0];}
	    if(y[2]>Max_y) {Max_y = y[2];}

	    for (int i = 0; i < 5; i++) {
		x[i] *= unitScale;
		y[i] *= unitScale;
	    }

	    json bound;
	    bound["type"] = "boundary";
	    bound["datatype"] = 0;
	    json xy = json::array();
	    for (size_t i = 0; i < 5; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    bound["xy"] = xy;
	    bound["layer"] = getLayerMask (Nets_pos[i].metal[j], drc_info);
	    jsonElements.push_back (bound);
	}   
    }
  
    //for neg nets
    for(int i =0; i < Nets_neg.size(); i++) {//for each net
	for(int j = 0; j < Nets_neg[i].start_conection_coord.size(); j++) { //for segment
            int width = drc_info.Metal_info[drc_info.Metalmap[Nets_neg[i].metal[j]]].width/2;
	    fillPathBoundingBox (x, y, Nets_neg[i].start_conection_coord[j],
				 Nets_neg[i].end_conection_coord[j], width);

	    if(x[0]<Min_x) Min_x = x[0];
	    if(x[2]>Max_x) Max_x = x[2];
	    if(y[0]<Min_y) Min_y = y[0];
	    if(y[2]>Max_y) Max_y = y[2];

	    for (int i = 0; i < 5; i++) {
		x[i] *= unitScale;
		y[i] *= unitScale;
	    }

	    json bound;
	    bound["type"] = "boundary";
	    bound["datatype"] = 0;
	    json xy = json::array();
	    for (size_t i = 0; i < 5; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    bound["xy"] = xy;
	    bound["layer"] = getLayerMask (Nets_neg[i].metal[j], drc_info);
	    jsonElements.push_back (bound);
	}
    }
  
    //wirting vias
    //for positive net
    //width = via_width[0];
    for (int i = 0; i < Nets_pos.size(); i++) {
	for (int j = 0; j < Nets_pos[i].via.size(); j++) {//the size of via needs to be modified according to different PDK
            int width = drc_info.Via_model[drc_info.Metalmap[Nets_pos[i].via_metal[j]]].ViaRect[1].x;
 	    x[0]=Nets_pos[i].via[j].first - width+offset_x;
	    x[1]=Nets_pos[i].via[j].first - width+offset_x;
	    x[2]=Nets_pos[i].via[j].first + width+offset_x;
	    x[3]=Nets_pos[i].via[j].first + width+offset_x;
	    x[4]=x[0];
            width = drc_info.Via_model[drc_info.Metalmap[Nets_pos[i].via_metal[j]]].ViaRect[1].y;        
	    y[0]=Nets_pos[i].via[j].second - width+offset_y;
	    y[1]=Nets_pos[i].via[j].second + width+offset_y;
	    y[2]=Nets_pos[i].via[j].second + width+offset_y;
	    y[3]=Nets_pos[i].via[j].second - width+offset_y;
	    y[4]=y[0];
        
	    if (x[0]<Min_x) {Min_x = x[0];}
	    if (x[2]>Max_x) {Max_x = x[2];}
	    if (y[0]<Min_y) {Min_y = y[0];}
	    if (y[2]>Max_y) {Max_y = y[2];}

	    for (int i = 0; i < 5; i++) {
		x[i] *= unitScale;
		y[i] *= unitScale;
	    }
    
	    json bound;
	    bound["type"] = "boundary";
	    bound["datatype"] = 0;
	    json xy = json::array();
	    for (size_t i = 0; i < 5; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    bound["xy"] = xy;
	    bound["layer"] = getLayerViaMask (Nets_pos[i].via_metal[j], drc_info);
	    jsonElements.push_back (bound);
	}
    }
    
    //for negative net
    for (int i = 0; i < Nets_neg.size(); i++) {
	for (int j = 0; j < Nets_neg[i].via.size(); j++) {//the size of via needs to be modified according to different PDK
            int width = drc_info.Via_model[drc_info.Metalmap[Nets_neg[i].via_metal[j]]].ViaRect[1].x; 
	    x[0]=Nets_neg[i].via[j].first - width+offset_x;
	    x[1]=Nets_neg[i].via[j].first - width+offset_x;
	    x[2]=Nets_neg[i].via[j].first + width+offset_x;
	    x[3]=Nets_neg[i].via[j].first + width+offset_x;
	    x[4]=x[0];
            width = drc_info.Via_model[drc_info.Metalmap[Nets_neg[i].via_metal[j]]].ViaRect[1].y;        
	    y[0]=Nets_neg[i].via[j].second - width+offset_y;
	    y[1]=Nets_neg[i].via[j].second + width+offset_y;
	    y[2]=Nets_neg[i].via[j].second + width+offset_y;
	    y[3]=Nets_neg[i].via[j].second - width+offset_y;
	    y[4]=y[0];
        
	    if (x[0]<Min_x) Min_x = x[0];
	    if (x[2]>Max_x) Max_x = x[2];
	    if (y[0]<Min_y) Min_y = y[0];
	    if (y[2]>Max_y) Max_y = y[2];

	    for (int i = 0; i < 5; i++) {
		x[i] *= unitScale;
		y[i] *= unitScale;
	    }

	    json bound;
	    bound["type"] = "boundary";
	    bound["datatype"] = 0;
	    json xy = json::array();
	    for (size_t i = 0; i < 5; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    bound["xy"] = xy;
	    bound["layer"] = getLayerViaMask (Nets_neg[i].via_metal[j], drc_info);
	    jsonElements.push_back (bound);
	}
    }
  
    //wirte orientation for each cap
    for (int i = 0; i < Caps.size(); i++) {
	json sref;
	sref["type"] = "sref";
	if (strBlocks_Top.size())
	    sref["sname"] = strBlocks_Top[0].c_str();
	else
	    cout << "ERROR: no block found to output from subcells" << endl;
	sref["strans"] = 0;
	sref["angle"] = 0.0;
	x[0] = unitScale*(Caps[i].x-unit_cap_demension.first/2+offset_x);
	y[0] = unitScale*(Caps[i].y-unit_cap_demension.second/2+offset_y);
     
	json xy = json::array();
	xy.push_back (x[0]);
	xy.push_back (y[0]);
	sref["xy"] = xy;
	jsonElements.push_back (sref);
    }

    addOABoundaries(jsonElements, unitScale * CheckOutBlock.width, unitScale * CheckOutBlock.height);
    jsonStr["elements"] = jsonElements;
    jsonStrAry.push_back (jsonStr);
    jsonLib["bgnstr"] = jsonStrAry;

    jsonLibAry.push_back(jsonLib);
    jsonTop["bgnlib"] = jsonLibAry;
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    std::cout << "CAP GDS JSON FINALIZE " <<  unit_capacitor << std::endl;
}

void Placer_Router_Cap::Common_centroid_capacitor_aspect_ratio(string opath, string fpath, PnRDB::hierNode& current_node, PnRDB::Drc_info & drc_info, map<string, PnRDB::lefMacro> lefData, bool dummy_flag, bool aspect_ratio, int num_aspect){ //if aspect_ratio 1, then do CC with different aspect_ratio; Else not.


  for(int i = 0;i<current_node.Blocks.size();i++){
       if(current_node.Blocks[i].instance.back().isLeaf == 1 and current_node.Blocks[i].instance.back().gdsFile ==""){
            //this block must be CC
            vector<int> ki;
            vector<pair<string, string> > pin_names;
            string unit_capacitor;
            string final_gds;
            pair<string, string> pins;
            for(int j=0;j<current_node.CC_Caps.size();j++){

                 std::cout<<"New CC 1 "<<j<<std::endl;
                 if(current_node.CC_Caps[j].CCCap_name == current_node.Blocks[i].instance.back().name){
                      ki = current_node.CC_Caps[j].size;
                      unit_capacitor = current_node.CC_Caps[j].Unit_capacitor;
                      final_gds = current_node.Blocks[i].instance.back().master;
                      int pin_index = 0;
                      while(pin_index <current_node.Blocks[i].instance.back().blockPins.size()){
                         pins.first = current_node.Blocks[i].instance.back().blockPins[pin_index].name;
                         pins.second = current_node.Blocks[i].instance.back().blockPins[pin_index+1].name;
                         pin_names.push_back(pins);
                         pin_index = pin_index + 2;
                      }
                      bool cap_ratio = current_node.CC_Caps[j].cap_ratio;
                      std::cout<<"New CC 2 "<<j<<std::endl;
                      vector<int> cap_r;
                      vector<int> cap_s;
                      if(cap_ratio){                        
                      cap_r.push_back(current_node.CC_Caps[j].cap_r);
                      cap_s.push_back(current_node.CC_Caps[j].cap_s);
                      }else{
                      //cap_r.push_back(0);
                      //cap_s.push_back(0);                      
                      }

                      std::cout<<"New CC 3 "<<j<<std::endl;
                      if(aspect_ratio){
                         int sum = 0;
                         double temp_r = 0;
                         //double temp_s = 0;
                         for(int k=0;k<ki.size();k++){
                               sum = sum+ ki[k];
                             }
                         temp_r = ceil(sqrt(sum));
                         //temp_s = ceil(sum/temp_r); 
                         int aspect_num = num_aspect;
                         while(aspect_num > 0 and temp_r > 0){
                                double temp_s = ceil(sum/temp_r);
                                cap_r.push_back(temp_r);
                                cap_s.push_back(temp_s);
                                aspect_num = aspect_num - 1;
                                temp_r = temp_r - 1;
                               }
                                                  
                         }
                      //increase other aspect ratio
                      std::cout<<"New CC 4 "<<j<<std::endl;
                      //std::vector<PnRDB::block> temp_Block;
                      std::cout<<"cap_r size "<<cap_r.size()<<std::endl;
                      for(int q=0;q<cap_r.size();q++){
                        std::cout<<"New CC 5 "<<j<<std::endl;
                        //stringstream cr,cs;
                        //cr<<cap_r[q]; 
                        //cs<<cap_s[q];
                        std::cout<<"New CC 6 "<<j<<std::endl;
                        //string cr_string = cr.str();
                        //string cs_string = cs.str();
                        std::cout<<"New CC 7 "<<j<<std::endl;
                        std::string cc_gds_file = final_gds+"_AspectRatio_"+to_string(cap_r[q])+"x"+to_string(cap_s[q]);
   
                        
                        std::cout<<"StartClean New CC"<<std::endl;
                        std::cout<<"q "<<q<<" cap_r[q] "<<cap_r[q]<<" cap_s[q] "<<cap_s[q]<<std::endl;
                        Placer_Router_Cap_clean();
                        std::cout<<"End Clean New CC"<<std::endl;

                        std::cout<<"Start New CC"<<std::endl;
                        Placer_Router_Cap_function(ki, pin_names, fpath, unit_capacitor, cc_gds_file, cap_ratio or aspect_ratio, cap_r[q], cap_s[q], drc_info, lefData, dummy_flag, opath);
                        std::cout<<"End New CC"<<std::endl;
                        PnRDB::block temp_block=CheckoutData();
                        //delete PRC;
                        

                        
                        //std::cout<<"Start feed blocks"<<std::endl;
                        if(q==0){
                        //feedback data
                            std::cout<<"Start feed blocks"<<std::endl;
                            current_node.Blocks[i].instance[q].width = temp_block.width;
                            current_node.Blocks[i].instance[q].height = temp_block.height;
                            current_node.Blocks[i].instance[q].originBox = temp_block.originBox;
                            current_node.Blocks[i].instance[q].originCenter = temp_block.originCenter;
                            current_node.Blocks[i].instance[q].gdsFile = temp_block.gdsFile;
                            current_node.Blocks[i].instance[q].orient = temp_block.orient;
                            current_node.Blocks[i].instance[q].interMetals = temp_block.interMetals;
                            current_node.Blocks[i].instance[q].interVias = temp_block.interVias;
                            for(int k=0;k<current_node.Blocks[i].instance[q].blockPins.size();k++){
                                  for(int l=0;l<temp_block.blockPins.size();l++){
                                       if(current_node.Blocks[i].instance[q].blockPins[k].name == temp_block.blockPins[l].name){    
                                            for(int p=0;p<temp_block.blockPins[l].pinContacts.size();p++){
                                        current_node.Blocks[i].instance[q].blockPins[k].pinContacts.push_back(temp_block.blockPins[l].pinContacts[p]);
                                                }
                                         }
                                     }
                               }
                            current_node.Blocks[i].instNum++;
                            std::cout<<"End feed blocks"<<std::endl;
                            continue;
                          }else{
                            std::cout<<"Start feed blocks"<<std::endl;
                            current_node.Blocks[i].instance.push_back(current_node.Blocks[i].instance[0]);
                            current_node.Blocks[i].instNum++;
                            current_node.Blocks[i].instance[q].width = temp_block.width;
                            current_node.Blocks[i].instance[q].height = temp_block.height;
                            current_node.Blocks[i].instance[q].originBox = temp_block.originBox;
                            current_node.Blocks[i].instance[q].originCenter = temp_block.originCenter;
                            current_node.Blocks[i].instance[q].gdsFile = temp_block.gdsFile;
                            current_node.Blocks[i].instance[q].orient = temp_block.orient;
                            current_node.Blocks[i].instance[q].interMetals = temp_block.interMetals;
                            current_node.Blocks[i].instance[q].interVias = temp_block.interVias;
                            for(int k=0;k<current_node.Blocks[i].instance[q].blockPins.size();k++){
                                 for(int l=0;l<temp_block.blockPins.size();l++){
                                     if(current_node.Blocks[i].instance[q].blockPins[k].name == temp_block.blockPins[l].name){ 
                                          current_node.Blocks[i].instance[q].blockPins[k].pinContacts.clear();   
                                          for(int p=0;p<temp_block.blockPins[l].pinContacts.size();p++){
                                        current_node.Blocks[i].instance[q].blockPins[k].pinContacts.push_back(temp_block.blockPins[l].pinContacts[p]);
                                             }
                                        }
                                    }
                                }
                       
                        
                             std::cout<<"End feed blocks"<<std::endl;
                             continue;
                          }
                          //std::cout<<"Current cap place "<<cap_r[q]<<std::endl;
                          //std::cout<<"Next cap "<<cap_r[q+1]<<std::endl;
                          

                       } 

                      //feedback data + modifcai capplacer.cpp + modify read in CCCap (centroid database is done)
                      
                   }
               }
               
            //find the instance name with CCC constrants, obtian the number & unit capacitor gds
            //find the master name for final gds name
            //find the pin name as a string
            //call the ccc fountion & checkout block & push_back the ccc information
         }
     }
}



/*
void Placer_Router_Cap::Common_centroid_capacitor(string fpath, PnRDB::hierNode& current_node, PnRDB::Drc_info & drc_info, map<string, PnRDB::lefMacro> lefData, bool dummy_flag){

  for(int i = 0;i<current_node.Blocks.size();i++){
       if(current_node.Blocks[i].instance.back().isLeaf == 1 and current_node.Blocks[i].instance.back().gdsFile ==""){
            //this block must be CC
            vector<int> ki;
            vector<pair<string, string> > pin_names;
            string unit_capacitor;
            string final_gds;
            pair<string, string> pins;
            for(int j=0;j<current_node.CC_Caps.size();j++){
                 if(current_node.CC_Caps[j].CCCap_name == current_node.Blocks[i].instance.back().name){
                      ki = current_node.CC_Caps[j].size;
                      unit_capacitor = current_node.CC_Caps[j].Unit_capacitor;
                      final_gds = current_node.Blocks[i].instance.back().master;
                      int pin_index = 0;
                      while(pin_index <current_node.Blocks[i].instance.back().blockPins.size()){
                         pins.first = current_node.Blocks[i].instance.back().blockPins[pin_index].name;
                         pins.second = current_node.Blocks[i].instance.back().blockPins[pin_index+1].name;
                         pin_names.push_back(pins);
                         pin_index = pin_index + 2;
                      }
                      bool cap_ratio = current_node.CC_Caps[j].cap_ratio;
                      int cap_r =current_node.CC_Caps[j].cap_r;
                      int cap_s =current_node.CC_Caps[j].cap_s;
                      Placer_Router_Cap PRC(ki, pin_names, fpath, unit_capacitor, final_gds, cap_ratio, cap_r, cap_s, drc_info, lefData, dummy_flag);
                      PnRDB::block temp_block=PRC.CheckoutData();
                      //feedback data
                      current_node.Blocks[i].instance.back().width = temp_block.width;
                      current_node.Blocks[i].instance.back().height = temp_block.height;
                      current_node.Blocks[i].instance.back().originBox = temp_block.originBox;
                      current_node.Blocks[i].instance.back().originCenter = temp_block.originCenter;
                      current_node.Blocks[i].instance.back().gdsFile = temp_block.gdsFile;
                      current_node.Blocks[i].instance.back().orient = temp_block.orient;
                      current_node.Blocks[i].instance.back().interMetals = temp_block.interMetals;
                      current_node.Blocks[i].instance.back().interVias = temp_block.interVias;
                      for(int k=0;k<current_node.Blocks[i].instance.back().blockPins.size();k++){
                          for(int l=0;l<temp_block.blockPins.size();l++){
                               if(current_node.Blocks[i].instance.back().blockPins[k].name == temp_block.blockPins[l].name){    
                                  for(int p=0;p<temp_block.blockPins[l].pinContacts.size();p++){
                                        current_node.Blocks[i].instance.back().blockPins[k].pinContacts.push_back(temp_block.blockPins[l].pinContacts[p]);
                                      }
                                 }
                             }
                         }
                      //feedback data + modifcai capplacer.cpp + modify read in CCCap (centroid database is done)
                      
                   }
               }
            //find the instance name with CCC constrants, obtian the number & unit capacitor gds
            //find the master name for final gds name
            //find the pin name as a string
            //call the ccc fountion & checkout block & push_back the ccc information
         }
     }
}
*/

void Placer_Router_Cap::PrintPlacer_Router_Cap(string outfile){
  cout<<"Placer-Router-Cap-Info: create gnuplot file"<<endl;
  int cap_num = Caps.size();
  ofstream fout;
  fout.open(outfile.c_str());

//set title
  fout<<"#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)"<<endl;
  fout<<"\nset title\" #capacitors= "<<Caps.size()<<" \""<<endl;
  fout<<"\nset nokey"<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save an EPS file for inclusion into a latex document"<<endl;
  fout<<"# set terminal postscript eps color solid 20"<<endl;
  fout<<"# set output \"result.eps\""<<endl<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save a PS file for printing"<<endl;
  fout<<"set term jpeg"<<endl;
  fout<<"set output \"result.jpg\""<<endl<<endl;

//set range
  //int max=(Xmax>Ymax)?Xmax:Ymax;
  fout<<"\nset xrange ["<<CheckOutBlock.originBox.LL.x-500<<":"<<CheckOutBlock.originBox.UR.x+500<<"]"<<endl;
  fout<<"\nset yrange ["<<CheckOutBlock.originBox.LL.y-500<<":"<<CheckOutBlock.originBox.UR.y+500<<"]"<<endl;

//set label for capacitors
  for(int i=0;i<Caps.size();i++){
       if(Caps[i].net_index!=-1){
       stringstream ss;
       ss<<Caps[i].net_index;
       string s1 = ss.str();
       string cap_name = "C_" + s1;
       fout<<"\nset label \""<<cap_name<<"\" at "<<Caps[i].x<<" , "<<Caps[i].y<<" center "<<endl;
       }else{
       string cap_name = "C_d";
       fout<<"\nset label \""<<cap_name<<"\" at "<<Caps[i].x<<" , "<<Caps[i].y<<" center "<<endl;
       }
       fout<<"\nset label \""<<i<<"\" at "<<Caps[i].x-unit_cap_demension.first/2<<" , "<<Caps[i].y-unit_cap_demension.second/2<<" center "<<endl;
     }

// plot capacitors
  fout<<"\nplot[:][:] \'-\' with lines linestyle 1,";
  for(int i=0;i<Nets_pos.size();i++){
     fout<<" \'-\' with lines linestyle "<<i+2<<",";
  }
  for(int i=0;i<Nets_neg.size();i++){
     fout<<" \'-\' with lines linestyle "<<i+2<<",";
  }
  fout<<endl<<endl;
  
  //fout<<"\nplot[:][:] \'-\' with lines linestyle 3, \'-\' with lines linestyle 7, \'-\' with lines linestyle 1, \'-\' with lines linestyle 0"<<endl<<endl;
  for(int i=0;i<Caps.size();i++){
      fout<<"\t"<<Caps[i].x-unit_cap_demension.first/2<<"\t"<<Caps[i].y-unit_cap_demension.second/2<<endl;
      fout<<"\t"<<Caps[i].x-unit_cap_demension.first/2<<"\t"<<Caps[i].y+unit_cap_demension.second/2<<endl;
      fout<<"\t"<<Caps[i].x+unit_cap_demension.first/2<<"\t"<<Caps[i].y+unit_cap_demension.second/2<<endl;
      fout<<"\t"<<Caps[i].x+unit_cap_demension.first/2<<"\t"<<Caps[i].y-unit_cap_demension.second/2<<endl;
      fout<<"\t"<<Caps[i].x-unit_cap_demension.first/2<<"\t"<<Caps[i].y-unit_cap_demension.second/2<<endl;
      fout<<endl;
     }
  if(Caps.size()>0){
  fout<<"\nEOF"<<endl; 
  }

// plot connection

  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<Nets_pos[i].start_conection_coord.size();j++){
     fout<<"\t"<<Nets_pos[i].start_conection_coord[j].first<<"\t"<<Nets_pos[i].start_conection_coord[j].second<<endl;
fout<<"\t"<<Nets_pos[i].end_conection_coord[j].first<<"\t"<<Nets_pos[i].end_conection_coord[j].second<<endl;
fout<<"\t"<<Nets_pos[i].start_conection_coord[j].first<<"\t"<<Nets_pos[i].start_conection_coord[j].second<<endl;
fout<<endl; 
        }
     if(Nets_pos.size()>0){  
        fout<<"\nEOF"<<endl;
        }
     }


  for(int i=0;i<Nets_neg.size();i++){
     for(int j=0;j<Nets_neg[i].start_conection_coord.size();j++){
     fout<<"\t"<<Nets_neg[i].start_conection_coord[j].first<<"\t"<<Nets_neg[i].start_conection_coord[j].second<<endl;
fout<<"\t"<<Nets_neg[i].end_conection_coord[j].first<<"\t"<<Nets_neg[i].end_conection_coord[j].second<<endl;
fout<<"\t"<<Nets_neg[i].start_conection_coord[j].first<<"\t"<<Nets_neg[i].start_conection_coord[j].second<<endl;
fout<<endl; 
        }
     if(Nets_neg.size()>0){  
       fout<<"\nEOF"<<endl;
      }
     }

  //fout<<endl<<"pause -1 \'Press any key\'";
  fout.close();
}
// Local Variables:
// c-basic-offset: 4
// End:
