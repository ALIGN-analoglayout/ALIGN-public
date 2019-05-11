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

Placer_Router_Cap::Placer_Router_Cap(string fpath, PnRDB::hierNode & current_node){
  cout<<"Enter"<<endl;
  Common_centroid_capacitor(fpath, current_node);
  cout<<"Out"<<endl;
}

Placer_Router_Cap::Placer_Router_Cap(vector<int> & ki, vector<pair<string, string> > &cap_pin, string fpath, string unit_capacitor, string final_gds){
//initial DRC router
  shifting = 18;
  offset_x = 0;
  offset_y = 0;
  for(int i=0;i<7;i++){
      metal_width.push_back(36); //change 
      metal_width[i] = metal_width[i] / 2;
      metal_distance_ss.push_back(112); //change //72
      metal_distance_ss[i] = metal_distance_ss[i]/2;
      via_width.push_back(36);
      via_width[i]=via_width[i]/2;
      via_cover.push_back(56); //change
      via_cover[i]=via_cover[i]/2;
  }
//initial demension
  min_dis = 2*metal_width[1]+metal_distance_ss[1];
  unit_cap_demension.first = 4428;
  unit_cap_demension.second = 4428;
  span_distance.first = 5;
  span_distance.second = 3*min_dis; //m1 distance
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
//for dummy caps
   r= r+2;
   s= s+2;

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
  //generate the cap pair sequence
  pair<int,int> temp_pair;
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
  initial_net_pair_sequence(ki,cap_pin);
  string outfile=final_gds+".plt";
  Router_Cap(ki,cap_pin);
  GetPhsicalInfo_router();
  cal_offset();
  //  WriteGDS(fpath ,unit_capacitor, final_gds);
  WriteJSON (fpath ,unit_capacitor, final_gds);
  PrintPlacer_Router_Cap(outfile);
}

void Placer_Router_Cap::cal_offset(){

  int x[5], y[5];
  int width = metal_width[0];
  int Min_x = INT_MAX;
  int Min_y = INT_MAX;
  int Max_x = INT_MIN;
  int Max_y = INT_MIN;
  //for positive nets
  
  for(int i=0; i< Nets_pos.size(); i++){//for each net
      for(int j=0; j< Nets_pos[i].start_conection_coord.size();j++){ //for segment
          if(Nets_pos[i].start_conection_coord[j].first == Nets_pos[i].end_conection_coord[j].first){//distance need to be modified then
             if(Nets_pos[i].start_conection_coord[j].second<Nets_pos[i].end_conection_coord[j].second){
                x[0]= Nets_pos[i].start_conection_coord[j].first-width;
                x[1]= Nets_pos[i].end_conection_coord[j].first-width;
                x[2]= Nets_pos[i].end_conection_coord[j].first+width;
                x[3]= Nets_pos[i].start_conection_coord[j].first+width;
                x[4]= x[0];
             
                y[0]= Nets_pos[i].start_conection_coord[j].second;
                y[1]= Nets_pos[i].end_conection_coord[j].second;
                y[2]= Nets_pos[i].end_conection_coord[j].second;
                y[3]= Nets_pos[i].start_conection_coord[j].second;
                y[4]=y[0];
                
               }else{

                x[0]= Nets_pos[i].end_conection_coord[j].first-width;
                x[1]= Nets_pos[i].start_conection_coord[j].first-width;
                x[2]= Nets_pos[i].start_conection_coord[j].first+width;
                x[3]= Nets_pos[i].end_conection_coord[j].first+width;
                x[4]= x[0];
             
                y[0]= Nets_pos[i].end_conection_coord[j].second;
                y[1]= Nets_pos[i].start_conection_coord[j].second;
                y[2]= Nets_pos[i].start_conection_coord[j].second;
                y[3]= Nets_pos[i].end_conection_coord[j].second;
                y[4]=y[0];

               }
          }else{
             if(Nets_pos[i].start_conection_coord[j].first<Nets_pos[i].end_conection_coord[j].first){

                x[0]= Nets_pos[i].start_conection_coord[j].first;
                x[1]= Nets_pos[i].start_conection_coord[j].first;
                x[2]= Nets_pos[i].end_conection_coord[j].first;
                x[3]= Nets_pos[i].end_conection_coord[j].first;
                x[4]= x[0];
             
                y[0]= Nets_pos[i].start_conection_coord[j].second-width;
                y[1]= Nets_pos[i].start_conection_coord[j].second+width;
                y[2]= Nets_pos[i].end_conection_coord[j].second+width;
                y[3]= Nets_pos[i].end_conection_coord[j].second-width;
                y[4]=y[0];

               }else{
    
                x[0]= Nets_pos[i].end_conection_coord[j].first;
                x[1]= Nets_pos[i].end_conection_coord[j].first;
                x[2]= Nets_pos[i].start_conection_coord[j].first;
                x[3]= Nets_pos[i].start_conection_coord[j].first;
                x[4]= x[0];
             
                y[0]= Nets_pos[i].end_conection_coord[j].second-width;
                y[1]= Nets_pos[i].end_conection_coord[j].second+width;
                y[2]= Nets_pos[i].start_conection_coord[j].second+width;
                y[3]= Nets_pos[i].start_conection_coord[j].second-width;
                y[4]=y[0];
       
               }
            }
            
            if(x[0]<Min_x){Min_x = x[0];}
            if(x[2]>Max_x){Max_x = x[2];}
            if(y[0]<Min_y){Min_y = y[0];}
            if(y[2]>Max_y){Max_y = y[2];}

        }
     }
  

  
  //for neg nets
  for(int i=0; i< Nets_neg.size(); i++){//for each net
      for(int j=0; j< Nets_neg[i].start_conection_coord.size();j++){ //for segment
          if(Nets_neg[i].start_conection_coord[j].first == Nets_neg[i].end_conection_coord[j].first){//distance need to be modified then
             if(Nets_neg[i].start_conection_coord[j].second<Nets_neg[i].end_conection_coord[j].second){
                x[0]= Nets_neg[i].start_conection_coord[j].first-width;
                x[1]= Nets_neg[i].end_conection_coord[j].first-width;
                x[2]= Nets_neg[i].end_conection_coord[j].first+width;
                x[3]= Nets_neg[i].start_conection_coord[j].first+width;
                x[4]= x[0];
             
                y[0]= Nets_neg[i].start_conection_coord[j].second;
                y[1]= Nets_neg[i].end_conection_coord[j].second;
                y[2]= Nets_neg[i].end_conection_coord[j].second;
                y[3]= Nets_neg[i].start_conection_coord[j].second;
                y[4]=y[0];
                
               }else{

                x[0]= Nets_neg[i].end_conection_coord[j].first-width;
                x[1]= Nets_neg[i].start_conection_coord[j].first-width;
                x[2]= Nets_neg[i].start_conection_coord[j].first+width;
                x[3]= Nets_neg[i].end_conection_coord[j].first+width;
                x[4]= x[0];
             
                y[0]= Nets_neg[i].end_conection_coord[j].second;
                y[1]= Nets_neg[i].start_conection_coord[j].second;
                y[2]= Nets_neg[i].start_conection_coord[j].second;
                y[3]= Nets_neg[i].end_conection_coord[j].second;
                y[4]=y[0];

               }
          }else{
             if(Nets_neg[i].start_conection_coord[j].first<Nets_neg[i].end_conection_coord[j].first){

                x[0]= Nets_neg[i].start_conection_coord[j].first;
                x[1]= Nets_neg[i].start_conection_coord[j].first;
                x[2]= Nets_neg[i].end_conection_coord[j].first;
                x[3]= Nets_neg[i].end_conection_coord[j].first;
                x[4]= x[0];
             
                y[0]= Nets_neg[i].start_conection_coord[j].second-width;
                y[1]= Nets_neg[i].start_conection_coord[j].second+width;
                y[2]= Nets_neg[i].end_conection_coord[j].second+width;
                y[3]= Nets_neg[i].end_conection_coord[j].second-width;
                y[4]=y[0];

               }else{
    
                x[0]= Nets_neg[i].end_conection_coord[j].first;
                x[1]= Nets_neg[i].end_conection_coord[j].first;
                x[2]= Nets_neg[i].start_conection_coord[j].first;
                x[3]= Nets_neg[i].start_conection_coord[j].first;
                x[4]= x[0];
             
                y[0]= Nets_neg[i].end_conection_coord[j].second-width;
                y[1]= Nets_neg[i].end_conection_coord[j].second+width;
                y[2]= Nets_neg[i].start_conection_coord[j].second+width;
                y[3]= Nets_neg[i].start_conection_coord[j].second-width;
                y[4]=y[0];
       
               }
            }

            if(x[0]<Min_x){Min_x = x[0];}
            if(x[2]>Max_x){Max_x = x[2];}
            if(y[0]<Min_y){Min_y = y[0];}
            if(y[2]>Max_y){Max_y = y[2];}

        }
     }
  
  //wirting vias
  //for positive net
  width = via_width[0];
  for(int i=0;i<Nets_pos.size();i++){
     for(int j=0;j<Nets_pos[i].via.size();j++){//the size of via needs to be modified according to different PDK
 
        x[0]=Nets_pos[i].via[j].first - width;
        x[1]=Nets_pos[i].via[j].first - width;
        x[2]=Nets_pos[i].via[j].first + width;
        x[3]=Nets_pos[i].via[j].first + width;
        x[4]=x[0];
        
        y[0]=Nets_pos[i].via[j].second - width;
        y[1]=Nets_pos[i].via[j].second + width;
        y[2]=Nets_pos[i].via[j].second + width;
        y[3]=Nets_pos[i].via[j].second - width;
        y[4]=y[0];

        if(x[0]<Min_x){Min_x = x[0];}
        if(x[2]>Max_x){Max_x = x[2];}
        if(y[0]<Min_y){Min_y = y[0];}
        if(y[2]>Max_y){Max_y = y[2];}
        
       }
    }
    
    //for negative net
  for(int i=0;i<Nets_neg.size();i++){
     for(int j=0;j<Nets_neg[i].via.size();j++){//the size of via needs to be modified according to different PDK
 
        x[0]=Nets_neg[i].via[j].first - width;
        x[1]=Nets_neg[i].via[j].first - width;
        x[2]=Nets_neg[i].via[j].first + width;
        x[3]=Nets_neg[i].via[j].first + width;
        x[4]=x[0];
        
        y[0]=Nets_neg[i].via[j].second - width;
        y[1]=Nets_neg[i].via[j].second + width;
        y[2]=Nets_neg[i].via[j].second + width;
        y[3]=Nets_neg[i].via[j].second - width;
        y[4]=y[0];
        

        if(x[0]<Min_x){Min_x = x[0];}
        if(x[2]>Max_x){Max_x = x[2];}
        if(y[0]<Min_y){Min_y = y[0];}
        if(y[2]>Max_y){Max_y = y[2];}

      
       }
    }
  
  for(int i= 0; i<Caps.size();i++){
      x[0]=Caps[i].x - unit_cap_demension.first/2;
      x[1]=Caps[i].x - unit_cap_demension.first/2;
      x[2]=Caps[i].x + unit_cap_demension.first/2;
      x[3]=Caps[i].x + unit_cap_demension.first/2;
      x[4]=x[0];
       
      y[0]=Caps[i].y - unit_cap_demension.second/2;
      y[1]=Caps[i].y + unit_cap_demension.second/2;
      y[2]=Caps[i].y + unit_cap_demension.second/2;
      y[3]=Caps[i].y - unit_cap_demension.second/2;
      y[4]=y[0];

      if(x[0]<Min_x){Min_x = x[0];}
      if(x[2]>Max_x){Max_x = x[2];}
      if(y[0]<Min_y){Min_y = y[0];}
      if(y[2]>Max_y){Max_y = y[2];}

     }
  
  offset_x = 0-Min_x;
  offset_y = 0-Min_y;

}

void Placer_Router_Cap::initial_net_pair_sequence(vector<int> & ki, vector<pair<string, string> > & cap_pin){
//initial net pair sequence
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
  
  net temp_net;
  // a dummy net is added for dummy capacitor
  for(int i=0;i<ki.size()+1;i++){
     if(i<ki.size()){
       temp_net.name = cap_pin[i].second;
     }else{
       temp_net.name = "dummy_gnd";
     }
     Nets_pos.push_back(temp_net);
   }
  int start_index=0;
  for(int i=0;i<net_sequence.size();i++){
     if(net_sequence[i].second==-1){
        Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
        Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
        start_index = start_index+1;
       }else if(net_sequence[i].second!=-1 and cap_pair_sequence[start_index].second == -1){
        start_index = start_index+1;
        Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
        Nets_pos[net_sequence[i].second].cap_index.push_back(cap_pair_sequence[start_index].second);
        Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
        Caps[cap_pair_sequence[start_index].second].net_index = net_sequence[i].second;
        start_index = start_index+1;
       }else if(net_sequence[i].second!=-1 and cap_pair_sequence[start_index].second != -1){
        Nets_pos[net_sequence[i].first].cap_index.push_back(cap_pair_sequence[start_index].first);
        Nets_pos[net_sequence[i].second].cap_index.push_back(cap_pair_sequence[start_index].second);
        Caps[cap_pair_sequence[start_index].first].net_index = net_sequence[i].first;
        Caps[cap_pair_sequence[start_index].second].net_index = net_sequence[i].second;
        start_index = start_index+1;
      }
     }
  //add a net for dummy capacitor
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

void Placer_Router_Cap::Router_Cap(vector<int> & ki, vector<pair<string, string> > &cap_pin){
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

  int net_size = ki.size();
  double sum = 0;
  double r;
  double s;
  for(int i=0;i<net_size;i++){
     sum = sum + ki[i];
    }
   r = ceil(sqrt(sum));
   s = ceil(sum/r);
   r= r+2;
   s= s+2;
   double Cx = (r)/2; //note this is different
   double Cy = (s)/2; //note this is different
//create router line for each net (cap) vertical 
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
             temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x]=1;
             temp_router_line.cap_index[2*Cx-Caps[Nets_pos[i].Set[j].cap_index[l]].index_x+1]=1;//-1
            }
         Nets_pos[i].router_line_v.push_back(temp_router_line);
        }
     }
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
             temp_router_line.cap_index[2*Cy-Caps[Nets_pos[i].Set[j].cap_index[l]].index_y+1]=1;//-1
            }
         Nets_pos[i].router_line_h.push_back(temp_router_line);
        }
     }
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
  
  //initial num_router_net_v
  for(int i=0;i<=r;i++){num_router_net_v.push_back(0);}
  //initial num_router_net_h
  for(int i=0;i<=s;i++){num_router_net_h.push_back(0);}
  
  Nets_neg = Nets_pos;
  for(int i=0;i<Nets_pos.size();i++){
       if(i!=Nets_pos.size()-1){
           Nets_neg[i].name = cap_pin[i].first;
         }else{
           Nets_neg[i].name = "dummy_gnd";
         }
     }
  

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

   span_distance.first = (max_num_+1)*min_dis;
  cout<<span_distance.first<<endl;

  for(int i=0;i<Caps.size();i++){
      Caps[i].x = unit_cap_demension.first/2 +  Caps[i].index_x* (unit_cap_demension.first+span_distance.first);
     }
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

void Placer_Router_Cap::GetPhsicalInfo_router(){
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
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting;
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting;
                      // via coverage???
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");

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
                    
                      //
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x- unit_cap_demension.first/2-shifting-(span_distance.first-min_dis*trails[l]);
                      Caps[Nets_pos[i].cap_index[k]].access = 1;
            
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      Nets_pos[i].metal.push_back("M2");
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                     
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
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting;
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting;
                      
                      //
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                     
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
                    
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting-min_dis;
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      Nets_pos[i].metal.push_back("M1");
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                      
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
                      
                      //
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting+(min_dis*trails[l]);
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      //
                      Nets_pos[i].metal.push_back("M2");
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                      
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
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x- unit_cap_demension.first/2-(span_distance.first-min_dis*trails[l]);
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
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting;
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting;
                      
                      //
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                      
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

                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_pos[i].cap_index[k]].y- unit_cap_demension.second/2+shifting-min_dis;
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      Nets_pos[i].metal.push_back("M1");
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                      
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

                      //
                      Nets_pos[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_pos[i].cap_index[k]].x+ unit_cap_demension.first/2-shifting+(min_dis*trails[l]);
                      Nets_pos[i].end_conection_coord.push_back(coord);
                      Nets_pos[i].Is_pin.push_back(0);
                      //
                      Nets_pos[i].metal.push_back("M2");
                      Nets_pos[i].via.push_back(coord);
                      Nets_pos[i].via_metal.push_back("M1");
                      
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
                 //connect from start to end for each trail 
                 coord.second = 0 - min_dis*routed_trail-2*min_dis+shifting;
                 
                 //
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
                 
                 Nets_pos[i].start_conection_coord.push_back(coord);
                 //
                 coord.second = -2*min_dis+shifting;
                 Nets_pos[i].end_conection_coord.push_back(coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 Nets_pos[i].metal.push_back("M3");
                 //
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
                
                 //
                 Nets_pos[i].start_conection_coord.push_back(coord);
                 coord.second = Caps[max_cap_index].y- unit_cap_demension.second/2-left_right*min_dis+shifting;
                 Nets_pos[i].end_conection_coord.push_back(coord);
                 Nets_pos[i].Is_pin.push_back(0);
                 //
                 Nets_pos[i].metal.push_back("M1");
                 //
                 if(first_lock==0){
                    first_coord.first = coord.first;
                    first_coord.second = 0 - min_dis*routed_trail-2*min_dis+shifting;
                    first_lock=1;
                 }else{
                    end_close=1;
                    end_coord.first = coord.first;;
                    end_coord.second = 0 - min_dis*routed_trail-2*min_dis+shifting;
                 }
            }
         }
       //connect to each trail
       if(first_lock==1 and end_close==1){
       Nets_pos[i].start_conection_coord.push_back(first_coord);
       Nets_pos[i].end_conection_coord.push_back(end_coord);
       Nets_pos[i].Is_pin.push_back(1);
       //
       Nets_pos[i].metal.push_back("M2");
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
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[k]].x + unit_cap_demension.first/2-shifting;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[k]].y - unit_cap_demension.second/2+shifting;  
                              
                              //
                              Nets_pos[i].via.push_back(coord);
                              Nets_pos[i].via_metal.push_back("M1");

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
                      
                              

                              //
                              Nets_pos[i].start_conection_coord.push_back(coord);
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[index]].x + unit_cap_demension.first/2-shifting;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[index]].y - unit_cap_demension.second/2+shifting;
                              Nets_pos[i].end_conection_coord.push_back(coord);
                              Nets_pos[i].Is_pin.push_back(0);
                              Nets_pos[i].metal.push_back("M2");
                              //
                              Nets_pos[i].via.push_back(coord);
                              Nets_pos[i].via_metal.push_back("M1");

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
                              
                              //
                              index = 0;
                              found = 1;
                             }else if((Caps[Nets_pos[i].Set[j].cap_index[k]].index_x==Caps[Nets_pos[i].Set[j].cap_index[index]].index_x and abs(Caps[Nets_pos[i].Set[j].cap_index[k]].index_y-Caps[Nets_pos[i].Set[j].cap_index[index]].index_y) ==1) and !(Caps[Nets_pos[i].Set[j].cap_index[k]].access)){
                              Caps[Nets_pos[i].Set[j].cap_index[k]].access=1;
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[k]].x + unit_cap_demension.first/2-shifting;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[k]].y - unit_cap_demension.second/2+shifting;  
                              
                              //
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
                              
                              //
                              Nets_pos[i].start_conection_coord.push_back(coord);
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;
                              coord.first = Caps[Nets_pos[i].Set[j].cap_index[index]].x + unit_cap_demension.first/2-shifting;
                              coord.second = Caps[Nets_pos[i].Set[j].cap_index[index]].y - unit_cap_demension.second/2+shifting;
                              Nets_pos[i].end_conection_coord.push_back(coord);
                              Nets_pos[i].Is_pin.push_back(0);
                              Nets_pos[i].metal.push_back("M3");
                              //
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
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2+shifting;
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2-shifting;
                      
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
                      
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
                      

                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2 + shifting-(span_distance.first-min_dis*trails[l]);
                      Caps[Nets_neg[i].cap_index[k]].access = 1;
                      //
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      //
                      Nets_neg[i].metal.push_back("M2");
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
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
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2+shifting;
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2-shifting;
                      
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
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
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2+min_dis-shifting;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back("M1");
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
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
                      
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x+ unit_cap_demension.first/2+(min_dis*trails[l])+shifting;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back("M2");
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
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
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2-(span_distance.first-min_dis*trails[l]);
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
                      
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x- unit_cap_demension.first/2+shifting;
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2-shifting;
                      
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
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
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.second = Caps[Nets_neg[i].cap_index[k]].y+ unit_cap_demension.second/2+min_dis-shifting;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back("M1");
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
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
                      
                      //
                      Nets_neg[i].start_conection_coord.push_back(coord);
                      coord.first = Caps[Nets_neg[i].cap_index[k]].x+ unit_cap_demension.first/2+(min_dis*trails[l])+shifting;
                      Nets_neg[i].end_conection_coord.push_back(coord);
                      Nets_neg[i].Is_pin.push_back(0);
                      Nets_neg[i].metal.push_back("M2");
                      //
                      Nets_neg[i].via.push_back(coord);
                      Nets_neg[i].via_metal.push_back("M1");
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
                 coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis*routed_trail+2*min_dis-shifting;
                 
                 //
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
                 Nets_neg[i].start_conection_coord.push_back(coord);
                 coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2+2*min_dis-shifting;
                 Nets_neg[i].end_conection_coord.push_back(coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back("M3");
                 //
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
                 Nets_neg[i].start_conection_coord.push_back(coord);
                 coord.second = Caps[min_cap_index].y+ unit_cap_demension.second/2+left_right*min_dis-shifting;
                 Nets_neg[i].end_conection_coord.push_back(coord);
                 Nets_neg[i].Is_pin.push_back(0);
                 Nets_neg[i].metal.push_back("M1");
                 if(first_lock==0){
                    first_coord.first = coord.first;
                    first_coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis*routed_trail+2*min_dis-shifting;
                    first_lock=1;
                 }else{
                    end_close=1;
                    end_coord.first = coord.first;
                    end_coord.second = Caps[num_cap-1].y+unit_cap_demension.second/2 + min_dis*routed_trail+2*min_dis-shifting;
                 }
            }
         }
       //connect to each trail
       if(first_lock==1 and end_close==1){
       Nets_neg[i].start_conection_coord.push_back(first_coord);
       Nets_neg[i].end_conection_coord.push_back(end_coord);
       Nets_neg[i].Is_pin.push_back(1);
       //
       Nets_neg[i].metal.push_back("M2");
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
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[k]].x - unit_cap_demension.first/2+shifting;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[k]].y + unit_cap_demension.second/2-shifting;  
                             
                              //
                              Nets_neg[i].via.push_back(coord);
                              Nets_neg[i].via_metal.push_back("M1");
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
                      
                              
                              //Nets_neg[i].via.push_back(coord);
                              //Nets_neg[i].via_metal.push_back("M2");
                              //
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;

                              Nets_neg[i].start_conection_coord.push_back(coord);
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[index]].x - unit_cap_demension.first/2+shifting;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[index]].y + unit_cap_demension.second/2-shifting;
                              Nets_neg[i].end_conection_coord.push_back(coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back("M2");
                              //
                              Nets_neg[i].via.push_back(coord);
                              Nets_neg[i].via_metal.push_back("M1");
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
                      
                      
                              //Nets_neg[i].via.push_back(coord);
                              //Nets_neg[i].via_metal.push_back("M2");
                              
                              //
                              index = 0;
                              found = 1;
                             }else if((Caps[Nets_neg[i].Set[j].cap_index[k]].index_x==Caps[Nets_neg[i].Set[j].cap_index[index]].index_x and abs(Caps[Nets_neg[i].Set[j].cap_index[k]].index_y-Caps[Nets_neg[i].Set[j].cap_index[index]].index_y) ==1 and !(Caps[Nets_neg[i].Set[j].cap_index[k]].access))){
                              Caps[Nets_neg[i].Set[j].cap_index[k]].access=1;
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[k]].x - unit_cap_demension.first/2+shifting;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[k]].y + unit_cap_demension.second/2-shifting;  
                              
                              //
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
                              
                              //Nets_neg[i].via.push_back(coord);
                              //Nets_neg[i].via_metal.push_back("M2");
                              //
                              //Caps[Nets_pos[i].Set[j].cap_index[k]].access = 1;
                              Nets_neg[i].start_conection_coord.push_back(coord);
                              coord.first = Caps[Nets_neg[i].Set[j].cap_index[index]].x - unit_cap_demension.first/2+shifting;
                              coord.second = Caps[Nets_neg[i].Set[j].cap_index[index]].y + unit_cap_demension.second/2-shifting;
                              Nets_neg[i].end_conection_coord.push_back(coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back("M3");
                              //
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
                              via_coord.second = coord.second - via_cover[0];
                              Nets_neg[i].start_conection_coord.push_back(via_coord);
                              via_coord.second = coord.second + via_cover[0];
                              Nets_neg[i].end_conection_coord.push_back(via_coord);
                              Nets_neg[i].Is_pin.push_back(0);
                              Nets_neg[i].metal.push_back("M3");
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
Placer_Router_Cap::WriteJSON(string fpath, string unit_capacitor, string final_gds) {
    //begin to write JSON file from unit capacitor to final capacitor file
    string gds_unit_capacitor = fpath+"/"+unit_capacitor+".gds";
    string topGDS_loc = final_gds+".gds";
    string TopCellName = final_gds;

    std::ofstream jsonStream;
    jsonStream.open (topGDS_loc + ".json");
    json jsonTop;

    jsonTop["header"] = 600;
    json jsonLibAry = json::array();
    json jsonLib;
    jsonLib["time"] = JSON_TimeTime();
    // DAK Overwrite to match
    jsonLib["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
    jsonLib["units"] = {0.00025, 2.5e-10};
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

    // DAK: These should be defined in a method that can load this map from a file / PDK
    string MaskID_M1 = "19";
    string MaskID_V1 = "21";
    string MaskID_M2 = "20";
    string MaskID_V2 = "25";
    string MaskID_M3 = "30";
    string MaskID_V3 = "35";
    string MaskID_M4 = "40";
    string MaskID_V4 = "45";
    string MaskID_M5 = "50";
    string MaskID_V5 = "55";
    string MaskID_M6 = "60";
    string MaskID_V6 = "65";
    string MaskID_M7 = "70";
    string MaskID_V7 = "75";

    int width = metal_width[0];
    int Min_x = INT_MAX;
    int Min_y = INT_MAX;
    int Max_x = INT_MIN;
    int Max_y = INT_MIN;
    //for positive nets

    for(int i=0; i< Nets_pos.size(); i++){//for each net
	PnRDB::pin temp_Pins;
	for(int j=0; j< Nets_pos[i].start_conection_coord.size();j++){ //for segment
	    fillPathBoundingBox (x, y, Nets_pos[i].start_conection_coord[j],
				 Nets_pos[i].end_conection_coord[j], width);
            
	    if(x[0]<Min_x){Min_x = x[0];}
	    if(x[2]>Max_x){Max_x = x[2];}
	    if(y[0]<Min_y){Min_y = y[0];}
	    if(y[2]>Max_y){Max_y = y[2];}

	    PnRDB::contact temp_contact;
	    fillContact (temp_contact, x, y);
            
	    for (int i = 0; i < 5; i++) {
		x[i] *= 2;
		y[i] *= 2;
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

	    temp_contact.metal = Nets_pos[i].metal[j];
      
	    if (Nets_pos[i].metal[j] == "M1"){
		bound["layer"] = stoi(MaskID_M1);
	    } else if(Nets_pos[i].metal[j] == "M2"){	
		bound["layer"] = stoi(MaskID_M2);
	    } else if(Nets_pos[i].metal[j] == "M3"){	
		bound["layer"] = stoi(MaskID_M3);
	    } else if(Nets_pos[i].metal[j] == "M4"){	
		bound["layer"] = stoi(MaskID_M4);
	    } else if(Nets_pos[i].metal[j] == "M5"){	
		bound["layer"] = stoi(MaskID_M5);
	    } else if(Nets_pos[i].metal[j] == "M6"){	
		bound["layer"] = stoi(MaskID_M6);
	    } else if(Nets_pos[i].metal[j] == "M7"){	
		bound["layer"] = stoi(MaskID_M7);
	    }

	    jsonElements.push_back (bound);

	    if (Nets_pos[i].Is_pin[j] == 1) {
		temp_Pins.name = Nets_pos[i].name;
		temp_Pins.pinContacts.push_back(temp_contact);
	    }
	    CheckOutBlock.interMetals.push_back(temp_contact);
	}   
	CheckOutBlock.blockPins.push_back(temp_Pins);
    }
  
    //for neg nets
    for(int i =0; i < Nets_neg.size(); i++) {//for each net
	PnRDB::pin temp_Pins_neg;
	for(int j = 0; j < Nets_neg[i].start_conection_coord.size(); j++) { //for segment
	    fillPathBoundingBox (x, y, Nets_neg[i].start_conection_coord[j],
				 Nets_neg[i].end_conection_coord[j], width);

	    if(x[0]<Min_x) Min_x = x[0];
	    if(x[2]>Max_x) Max_x = x[2];
	    if(y[0]<Min_y) Min_y = y[0];
	    if(y[2]>Max_y) Max_y = y[2];

	    PnRDB::contact temp_contact;
	    fillContact (temp_contact, x, y);

	    for (int i = 0; i < 5; i++) {
		x[i] *= 2;
		y[i] *= 2;
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

	    temp_contact.metal = Nets_neg[i].metal[j];

	    if (Nets_neg[i].metal[j] == "M1") {
		bound["layer"] = stoi(MaskID_M1);
	    } else if (Nets_neg[i].metal[j] == "M2") {
		bound["layer"] = stoi(MaskID_M2);
	    } else if (Nets_neg[i].metal[j] == "M3") {	
		bound["layer"] = stoi(MaskID_M3);
	    } else if (Nets_neg[i].metal[j] == "M4") {	
		bound["layer"] = stoi(MaskID_M4);
	    } else if (Nets_neg[i].metal[j] == "M5") {	
		bound["layer"] = stoi(MaskID_M5);
	    } else if (Nets_neg[i].metal[j] == "M6") {
		bound["layer"] = stoi(MaskID_M6);
	    } else if (Nets_neg[i].metal[j] == "M7") {
		bound["layer"] = stoi(MaskID_M7);
	    }

	    jsonElements.push_back (bound);
	    if (Nets_neg[i].Is_pin[j] == 1) {
		temp_Pins_neg.name = Nets_neg[i].name;
		temp_Pins_neg.pinContacts.push_back(temp_contact);
	    }
	    CheckOutBlock.interMetals.push_back(temp_contact);
	}
	CheckOutBlock.blockPins.push_back(temp_Pins_neg);
    }
  
    //wirting vias
    //for positive net
    width = via_width[0];
    for(int i=0;i<Nets_pos.size();i++){
	for(int j=0;j<Nets_pos[i].via.size();j++){//the size of via needs to be modified according to different PDK
 
	    x[0]=Nets_pos[i].via[j].first - width+offset_x;
	    x[1]=Nets_pos[i].via[j].first - width+offset_x;
	    x[2]=Nets_pos[i].via[j].first + width+offset_x;
	    x[3]=Nets_pos[i].via[j].first + width+offset_x;
	    x[4]=x[0];
        
	    y[0]=Nets_pos[i].via[j].second - width+offset_y;
	    y[1]=Nets_pos[i].via[j].second + width+offset_y;
	    y[2]=Nets_pos[i].via[j].second + width+offset_y;
	    y[3]=Nets_pos[i].via[j].second - width+offset_y;
	    y[4]=y[0];
        

	    if(x[0]<Min_x){Min_x = x[0];}
	    if(x[2]>Max_x){Max_x = x[2];}
	    if(y[0]<Min_y){Min_y = y[0];}
	    if(y[2]>Max_y){Max_y = y[2];}

	    PnRDB::contact temp_contact;
	    fillContact (temp_contact, x, y);

	    for (int i = 0; i < 5; i++) {
		x[i] *= 2;
		y[i] *= 2;
	    }
    
	    PnRDB::Via temp_via;
	    PnRDB::contact upper_contact;
	    PnRDB::contact lower_contact;
	    upper_contact.placedCenter = temp_contact.placedCenter;
	    lower_contact.placedCenter = temp_contact.placedCenter;

	    PnRDB::contact h_contact;
	    h_contact.originBox.LL = temp_contact.originBox.LL;
	    h_contact.originBox.UL = temp_contact.originBox.UL;
	    h_contact.originBox.UR = temp_contact.originBox.UR;
	    h_contact.originBox.LR = temp_contact.originBox.LR;
	    h_contact.originBox.LL.y = temp_contact.originBox.LL.y-(via_cover[0]-via_width[0]);
	    h_contact.originBox.UL.y = temp_contact.originBox.UL.y+(via_cover[0]-via_width[0]);
	    h_contact.originBox.UR.y = temp_contact.originBox.UR.y+(via_cover[0]-via_width[0]);
	    h_contact.originBox.LR.y = temp_contact.originBox.LR.y-(via_cover[0]-via_width[0]);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.LL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UR);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.LR);

	    PnRDB::contact v_contact;
	    v_contact.originBox.LL = temp_contact.originBox.LL;
	    v_contact.originBox.UL = temp_contact.originBox.UL;
	    v_contact.originBox.UR = temp_contact.originBox.UR;
	    v_contact.originBox.LR = temp_contact.originBox.LR;
	    v_contact.originBox.LL.x = temp_contact.originBox.LL.x-(via_cover[0]-via_width[0]);
	    v_contact.originBox.UL.x = temp_contact.originBox.UL.x-(via_cover[0]-via_width[0]);
	    v_contact.originBox.UR.x = temp_contact.originBox.UR.x+(via_cover[0]-via_width[0]);
	    v_contact.originBox.LR.x = temp_contact.originBox.LR.x+(via_cover[0]-via_width[0]);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.LL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UR);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.LR);


	    json bound;
	    bound["type"] = "boundary";
	    bound["datatype"] = 0;
	    json xy = json::array();
	    for (size_t i = 0; i < 5; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    bound["xy"] = xy;

	    if(Nets_pos[i].via_metal[j].compare("M1")==0){

		bound["layer"] = stoi(MaskID_V1);
		temp_contact.metal = "V1";
		lower_contact.metal = "M1";
		upper_contact.metal = "M2";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 0;
	    }else if(Nets_pos[i].via_metal[j].compare("M2")==0){

		bound["layer"] = stoi(MaskID_V2);
		temp_contact.metal = "V2";
		lower_contact.metal = "M2";
		upper_contact.metal = "M3";
		lower_contact.originBox = h_contact.originBox;
		upper_contact.originBox = v_contact.originBox;
		temp_via.model_index = 1;
	    }else if(Nets_pos[i].via_metal[j].compare("M3")==0){

		bound["layer"] = stoi(MaskID_V3);
		temp_contact.metal = "V3";
		lower_contact.metal = "M3";
		upper_contact.metal = "M4";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 2;
	    }else if(Nets_pos[i].via_metal[j].compare("M4")==0){

		bound["layer"] = stoi(MaskID_V4);
		temp_contact.metal = "V4";
		lower_contact.metal = "M4";
		upper_contact.metal = "M5";
		lower_contact.originBox = h_contact.originBox;
		upper_contact.originBox = v_contact.originBox;
		temp_via.model_index = 3;
	    }else if(Nets_pos[i].via_metal[j].compare("M5")==0){

		bound["layer"] = stoi(MaskID_V5);
		temp_contact.metal = "V5";
		lower_contact.metal = "M5";
		upper_contact.metal = "M6";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 4;
	    }else if(Nets_pos[i].via_metal[j].compare("M6")==0){

		bound["layer"] = stoi(MaskID_V6);
		temp_contact.metal = "V6";
		lower_contact.metal = "M6";
		upper_contact.metal = "M7";
		lower_contact.originBox = h_contact.originBox;
		upper_contact.originBox = v_contact.originBox;
		temp_via.model_index = 5;
	    }else if(Nets_pos[i].via_metal[j].compare("M7")==0){

		bound["layer"] = stoi(MaskID_V7);
		temp_contact.metal = "V7";
		lower_contact.metal = "M7";
		upper_contact.metal = "M8";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 6;
	    }

	    jsonElements.push_back (bound);
	
	    temp_via.placedpos = temp_contact.originCenter;
	    temp_via.ViaRect = temp_contact;
	    temp_via.LowerMetalRect = lower_contact;
	    temp_via.UpperMetalRect = upper_contact;
	    CheckOutBlock.interVias.push_back(temp_via);
	}
    }
    
    //for negative net
    for(int i=0;i<Nets_neg.size();i++){
	for(int j=0;j<Nets_neg[i].via.size();j++){//the size of via needs to be modified according to different PDK
 
	    x[0]=Nets_neg[i].via[j].first - width+offset_x;
	    x[1]=Nets_neg[i].via[j].first - width+offset_x;
	    x[2]=Nets_neg[i].via[j].first + width+offset_x;
	    x[3]=Nets_neg[i].via[j].first + width+offset_x;
	    x[4]=x[0];
        
	    y[0]=Nets_neg[i].via[j].second - width+offset_y;
	    y[1]=Nets_neg[i].via[j].second + width+offset_y;
	    y[2]=Nets_neg[i].via[j].second + width+offset_y;
	    y[3]=Nets_neg[i].via[j].second - width+offset_y;
	    y[4]=y[0];
        
	    if(x[0]<Min_x){Min_x = x[0];}
	    if(x[2]>Max_x){Max_x = x[2];}
	    if(y[0]<Min_y){Min_y = y[0];}
	    if(y[2]>Max_y){Max_y = y[2];}

	    PnRDB::contact temp_contact;
	    fillContact (temp_contact, x, y);

	    for (int i = 0; i < 5; i++) {
		x[i] *= 2;
		y[i] *= 2;
	    }

	    PnRDB::Via temp_via;
	    PnRDB::contact upper_contact;
	    PnRDB::contact lower_contact;
	    upper_contact.placedCenter = temp_contact.placedCenter;
	    lower_contact.placedCenter = temp_contact.placedCenter;

	    PnRDB::contact h_contact;
	    h_contact.originBox.LL = temp_contact.originBox.LL;
	    h_contact.originBox.UL = temp_contact.originBox.UL;
	    h_contact.originBox.UR = temp_contact.originBox.UR;
	    h_contact.originBox.LR = temp_contact.originBox.LR;
	    h_contact.originBox.LL.y = temp_contact.originBox.LL.y-(via_cover[0]-via_width[0]);
	    h_contact.originBox.UL.y = temp_contact.originBox.UL.y+(via_cover[0]-via_width[0]);
	    h_contact.originBox.UR.y = temp_contact.originBox.UR.y+(via_cover[0]-via_width[0]);
	    h_contact.originBox.LR.y = temp_contact.originBox.LR.y-(via_cover[0]-via_width[0]);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.LL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UL);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.UR);
	    h_contact.originBox.polygon.push_back(h_contact.originBox.LR);

	    PnRDB::contact v_contact;
	    v_contact.originBox.LL = temp_contact.originBox.LL;
	    v_contact.originBox.UL = temp_contact.originBox.UL;
	    v_contact.originBox.UR = temp_contact.originBox.UR;
	    v_contact.originBox.LR = temp_contact.originBox.LR;
	    v_contact.originBox.LL.x = temp_contact.originBox.LL.x-(via_cover[0]-via_width[0]);
	    v_contact.originBox.UL.x = temp_contact.originBox.UL.x-(via_cover[0]-via_width[0]);
	    v_contact.originBox.UR.x = temp_contact.originBox.UR.x+(via_cover[0]-via_width[0]);
	    v_contact.originBox.LR.x = temp_contact.originBox.LR.x+(via_cover[0]-via_width[0]);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.LL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UL);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.UR);
	    v_contact.originBox.polygon.push_back(v_contact.originBox.LR);

	    json bound;
	    bound["type"] = "boundary";
	    bound["datatype"] = 0;
	    json xy = json::array();
	    for (size_t i = 0; i < 5; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    bound["xy"] = xy;

	    if(Nets_neg[i].via_metal[j].compare("M1")==0){

		bound["layer"] = stoi(MaskID_V1);
		temp_contact.metal = "V1";
		lower_contact.metal = "M1";
		upper_contact.metal = "M2";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 0;
	    }else if(Nets_neg[i].via_metal[j].compare("M2")==0){

		bound["layer"] = stoi(MaskID_V2);
		temp_contact.metal = "V2";
		lower_contact.metal = "M2";
		upper_contact.metal = "M3";
		lower_contact.originBox = h_contact.originBox;
		upper_contact.originBox = v_contact.originBox;
		temp_via.model_index = 1;
	    }else if(Nets_neg[i].via_metal[j].compare("M3")==0){

		bound["layer"] = stoi(MaskID_V3);
		temp_contact.metal = "V3";
		lower_contact.metal = "M3";
		upper_contact.metal = "M4";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 2;
	    }else if(Nets_neg[i].via_metal[j].compare("M4")==0){

		bound["layer"] = stoi(MaskID_V4);
		temp_contact.metal = "V4";
		lower_contact.metal = "M4";
		upper_contact.metal = "M5";
		lower_contact.originBox = h_contact.originBox;
		upper_contact.originBox = v_contact.originBox;
		temp_via.model_index = 3;
	    }else if(Nets_neg[i].via_metal[j].compare("M5")==0){

		bound["layer"] = stoi(MaskID_V5);
		temp_contact.metal = "V5";
		lower_contact.metal = "M5";
		upper_contact.metal = "M6";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 4;
	    }else if(Nets_neg[i].via_metal[j].compare("M6")==0){

		bound["layer"] = stoi(MaskID_V6);
		temp_contact.metal = "V6";
		lower_contact.metal = "M6";
		upper_contact.metal = "M7";
		lower_contact.originBox = h_contact.originBox;
		upper_contact.originBox = v_contact.originBox;
		temp_via.model_index = 5;
	    }else if(Nets_neg[i].via_metal[j].compare("M7")==0){

		bound["layer"] = stoi(MaskID_V7);
		temp_contact.metal = "V7";
		lower_contact.metal = "M7";
		upper_contact.metal = "M8";
		lower_contact.originBox = v_contact.originBox;
		upper_contact.originBox = h_contact.originBox;
		temp_via.model_index = 6;
	    }

	    jsonElements.push_back (bound);
	 
	    temp_via.placedpos = temp_contact.originCenter;
	    temp_via.ViaRect = temp_contact;
	    temp_via.LowerMetalRect = lower_contact;
	    temp_via.UpperMetalRect = upper_contact;
	    CheckOutBlock.interVias.push_back(temp_via);
	}
    }
    CheckOutBlock.orient = PnRDB::Omark(0); //need modify
  
    for(int i= 0; i<Caps.size();i++){
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
     

	if(x[0]<Min_x){Min_x = x[0];}
	if(x[2]>Max_x){Max_x = x[2];}
	if(y[0]<Min_y){Min_y = y[0];}
	if(y[2]>Max_y){Max_y = y[2];}
 
	PnRDB::contact temp_contact;
	fillContact (temp_contact, x, y);

	temp_contact.metal = "M1";
	CheckOutBlock.interMetals.push_back(temp_contact);
	temp_contact.metal = "M2";
	CheckOutBlock.interMetals.push_back(temp_contact);
	temp_contact.metal = "M3";
	CheckOutBlock.interMetals.push_back(temp_contact);
    }

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
  
    //wirte orientation for each cap
    for(int i=0;i<Caps.size();i++){

	json sref;
	sref["type"] = "sref";
	if (strBlocks_Top.size())
	    sref["sname"] = strBlocks_Top[0].c_str();
	else
	    cout << "ERROR: no block found to output from subcells" << endl;
	sref["strans"] = 0;
	sref["angle"] = 0.0;
	x[0]=2*(Caps[i].x-unit_cap_demension.first/2+offset_x);
	y[0]=2*(Caps[i].y-unit_cap_demension.second/2+offset_y);
     
	json xy = json::array();
	xy.push_back (x[0]);
	xy.push_back (y[0]);
	sref["xy"] = xy;
	jsonElements.push_back (sref);
    }

    jsonStr["elements"] = jsonElements;
    jsonStrAry.push_back (jsonStr);
    jsonLib["bgnstr"] = jsonStrAry;

    jsonLibAry.push_back(jsonLib);
    jsonTop["bgnlib"] = jsonLibAry;
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    std::cout << "CAP GDS JSON FINALIZE " <<  unit_capacitor << std::endl;
}

// void Placer_Router_Cap::GDSReaderWriterTxTFile_extension(string GDSData, GdsParser::GdsWriter& gw, int& rndnum, vector<string>& strBlocks, vector<int>& llx, vector<int>& lly, vector<int>& urx, vector<int>& ury)
// {

// //{{{

//   	cout<<"Reading & Writing GDS & Gen. txt file for debugging"<<endl;
//   	rndnum++;
// 	string GDS_txt = "GDS_Building_Block_" + to_string(rndnum)+".txt";
// 	cout<<"GDS_txt: "<< GDS_txt<<endl;

// 	string GDS_txt_location = "./router/GDS_To_ASCII/" + GDS_txt;

// 	ofstream output_GDS_txt;
// 	output_GDS_txt.open(GDS_txt_location);

// 	//blockGDS_file_name.push_back(GDS_txt_location);

// 	cout <<"#BLOCKS: "<<rndnum<<endl;
// 	EnumDataBase edb;
// 	cout << "TEST enum API"<<endl;
// 	GdsParser::read(edb, GDSData);

//         // + wbxu
// 	cout<<"wbxu testing"<<endl;
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
// 		cout<<"edb.header_db_bitarray: "<<edb.header_db_bitarray[q]<<endl;
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
// 	Pin tempPin;
	
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
//               strname=edb.vInteger_vec_string[string_idx]+"_"+to_string(rndnum);
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
// 	      sname = edb.vInteger_vec_string[string_idx]+"_"+to_string(rndnum);	
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

// void Placer_Router_Cap::WriteGDS(string fpath, string unit_capacitor, string final_gds){
//   //begin to write GDS file from unit capacitor to final capacitor file
//   //inherit from another class !!!
  
//   //initial gw part
//   string gds_unit_capacitor = fpath+"/"+unit_capacitor+".gds";
//   string topGDS_loc = final_gds+".gds";
//   string TopCellName = final_gds;
//   GdsParser::GdsWriter gw(topGDS_loc.c_str());
//   gw.create_lib("test", 0.00025, 2.5e-10);
//   int randnum = 111;
//   //what is this
//   vector<string> uniGDS;
//   for(int i=0;i<1;i++){
//      uniGDS.push_back(gds_unit_capacitor);
//      }

//   vector<string> strBlocks;
//   vector<int> llx, lly, urx, ury;
//   map<string,int> gdsMap2strBlock;
//   int rndnum=111;
//   vector<string> strBlocks_Top;
//   int idx=0;
//   //writing unit capacitors??? confirm with jinhyun
//   for(int i=0;i<uniGDS.size();i++){
//      GDSReaderWriterTxTFile_extension(gds_unit_capacitor, gw, rndnum, strBlocks, llx, lly, urx, ury);
//      strBlocks_Top.push_back(strBlocks.back());
//      gdsMap2strBlock.insert(make_pair(gds_unit_capacitor,idx));
//      idx++;
//   }
//   //writing metals
//   int x[5], y[5];
  
//   gw.gds_write_bgnstr();
//   gw.gds_flush();
//   gw.gds_write_strname(TopCellName.c_str());
//   gw.gds_flush();

//   string MaskID_M1 = "19";
//   string MaskID_V1 = "21";
//   string MaskID_M2 = "20";
//   string MaskID_V2 = "25";
//   string MaskID_M3 = "30";
//   string MaskID_V3 = "35";
//   string MaskID_M4 = "40";
//   string MaskID_V4 = "45";
//   string MaskID_M5 = "50";
//   string MaskID_V5 = "55";
//   string MaskID_M6 = "60";
//   string MaskID_V6 = "65";
//   string MaskID_M7 = "70";
//   string MaskID_V7 = "75";
//   int width = metal_width[0];
//   int Min_x = INT_MAX;
//   int Min_y = INT_MAX;
//   int Max_x = INT_MIN;
//   int Max_y = INT_MIN;
//   //for positive nets
  
//   for(int i=0; i< Nets_pos.size(); i++){//for each net
//       PnRDB::pin temp_Pins;
//       for(int j=0; j< Nets_pos[i].start_conection_coord.size();j++){ //for segment
//           if(Nets_pos[i].start_conection_coord[j].first == Nets_pos[i].end_conection_coord[j].first){//distance need to be modified then
//              if(Nets_pos[i].start_conection_coord[j].second<Nets_pos[i].end_conection_coord[j].second){
//                 x[0]= Nets_pos[i].start_conection_coord[j].first-width+offset_x;
//                 x[1]= Nets_pos[i].end_conection_coord[j].first-width+offset_x;
//                 x[2]= Nets_pos[i].end_conection_coord[j].first+width+offset_x;
//                 x[3]= Nets_pos[i].start_conection_coord[j].first+width+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_pos[i].start_conection_coord[j].second+offset_y;
//                 y[1]= Nets_pos[i].end_conection_coord[j].second+offset_y;
//                 y[2]= Nets_pos[i].end_conection_coord[j].second+offset_y;
//                 y[3]= Nets_pos[i].start_conection_coord[j].second+offset_y;
//                 y[4]=y[0];
                
//                }else{

//                 x[0]= Nets_pos[i].end_conection_coord[j].first-width+offset_x;
//                 x[1]= Nets_pos[i].start_conection_coord[j].first-width+offset_x;
//                 x[2]= Nets_pos[i].start_conection_coord[j].first+width+offset_x;
//                 x[3]= Nets_pos[i].end_conection_coord[j].first+width+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_pos[i].end_conection_coord[j].second+offset_y;
//                 y[1]= Nets_pos[i].start_conection_coord[j].second+offset_y;
//                 y[2]= Nets_pos[i].start_conection_coord[j].second+offset_y;
//                 y[3]= Nets_pos[i].end_conection_coord[j].second+offset_y;
//                 y[4]=y[0];

//                }
//           }else{
//              if(Nets_pos[i].start_conection_coord[j].first<Nets_pos[i].end_conection_coord[j].first){

//                 x[0]= Nets_pos[i].start_conection_coord[j].first+offset_x;
//                 x[1]= Nets_pos[i].start_conection_coord[j].first+offset_x;
//                 x[2]= Nets_pos[i].end_conection_coord[j].first+offset_x;
//                 x[3]= Nets_pos[i].end_conection_coord[j].first+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_pos[i].start_conection_coord[j].second-width+offset_y;
//                 y[1]= Nets_pos[i].start_conection_coord[j].second+width+offset_y;
//                 y[2]= Nets_pos[i].end_conection_coord[j].second+width+offset_y;
//                 y[3]= Nets_pos[i].end_conection_coord[j].second-width+offset_y;
//                 y[4]=y[0];

//                }else{
    
//                 x[0]= Nets_pos[i].end_conection_coord[j].first+offset_x;
//                 x[1]= Nets_pos[i].end_conection_coord[j].first+offset_x;
//                 x[2]= Nets_pos[i].start_conection_coord[j].first+offset_x;
//                 x[3]= Nets_pos[i].start_conection_coord[j].first+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_pos[i].end_conection_coord[j].second-width+offset_y;
//                 y[1]= Nets_pos[i].end_conection_coord[j].second+width+offset_y;
//                 y[2]= Nets_pos[i].start_conection_coord[j].second+width+offset_y;
//                 y[3]= Nets_pos[i].start_conection_coord[j].second-width+offset_y;
//                 y[4]=y[0];
       
//                }
//             }
            
//             if(x[0]<Min_x){Min_x = x[0];}
//             if(x[2]>Max_x){Max_x = x[2];}
//             if(y[0]<Min_y){Min_y = y[0];}
//             if(y[2]>Max_y){Max_y = y[2];}

//             PnRDB::point temp_point;
//             PnRDB::contact temp_contact;
            
//             temp_point.x = x[0];
//             temp_point.y = y[0];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.LL = temp_point;

//             if(temp_contact.originBox.LL.x == 9510 and temp_contact.originBox.LL.y == -552){
//                 cout<<"Found Error"<<endl;
//                 cout<<x[0]<<" "<<y[0]<<endl;
//                 cout<<x[1]<<" "<<y[1]<<endl;
//                 cout<<x[2]<<" "<<y[2]<<endl;
//                 cout<<x[3]<<" "<<y[3]<<endl;
//                 cout<<x[4]<<" "<<y[4]<<endl;
//                 cout<<"Start point"<<Nets_pos[i].start_conection_coord[j].first<<" "<<Nets_pos[i].start_conection_coord[j].second<<endl;
//                 cout<<"Start point"<<Nets_pos[i].end_conection_coord[j].first<<" "<<Nets_pos[i].end_conection_coord[j].second<<endl;
//                 cout<<"Error end"<<endl;
//               }
            
//             temp_point.x = x[1];
//             temp_point.y = y[1];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.UL = temp_point;
            
//             temp_point.x = x[2];
//             temp_point.y = y[2];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.UR = temp_point;

//             temp_point.x = x[3];
//             temp_point.y = y[3];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.LR = temp_point;

//             temp_contact.originCenter.x = (x[0]+x[2])/2;
//             temp_contact.originCenter.y = (y[0]+y[2])/2;
            

//             x[0]=2*x[0];
//             x[1]=2*x[1];    
//             x[2]=2*x[2];
//             x[3]=2*x[3];
//             x[4]=2*x[4];
            
//             y[0]=2*y[0];
//             y[1]=2*y[1];
//             y[2]=2*y[2];
//             y[3]=2*y[3];
//             y[4]=2*y[4];

//             if(Nets_pos[i].metal[j] == "M1"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M1));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M1";
//              }else if(Nets_pos[i].metal[j] == "M2"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M2));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M2";
//              }else if(Nets_pos[i].metal[j] == "M3"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M3));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M3";
//              }else if(Nets_pos[i].metal[j] == "M4"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M4));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M4";
//              }else if(Nets_pos[i].metal[j] == "M5"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M5));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M5";
//              }else if(Nets_pos[i].metal[j] == "M6"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M6));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M6";
//              }else if(Nets_pos[i].metal[j] == "M7"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M7));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M7";
//              }

//              if(Nets_pos[i].Is_pin[j] == 1){
//                 temp_Pins.name = Nets_pos[i].name;
//                 temp_Pins.pinContacts.push_back(temp_contact);
//                }
//              CheckOutBlock.interMetals.push_back(temp_contact);
//          }   
//        CheckOutBlock.blockPins.push_back(temp_Pins);
//      }
  

  
//   //for neg nets
//   for(int i=0; i< Nets_neg.size(); i++){//for each net
//       PnRDB::pin temp_Pins_neg;
//       for(int j=0; j< Nets_neg[i].start_conection_coord.size();j++){ //for segment
//           if(Nets_neg[i].start_conection_coord[j].first == Nets_neg[i].end_conection_coord[j].first){//distance need to be modified then
//              if(Nets_neg[i].start_conection_coord[j].second<Nets_neg[i].end_conection_coord[j].second){
//                 x[0]= Nets_neg[i].start_conection_coord[j].first-width+offset_x;
//                 x[1]= Nets_neg[i].end_conection_coord[j].first-width+offset_x;
//                 x[2]= Nets_neg[i].end_conection_coord[j].first+width+offset_x;
//                 x[3]= Nets_neg[i].start_conection_coord[j].first+width+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_neg[i].start_conection_coord[j].second+offset_y;
//                 y[1]= Nets_neg[i].end_conection_coord[j].second+offset_y;
//                 y[2]= Nets_neg[i].end_conection_coord[j].second+offset_y;
//                 y[3]= Nets_neg[i].start_conection_coord[j].second+offset_y;
//                 y[4]=y[0];
                
//                }else{

//                 x[0]= Nets_neg[i].end_conection_coord[j].first-width+offset_x;
//                 x[1]= Nets_neg[i].start_conection_coord[j].first-width+offset_x;
//                 x[2]= Nets_neg[i].start_conection_coord[j].first+width+offset_x;
//                 x[3]= Nets_neg[i].end_conection_coord[j].first+width+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_neg[i].end_conection_coord[j].second+offset_y;
//                 y[1]= Nets_neg[i].start_conection_coord[j].second+offset_y;
//                 y[2]= Nets_neg[i].start_conection_coord[j].second+offset_y;
//                 y[3]= Nets_neg[i].end_conection_coord[j].second+offset_y;
//                 y[4]=y[0];

//                }
//           }else{
//              if(Nets_neg[i].start_conection_coord[j].first<Nets_neg[i].end_conection_coord[j].first){

//                 x[0]= Nets_neg[i].start_conection_coord[j].first+offset_x;
//                 x[1]= Nets_neg[i].start_conection_coord[j].first+offset_x;
//                 x[2]= Nets_neg[i].end_conection_coord[j].first+offset_x;
//                 x[3]= Nets_neg[i].end_conection_coord[j].first+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_neg[i].start_conection_coord[j].second-width+offset_y;
//                 y[1]= Nets_neg[i].start_conection_coord[j].second+width+offset_y;
//                 y[2]= Nets_neg[i].end_conection_coord[j].second+width+offset_y;
//                 y[3]= Nets_neg[i].end_conection_coord[j].second-width+offset_y;
//                 y[4]=y[0];

//                }else{
    
//                 x[0]= Nets_neg[i].end_conection_coord[j].first+offset_x;
//                 x[1]= Nets_neg[i].end_conection_coord[j].first+offset_x;
//                 x[2]= Nets_neg[i].start_conection_coord[j].first+offset_x;
//                 x[3]= Nets_neg[i].start_conection_coord[j].first+offset_x;
//                 x[4]= x[0];
             
//                 y[0]= Nets_neg[i].end_conection_coord[j].second-width+offset_y;
//                 y[1]= Nets_neg[i].end_conection_coord[j].second+width+offset_y;
//                 y[2]= Nets_neg[i].start_conection_coord[j].second+width+offset_y;
//                 y[3]= Nets_neg[i].start_conection_coord[j].second-width+offset_y;
//                 y[4]=y[0];
       
//                }
//             }
            
//             PnRDB::point temp_point;
//             PnRDB::contact temp_contact;

//             if(x[0]<Min_x){Min_x = x[0];}
//             if(x[2]>Max_x){Max_x = x[2];}
//             if(y[0]<Min_y){Min_y = y[0];}
//             if(y[2]>Max_y){Max_y = y[2];}

//             temp_point.x = x[0];
//             temp_point.y = y[0];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.LL = temp_point;
            
//             temp_point.x = x[1];
//             temp_point.y = y[1];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.UL = temp_point;
            
//             temp_point.x = x[2];
//             temp_point.y = y[2];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.UR = temp_point;

//             temp_point.x = x[3];
//             temp_point.y = y[3];
//             temp_contact.originBox.polygon.push_back(temp_point);
//             temp_contact.originBox.LR = temp_point;

//             temp_contact.originCenter.x = (x[0]+x[2])/2;
//             temp_contact.originCenter.y = (y[0]+y[2])/2;

//             x[0]=2*x[0];
//             x[1]=2*x[1];    
//             x[2]=2*x[2];
//             x[3]=2*x[3];
//             x[4]=2*x[4];
            
//             y[0]=2*y[0];
//             y[1]=2*y[1];
//             y[2]=2*y[2];
//             y[3]=2*y[3];
//             y[4]=2*y[4];

//             if(Nets_neg[i].metal[j] == "M1"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M1));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M1";
//              }else if(Nets_neg[i].metal[j] == "M2"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M2));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M2";
//              }else if(Nets_neg[i].metal[j] == "M3"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M3));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M3";
//              }else if(Nets_neg[i].metal[j] == "M4"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M4));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M4";
//              }else if(Nets_neg[i].metal[j] == "M5"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M5));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M5";
//              }else if(Nets_neg[i].metal[j] == "M6"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M6));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M6";
//              }else if(Nets_neg[i].metal[j] == "M7"){	
//               gw.gds_write_boundary();
//               gw.gds_flush();
//               gw.gds_write_layer(stoi(MaskID_M7));
//               gw.gds_flush();
//               gw.gds_write_datatype(0);
//               gw.gds_flush();
//               gw.gds_write_xy(x,y,5);
//               gw.gds_flush();
//               gw.gds_write_endel();
//               gw.gds_flush();
//               temp_contact.metal = "M7";
//              }
//                if(Nets_neg[i].Is_pin[j] == 1){
                
//                 temp_Pins_neg.name = Nets_neg[i].name;
//                 temp_Pins_neg.pinContacts.push_back(temp_contact);
       
//                }
//              CheckOutBlock.interMetals.push_back(temp_contact);
//          }
//        CheckOutBlock.blockPins.push_back(temp_Pins_neg);
//      }
  
//   //wirting vias
//   //for positive net
//   width = via_width[0];
//   for(int i=0;i<Nets_pos.size();i++){
//      for(int j=0;j<Nets_pos[i].via.size();j++){//the size of via needs to be modified according to different PDK
 
//         x[0]=Nets_pos[i].via[j].first - width+offset_x;
//         x[1]=Nets_pos[i].via[j].first - width+offset_x;
//         x[2]=Nets_pos[i].via[j].first + width+offset_x;
//         x[3]=Nets_pos[i].via[j].first + width+offset_x;
//         x[4]=x[0];
        
//         y[0]=Nets_pos[i].via[j].second - width+offset_y;
//         y[1]=Nets_pos[i].via[j].second + width+offset_y;
//         y[2]=Nets_pos[i].via[j].second + width+offset_y;
//         y[3]=Nets_pos[i].via[j].second - width+offset_y;
//         y[4]=y[0];
        
//         PnRDB::point temp_point;
//         PnRDB::contact temp_contact;

//         if(x[0]<Min_x){Min_x = x[0];}
//         if(x[2]>Max_x){Max_x = x[2];}
//         if(y[0]<Min_y){Min_y = y[0];}
//         if(y[2]>Max_y){Max_y = y[2];}

//         temp_point.x = x[0];
//         temp_point.y = y[0];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.LL = temp_point;
            
//         temp_point.x = x[1];
//         temp_point.y = y[1];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.UL = temp_point;
            
//         temp_point.x = x[2];
//         temp_point.y = y[2];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.UR = temp_point;

//         temp_point.x = x[3];
//         temp_point.y = y[3];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.LR = temp_point;

//         temp_contact.originCenter.x = (x[0]+x[2])/2;
//         temp_contact.originCenter.y = (y[0]+y[2])/2;
        
       
//         x[0]=2*x[0];
//         x[1]=2*x[1];    
//         x[2]=2*x[2];
//         x[3]=2*x[3];
//         x[4]=2*x[4];
            
//         y[0]=2*y[0];
//         y[1]=2*y[1];
//         y[2]=2*y[2];
//         y[3]=2*y[3];
//         y[4]=2*y[4];  
    
//         PnRDB::Via temp_via;
//         PnRDB::contact upper_contact;
//         PnRDB::contact lower_contact;
//         upper_contact.placedCenter = temp_contact.placedCenter;
//         lower_contact.placedCenter = temp_contact.placedCenter;

//         PnRDB::contact h_contact;
//         h_contact.originBox.LL = temp_contact.originBox.LL;
//         h_contact.originBox.UL = temp_contact.originBox.UL;
//         h_contact.originBox.UR = temp_contact.originBox.UR;
//         h_contact.originBox.LR = temp_contact.originBox.LR;
//         h_contact.originBox.LL.y = temp_contact.originBox.LL.y-(via_cover[0]-via_width[0]);
//         h_contact.originBox.UL.y = temp_contact.originBox.UL.y+(via_cover[0]-via_width[0]);
//         h_contact.originBox.UR.y = temp_contact.originBox.UR.y+(via_cover[0]-via_width[0]);
//         h_contact.originBox.LR.y = temp_contact.originBox.LR.y-(via_cover[0]-via_width[0]);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.LL);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.UL);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.UR);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.LR);

//         PnRDB::contact v_contact;
//         v_contact.originBox.LL = temp_contact.originBox.LL;
//         v_contact.originBox.UL = temp_contact.originBox.UL;
//         v_contact.originBox.UR = temp_contact.originBox.UR;
//         v_contact.originBox.LR = temp_contact.originBox.LR;
//         v_contact.originBox.LL.x = temp_contact.originBox.LL.x-(via_cover[0]-via_width[0]);
//         v_contact.originBox.UL.x = temp_contact.originBox.UL.x-(via_cover[0]-via_width[0]);
//         v_contact.originBox.UR.x = temp_contact.originBox.UR.x+(via_cover[0]-via_width[0]);
//         v_contact.originBox.LR.x = temp_contact.originBox.LR.x+(via_cover[0]-via_width[0]);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.LL);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.UL);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.UR);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.LR);

//         if(Nets_pos[i].via_metal[j].compare("M1")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V1));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V1";
//            lower_contact.metal = "M1";
//            upper_contact.metal = "M2";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 0;
//           }else if(Nets_pos[i].via_metal[j].compare("M2")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V2));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V2";
//            lower_contact.metal = "M2";
//            upper_contact.metal = "M3";
//            lower_contact.originBox = h_contact.originBox;
//            upper_contact.originBox = v_contact.originBox;
//            temp_via.model_index = 1;
//           }else if(Nets_pos[i].via_metal[j].compare("M3")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V3));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V3";
//            lower_contact.metal = "M3";
//            upper_contact.metal = "M4";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 2;
//           }else if(Nets_pos[i].via_metal[j].compare("M4")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V4));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V4";
//            lower_contact.metal = "M4";
//            upper_contact.metal = "M5";
//            lower_contact.originBox = h_contact.originBox;
//            upper_contact.originBox = v_contact.originBox;
//            temp_via.model_index = 3;
//           }else if(Nets_pos[i].via_metal[j].compare("M5")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V5));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V5";
//            lower_contact.metal = "M5";
//            upper_contact.metal = "M6";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 4;
//           }else if(Nets_pos[i].via_metal[j].compare("M6")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V6));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V6";
//            lower_contact.metal = "M6";
//            upper_contact.metal = "M7";
//            lower_contact.originBox = h_contact.originBox;
//            upper_contact.originBox = v_contact.originBox;
//            temp_via.model_index = 5;
//           }else if(Nets_pos[i].via_metal[j].compare("M7")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V7));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V7";
//            lower_contact.metal = "M7";
//            upper_contact.metal = "M8";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 6;
//           }
//          temp_via.placedpos = temp_contact.originCenter;
//          temp_via.ViaRect = temp_contact;
//          temp_via.LowerMetalRect = lower_contact;
//          temp_via.UpperMetalRect = upper_contact;
//          CheckOutBlock.interVias.push_back(temp_via);

        
//        }
//     }
    
//     //for negative net
//   for(int i=0;i<Nets_neg.size();i++){
//      for(int j=0;j<Nets_neg[i].via.size();j++){//the size of via needs to be modified according to different PDK
 
//         x[0]=Nets_neg[i].via[j].first - width+offset_x;
//         x[1]=Nets_neg[i].via[j].first - width+offset_x;
//         x[2]=Nets_neg[i].via[j].first + width+offset_x;
//         x[3]=Nets_neg[i].via[j].first + width+offset_x;
//         x[4]=x[0];
        
//         y[0]=Nets_neg[i].via[j].second - width+offset_y;
//         y[1]=Nets_neg[i].via[j].second + width+offset_y;
//         y[2]=Nets_neg[i].via[j].second + width+offset_y;
//         y[3]=Nets_neg[i].via[j].second - width+offset_y;
//         y[4]=y[0];
        
//         PnRDB::point temp_point;
//         PnRDB::contact temp_contact;

//         if(x[0]<Min_x){Min_x = x[0];}
//         if(x[2]>Max_x){Max_x = x[2];}
//         if(y[0]<Min_y){Min_y = y[0];}
//         if(y[2]>Max_y){Max_y = y[2];}

//         temp_point.x = x[0];
//         temp_point.y = y[0];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.LL = temp_point;
            
//         temp_point.x = x[1];
//         temp_point.y = y[1];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.UL = temp_point;
            
//         temp_point.x = x[2];
//         temp_point.y = y[2];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.UR = temp_point;

//         temp_point.x = x[3];
//         temp_point.y = y[3];
//         temp_contact.originBox.polygon.push_back(temp_point);
//         temp_contact.originBox.LR = temp_point;

//         temp_contact.originCenter.x = (x[0]+x[2])/2;
//         temp_contact.originCenter.y = (y[0]+y[2])/2;

//         x[0]=2*x[0];
//         x[1]=2*x[1];    
//         x[2]=2*x[2];
//         x[3]=2*x[3];
//         x[4]=2*x[4];
            
//         y[0]=2*y[0];
//         y[1]=2*y[1];
//         y[2]=2*y[2];
//         y[3]=2*y[3];
//         y[4]=2*y[4];

//         PnRDB::Via temp_via;
//         PnRDB::contact upper_contact;
//         PnRDB::contact lower_contact;
//         upper_contact.placedCenter = temp_contact.placedCenter;
//         lower_contact.placedCenter = temp_contact.placedCenter;

//         PnRDB::contact h_contact;
//         h_contact.originBox.LL = temp_contact.originBox.LL;
//         h_contact.originBox.UL = temp_contact.originBox.UL;
//         h_contact.originBox.UR = temp_contact.originBox.UR;
//         h_contact.originBox.LR = temp_contact.originBox.LR;
//         h_contact.originBox.LL.y = temp_contact.originBox.LL.y-(via_cover[0]-via_width[0]);
//         h_contact.originBox.UL.y = temp_contact.originBox.UL.y+(via_cover[0]-via_width[0]);
//         h_contact.originBox.UR.y = temp_contact.originBox.UR.y+(via_cover[0]-via_width[0]);
//         h_contact.originBox.LR.y = temp_contact.originBox.LR.y-(via_cover[0]-via_width[0]);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.LL);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.UL);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.UR);
//         h_contact.originBox.polygon.push_back(h_contact.originBox.LR);

//         PnRDB::contact v_contact;
//         v_contact.originBox.LL = temp_contact.originBox.LL;
//         v_contact.originBox.UL = temp_contact.originBox.UL;
//         v_contact.originBox.UR = temp_contact.originBox.UR;
//         v_contact.originBox.LR = temp_contact.originBox.LR;
//         v_contact.originBox.LL.x = temp_contact.originBox.LL.x-(via_cover[0]-via_width[0]);
//         v_contact.originBox.UL.x = temp_contact.originBox.UL.x-(via_cover[0]-via_width[0]);
//         v_contact.originBox.UR.x = temp_contact.originBox.UR.x+(via_cover[0]-via_width[0]);
//         v_contact.originBox.LR.x = temp_contact.originBox.LR.x+(via_cover[0]-via_width[0]);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.LL);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.UL);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.UR);
//         v_contact.originBox.polygon.push_back(v_contact.originBox.LR);

//         if(Nets_neg[i].via_metal[j].compare("M1")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V1));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V1";
//            lower_contact.metal = "M1";
//            upper_contact.metal = "M2";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 0;
//           }else if(Nets_neg[i].via_metal[j].compare("M2")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V2));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V2";
//            lower_contact.metal = "M2";
//            upper_contact.metal = "M3";
//            lower_contact.originBox = h_contact.originBox;
//            upper_contact.originBox = v_contact.originBox;
//            temp_via.model_index = 1;
//           }else if(Nets_neg[i].via_metal[j].compare("M3")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V3));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V3";
//            lower_contact.metal = "M3";
//            upper_contact.metal = "M4";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 2;
//           }else if(Nets_neg[i].via_metal[j].compare("M4")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V4));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V4";
//            lower_contact.metal = "M4";
//            upper_contact.metal = "M5";
//            lower_contact.originBox = h_contact.originBox;
//            upper_contact.originBox = v_contact.originBox;
//            temp_via.model_index = 3;
//           }else if(Nets_neg[i].via_metal[j].compare("M5")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V5));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V5";
//            lower_contact.metal = "M5";
//            upper_contact.metal = "M6";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 4;
//           }else if(Nets_neg[i].via_metal[j].compare("M6")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V6));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V6";
//            lower_contact.metal = "M6";
//            upper_contact.metal = "M7";
//            lower_contact.originBox = h_contact.originBox;
//            upper_contact.originBox = v_contact.originBox;
//            temp_via.model_index = 5;
//           }else if(Nets_neg[i].via_metal[j].compare("M7")==0){
           
//            gw.gds_write_boundary();
//            gw.gds_write_layer(stoi(MaskID_V7));
//            gw.gds_write_datatype(0);
//            gw.gds_write_xy(x,y,5);
//            gw.gds_write_endel();
//            gw.gds_flush();
//            temp_contact.metal = "V7";
//            lower_contact.metal = "M7";
//            upper_contact.metal = "M8";
//            lower_contact.originBox = v_contact.originBox;
//            upper_contact.originBox = h_contact.originBox;
//            temp_via.model_index = 6;
//           }
//          temp_via.placedpos = temp_contact.originCenter;
//          temp_via.ViaRect = temp_contact;
//          temp_via.LowerMetalRect = lower_contact;
//          temp_via.UpperMetalRect = upper_contact;
//          CheckOutBlock.interVias.push_back(temp_via);
//        }
//     }
//   CheckOutBlock.orient = PnRDB::Omark(0); //need modify
  
//   for(int i= 0; i<Caps.size();i++){
//       x[0]=Caps[i].x - unit_cap_demension.first/2+offset_x;
//       x[1]=Caps[i].x - unit_cap_demension.first/2+offset_x;
//       x[2]=Caps[i].x + unit_cap_demension.first/2+offset_x;
//       x[3]=Caps[i].x + unit_cap_demension.first/2+offset_x;
//       x[4]=x[0];
       
//       y[0]=Caps[i].y - unit_cap_demension.second/2+offset_y;
//       y[1]=Caps[i].y + unit_cap_demension.second/2+offset_y;
//       y[2]=Caps[i].y + unit_cap_demension.second/2+offset_y;
//       y[3]=Caps[i].y - unit_cap_demension.second/2+offset_y;
//       y[4]=y[0];
     
//       PnRDB::point temp_point;
//       PnRDB::contact temp_contact;

//       if(x[0]<Min_x){Min_x = x[0];}
//       if(x[2]>Max_x){Max_x = x[2];}
//       if(y[0]<Min_y){Min_y = y[0];}
//       if(y[2]>Max_y){Max_y = y[2];}
 
//       temp_point.x = x[0];
//       temp_point.y = y[0];
//       temp_contact.originBox.polygon.push_back(temp_point);
//       temp_contact.originBox.LL = temp_point;
            
//       temp_point.x = x[1];
//       temp_point.y = y[1];
//       temp_contact.originBox.polygon.push_back(temp_point);
//       temp_contact.originBox.UL = temp_point;
            
//       temp_point.x = x[2];
//       temp_point.y = y[2];
//       temp_contact.originBox.polygon.push_back(temp_point);
//       temp_contact.originBox.UR = temp_point;

//       temp_point.x = x[3];
//       temp_point.y = y[3];
//       temp_contact.originBox.polygon.push_back(temp_point);
//       temp_contact.originBox.LR = temp_point;

//       temp_contact.originCenter.x = (x[0]+x[2])/2;
//       temp_contact.originCenter.y = (y[0]+y[2])/2;
      
//       temp_contact.metal = "M1";
//       CheckOutBlock.interMetals.push_back(temp_contact);
//       temp_contact.metal = "M2";
//       CheckOutBlock.interMetals.push_back(temp_contact);
//       temp_contact.metal = "M3";
//       CheckOutBlock.interMetals.push_back(temp_contact);
      
//      }


//   CheckOutBlock.gdsFile = topGDS_loc;
//   PnRDB::point temp_point;
//   temp_point.x = Min_x;
//   temp_point.y = Min_y;
//   CheckOutBlock.originBox.polygon.push_back(temp_point);
//   CheckOutBlock.originBox.LL = temp_point;
//   temp_point.x = Min_x;
//   temp_point.y = Max_y;
//   CheckOutBlock.originBox.polygon.push_back(temp_point);
//   CheckOutBlock.originBox.UL = temp_point;
//   temp_point.x = Max_x;
//   temp_point.y = Max_y;
//   CheckOutBlock.originBox.polygon.push_back(temp_point);
//   CheckOutBlock.originBox.UR = temp_point;
//   temp_point.x = Max_x;
//   temp_point.y = Min_y;
//   CheckOutBlock.originBox.polygon.push_back(temp_point);
//   CheckOutBlock.originBox.LR = temp_point;
//   CheckOutBlock.originCenter.x = (CheckOutBlock.originBox.LL.x + CheckOutBlock.originBox.UR.x)/2;
//   CheckOutBlock.originCenter.y = (CheckOutBlock.originBox.LL.y + CheckOutBlock.originBox.UR.y)/2;
//   CheckOutBlock.width = CheckOutBlock.originBox.UR.x-CheckOutBlock.originBox.LL.x;
//   CheckOutBlock.height = CheckOutBlock.originBox.UR.y-CheckOutBlock.originBox.LL.y;
  
//   //wirte orientation for each cap
//   for(int i=0;i<Caps.size();i++){
//      //int index = gdsMap2strBlock[];
//      gw.gds_write_sref();
//      gw.gds_write_sname(strBlocks_Top[0].c_str());
//      gw.gds_flush();
//      x[0]=Caps[i].x+offset_x;
//      y[0]=Caps[i].y+offset_y;
//      gw.gds_write_strans(false,false,false);gw.gds_write_angle(0);//N 
//      gw.gds_flush();
//      x[0]=2*(Caps[i].x-unit_cap_demension.first/2+offset_x);
//      y[0]=2*(Caps[i].y-unit_cap_demension.second/2+offset_y);
//      gw.gds_write_xy(x,y,1);
//      gw.gds_write_endel();
//      gw.gds_flush();
//     }
//   gw.gds_write_endstr();
//   gw.gds_write_endlib();
//   gw.gds_flush();
  

// }

void Placer_Router_Cap::Common_centroid_capacitor(string fpath, PnRDB::hierNode& current_node){

  for(int i = 0;i<current_node.Blocks.size();i++){
       if(current_node.Blocks[i].instance.isLeaf == 1 and current_node.Blocks[i].instance.gdsFile ==""){
            //this block must be CC
            vector<int> ki;
            vector<pair<string, string> > pin_names;
            string unit_capacitor;
            string final_gds;
            pair<string, string> pins;
            for(int j=0;j<current_node.CC_Caps.size();j++){
                 if(current_node.CC_Caps[j].CCCap_name == current_node.Blocks[i].instance.name){
                      ki = current_node.CC_Caps[j].size;
                      unit_capacitor = current_node.CC_Caps[j].Unit_capacitor;
                      final_gds = current_node.Blocks[i].instance.master;
                      int pin_index = 0;
                      while(pin_index <current_node.Blocks[i].instance.blockPins.size()){
                         pins.first = current_node.Blocks[i].instance.blockPins[pin_index].name;
                         pins.second = current_node.Blocks[i].instance.blockPins[pin_index+1].name;
                         pin_names.push_back(pins);
                         pin_index = pin_index + 2;
                      }
                      Placer_Router_Cap PRC(ki, pin_names, fpath, unit_capacitor, final_gds);
                      PnRDB::block temp_block=PRC.CheckoutData();
                      //feedback data
                      current_node.Blocks[i].instance.width = temp_block.width;
                      current_node.Blocks[i].instance.height = temp_block.height;
                      current_node.Blocks[i].instance.originBox = temp_block.originBox;
                      current_node.Blocks[i].instance.originCenter = temp_block.originCenter;
                      current_node.Blocks[i].instance.gdsFile = temp_block.gdsFile;
                      current_node.Blocks[i].instance.orient = temp_block.orient;
                      current_node.Blocks[i].instance.interMetals = temp_block.interMetals;
                      current_node.Blocks[i].instance.interVias = temp_block.interVias;
                      for(int k=0;k<current_node.Blocks[i].instance.blockPins.size();k++){
                          for(int l=0;l<temp_block.blockPins.size();l++){
                               if(current_node.Blocks[i].instance.blockPins[k].name == temp_block.blockPins[l].name){    
                                  for(int p=0;p<temp_block.blockPins[l].pinContacts.size();p++){
                                        current_node.Blocks[i].instance.blockPins[k].pinContacts.push_back(temp_block.blockPins[l].pinContacts[p]);
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
