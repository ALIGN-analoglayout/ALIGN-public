#include "A_star.h"

A_star::A_star(Grid& grid, bool shielding):drc_info(grid.drc_info){

  this->path_number=1;
  source = grid.Source;
  dest = grid.Dest;
  this->shielding = shielding;

};


bool A_star::FindFeasiblePath(Grid& grid, int pathNo, int left_up, int right_down) {

  
  bool mark=false;
  for(int i =0;i<pathNo;++i){
    
     std::cout<<"Path No "<<pathNo<<" current path index "<<i<<std::endl;
     //find one shortest path

     std::vector<int> temp_path;
     
     std::cout<<"start A_star "<<std::endl;

     temp_path = A_star_algorithm(grid, left_up, right_down);// grid.Source grid.dest
     
     std::cout<<"end A_star"<<std::endl; 
     if((int)temp_path.size()>0) {
     //return the shortest path
     Path.push_back(temp_path);
     CopyPath(grid, left_up, right_down);
     mark=true;
     } else {
       mark=(mark or false);
       std::cout<<"Router-Warning: feasible path might not be found\n";
     }
  }
  return mark;

}

std::vector<std::vector<RouterDB::Metal> > A_star::ConvertPathintoPhysical(Grid& grid){

  std::vector<std::vector<RouterDB::Metal> > Phsical_Path;
  for(int i= 0; i<(int) Path.size();++i){
      std::vector<RouterDB::Metal> temp_physical_path;
      //int start_index = 0;
      //int end_index = 0;
      int flag_start_write = 1;
      //int flag_end_write = 0;
      RouterDB::point temp_point;
      RouterDB::Metal temp_metal;
      for(int j=0;j<(int) Path[i].size();++j){
          if(flag_start_write == 1){
              temp_metal.LinePoint.clear();
              temp_metal.MetalIdx = grid.vertices_total[Path[i][j]].metal;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              flag_start_write = 0;
            }
           if(j<(int) Path[i].size()-1 and grid.vertices_total[Path[i][j]].metal!=grid.vertices_total[Path[i][j+1]].metal){
              flag_start_write = 1;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              temp_metal.width = grid.drc_info.Metal_info[grid.vertices_total[Path[i][j]].metal].width;
              temp_physical_path.push_back(temp_metal);
            }
            if(j==(int) Path[i].size()-1 and flag_start_write == 0){

              flag_start_write = 1;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              temp_metal.width = grid.drc_info.Metal_info[grid.vertices_total[Path[i][j]].metal].width;
              temp_physical_path.push_back(temp_metal);
            }
            
         }
      Phsical_Path.push_back(temp_physical_path);
     }

  return Phsical_Path;
};

int A_star::Manhattan_distan(int sindex, Grid& grid){

  std::set<int> Mdis;

  for(int i=0;i<(int) dest.size();i++){

      int temp_dis = abs(grid.vertices_total[sindex].x - grid.vertices_total[dest[i]].x)+abs(grid.vertices_total[sindex].y - grid.vertices_total[dest[i]].y);
      Mdis.insert(temp_dis);

     }

  std::set<int>::iterator it;

  it=Mdis.begin();

  int dis = *it;

  return dis;
  
};

void A_star::initial_source(Grid& grid, std::set<std::pair<int,int>, RouterDB::pairComp>& L_list, const std::set<int> &S_or_D, int left_up, int right_down){
  
  std::vector<int> left_up_node, right_down_node;
  for(int i=0;i<(int)source.size();i++){

      //if(Check_Parallel_SD(left_up, right_down, source[i], left_up_node, right_down_node, grid, S_or_D)){
         int Mdis = Manhattan_distan(source[i], grid);
         grid.vertices_total[source[i]].Cost = 0;
         int dis = grid.vertices_total[source[i]].Cost + Mdis;
         std::pair<int,int> temp_pair;
         temp_pair.first = dis;
         temp_pair.second = source[i];
         L_list.insert(temp_pair);
        //}

     }

};

bool A_star::expand_node(std::vector<int> &direction, std::vector<int> &temp_node, Grid &grid){

  for(int i=0;i<(int)direction.size();i++){
 
       if(grid.vertices_total[direction[i]].active and grid.vertices_total[direction[i]].Cost==-1){
       temp_node.push_back(direction[i]);
       }
     }

  if((int)temp_node.size()>0){
    return true;
    }else{
    return false;
    }

};


bool A_star::expand_node_ud(int direction, std::vector<int> &temp_node, Grid &grid){

  if( direction!= -1 and grid.vertices_total[direction].active and grid.vertices_total[direction].Cost==-1){
     temp_node.push_back(direction);
    }

  if((int)temp_node.size()>0){
    return true;
    }else{
    return false;
    }

};


bool A_star::Check_S_Connection_L(std::vector<int> &left_up_node, std::vector<int> &right_down_node, std::set<int> &src_set, Grid &grid){

  for(int i=0;i<(int)left_up_node.size();i++){

       int const_number = i+1;
       int current_index = const_number;
       int current_node = left_up_node[i];

       if(drc_info.Metal_info[grid.vertices_total[left_up_node[i]].metal].direct==1){//heritical

          while(current_index>0){//left, left
                current_node = current_node -1 ;
                current_index = current_index -1;                
                if(current_node < 0 or current_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[current_node].active==0){return 0;}
              }

          //current_node = current_node + 1;
          bool up = 1;
          bool down = 1;

          if(grid.vertices_total[current_node].up !=-1 and grid.vertices_total[grid.vertices_total[current_node].up].active){

             int future_node = grid.vertices_total[current_node].up;
             current_index = const_number;

             while(current_index>0){//down, down
                   future_node = future_node -1 ;
                   current_index = current_index -1;                   
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){up=0;}
                  }
             //future_node = future_node + 1;
              
             if(grid.vertices_total[future_node].down ==-1 or  src_set.find(grid.vertices_total[future_node].down)==src_set.end() ){
                   up=0;
                  }
            }else{
              up=0;
            }

          if(grid.vertices_total[current_node].down !=-1 and grid.vertices_total[grid.vertices_total[current_node].down].active){

             int future_node = grid.vertices_total[current_node].down;
             current_index = const_number;

             while(current_index>0){//down, down
                   future_node = future_node -1 ;
                   current_index = current_index -1;                   
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){down=0;}
                  }
              
             if(grid.vertices_total[future_node].up ==-1 or src_set.find(grid.vertices_total[future_node].up)==src_set.end() ){
                   down=0;
                  }

            }else{
              down=0;
            }

          if(down==0 and up==0){return 0;}

         }else{

          while(current_index>0){//down, down

                current_node = current_node -1 ;
                current_index = current_index -1;                
                if(current_node < 0 or current_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[current_node].active==0){return 0;}

              }
          bool up = 1;
          bool down = 1;

          if(grid.vertices_total[current_node].up !=-1 and grid.vertices_total[grid.vertices_total[current_node].up].active){

             int future_node = grid.vertices_total[current_node].up;
             current_index = const_number;

             while(current_index>0){//down, down

                   future_node = future_node +1 ;
                   current_index = current_index -1;                
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){up=0;}

                  }
              
             if(grid.vertices_total[future_node].down ==-1 or  src_set.find(grid.vertices_total[future_node].down)==src_set.end() ){
                   up=0;
                  }
            }else{
              up=0;
            }

          if(grid.vertices_total[current_node].down !=-1 and grid.vertices_total[grid.vertices_total[current_node].down].active){

             int future_node = grid.vertices_total[current_node].down;
             current_index = const_number;

             while(current_index>0){//down, down

                   future_node = future_node + 1 ;
                   current_index = current_index -1;
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){down=0;}

                  }
              
             if(grid.vertices_total[future_node].up ==-1 or  src_set.find(grid.vertices_total[future_node].up)==src_set.end() ){
                   down=0;
                  }
            }else{
              down=0;
            }

          if(down==0 and up==0){return 0;}

         }

     }


  for(int i=0;i<(int)right_down_node.size();i++){

       int const_number = i+1;
       int current_index = const_number;
       int current_node = right_down_node[i];

       if(drc_info.Metal_info[grid.vertices_total[right_down_node[i]].metal].direct==1){//heritical

          while(current_index>0){//left, left

                current_node = current_node +1 ;
                current_index = current_index -1;                
                if(current_node < 0 or current_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[current_node].active==0){return 0;}

              }
          bool up = 1;
          bool down = 1;

          if(grid.vertices_total[current_node].up !=-1 and grid.vertices_total[grid.vertices_total[current_node].up].active){

             int future_node = grid.vertices_total[current_node].up;
             current_index = const_number;

             while(current_index>0){//down, down

                   future_node = future_node +1 ;
                   current_index = current_index -1;                
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){up=0;}

                  }
              
             if(grid.vertices_total[future_node].down ==-1 or  src_set.find(grid.vertices_total[future_node].down)==src_set.end() ){
                   up=0;
                  }
            }else{
              up=0;
            }

          if(grid.vertices_total[current_node].down !=-1 and grid.vertices_total[grid.vertices_total[current_node].down].active){

             int future_node = grid.vertices_total[current_node].down;
             current_index = const_number;

             while(current_index>0){//down, down

                   future_node = future_node +1 ;
                   current_index = current_index -1;                
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){down=0;}

                  }
              
             if(grid.vertices_total[future_node].up ==-1 or  src_set.find(grid.vertices_total[future_node].up)==src_set.end() ){
                   down=0;
                  }
            }else{
              down=0;
            }

          if(down==0 and up==0){return 0;}

         }else{

          while(current_index>0){//down, down

                current_node = current_node +1 ;
                current_index = current_index -1;                
                if(current_node < 0 or current_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[current_node].active==0){return 0;}

              }
          bool up = 1;
          bool down = 1;

          if(grid.vertices_total[current_node].up !=-1 and grid.vertices_total[grid.vertices_total[current_node].up].active){

             int future_node = grid.vertices_total[current_node].up;
             current_index = const_number;

             while(current_index>0){//down, down

                   future_node = future_node -1 ;
                   current_index = current_index -1;                
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){up=0;}

                  }
              
             if(grid.vertices_total[future_node].down ==-1 or  src_set.find(grid.vertices_total[future_node].down)==src_set.end() ){
                   up=0;
                  }
            }else{
              up=0;
            }

          if(grid.vertices_total[current_node].down !=-1 and grid.vertices_total[grid.vertices_total[current_node].down].active){

             int future_node = grid.vertices_total[current_node].down;
             current_index = const_number;

             while(current_index>0){//down, down
                
                   future_node = future_node - 1 ;
                   current_index = current_index -1;
                   if(future_node < 0 or future_node > (int) grid.vertices_total.size()-1 or grid.vertices_total[future_node].active==0){down=0;}

                  }
              
             if(grid.vertices_total[future_node].up ==-1 or  src_set.find(grid.vertices_total[future_node].up)==src_set.end() ){
                   down=0;
                  }
            }else{
              down=0;
            }

          if(down==0 and up==0){return 0;}

         }

     }

  return 1;
  

};

bool A_star::Check_S_Connection( std::vector<int> &left_up_node, std::vector<int> &right_down_node, std::set<int> &src_set, Grid &grid){

  for(int i=0;i<(int)left_up_node.size();i++){

      if(src_set.find(grid.vertices_total[left_up_node[i]].down)==src_set.end() and src_set.find(grid.vertices_total[left_up_node[i]].up)==src_set.end()){
          return 0;
         }

     }

  for(int i=0;i<(int)right_down_node.size();i++){

      if(src_set.find(grid.vertices_total[right_down_node[i]].down)==src_set.end() and src_set.find(grid.vertices_total[right_down_node[i]].up)==src_set.end()){
          return 0;
         }

     }

  return 1;

};

bool A_star::found_near_node_S(int left_up, int right_down, int current_node, Grid &grid, std::vector<int> &candidate_node, std::set<int> src_set, std::set<int> dest_set){

    std::vector<int> left_up_node;
    std::vector<int> right_down_node;
    //Check_Parallel_Rule(left_up, right_down, current_node, left_up_node, right_down_node, grid);
    
    std::vector<int> north_node, south_node, east_node, west_node, up_node, down_node;
    bool north_found, south_found, east_found, west_found, up_found, down_found;

    //std::cout<<"expand node checkout point1"<<std::endl;
    north_found = expand_node(grid.vertices_total[current_node].north, north_node, grid);
    //std::cout<<"expand node checkout point2"<<std::endl;
    south_found = expand_node(grid.vertices_total[current_node].south, south_node, grid);
    //std::cout<<"expand node checkout point3"<<std::endl;
    east_found = expand_node(grid.vertices_total[current_node].east, east_node, grid);
    //std::cout<<"expand node checkout point4"<<std::endl;
    west_found = expand_node(grid.vertices_total[current_node].west, west_node, grid);
    //std::cout<<"expand node checkout point5"<<std::endl;
    if(grid.vertices_total[current_node].via_active_up){
      up_found = expand_node_ud(grid.vertices_total[current_node].up, up_node, grid);
    }else{
      up_found = false;
    }
    //std::cout<<"expand node checkout point6"<<std::endl;
    if(grid.vertices_total[current_node].via_active_down){
      down_found = expand_node_ud(grid.vertices_total[current_node].down, down_node, grid);
    }else{
      down_found = false;
    }
    //std::cout<<"expand node checkout point7"<<std::endl;

    if(Check_Parallel_Rule(left_up, right_down, current_node, left_up_node, right_down_node, grid) and Check_S_Connection_L( left_up_node, right_down_node, src_set, grid) ){
    if(north_found){
       for(int i=0;i<(int)north_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(north_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, north_node[i], left_up_node1, right_down_node1, grid) ){
         //std::cout<<"expand node checkout point7.1"<<std::endl;
         candidate_node.push_back(north_node[i]);
         }else if(dest_set.find(north_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, north_node[i], left_up_node1, right_down_node1, grid)  and  Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(north_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point8"<<std::endl;
    if(south_found){
       for(int i=0;i<(int)south_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(south_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, south_node[i], left_up_node1, right_down_node1, grid) ){
         //std::cout<<"expand node checkout point8.1"<<std::endl;
         candidate_node.push_back(south_node[i]);
         }else if(dest_set.find(south_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, south_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(south_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point9"<<std::endl;
    if(west_found){
       for(int i=0;i<(int)west_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(west_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, west_node[i], left_up_node1, right_down_node1, grid) ){
         //std::cout<<"expand node checkout point9.1"<<std::endl;
         candidate_node.push_back(west_node[i]);
         }else if(dest_set.find(west_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, west_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(west_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point10"<<std::endl;
    if(east_found){
       for(int i=0;i<(int)east_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(east_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, east_node[i], left_up_node1, right_down_node1, grid) ){
         //std::cout<<"expand node checkout point10.1"<<std::endl;
         candidate_node.push_back(east_node[i]);
         }else if(dest_set.find(east_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, east_node[i], left_up_node1, right_down_node1, grid) and  Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(east_node[i]);
       }
       }
      }
      }
    //std::cout<<"expand node checkout point11"<<std::endl;

    if(up_found){
       for(int i=0;i<(int)up_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       left_up_node.clear();
       right_down_node.clear();
       //std::cout<<"expand node checkout point11.1"<<std::endl;
       if(dest_set.find(up_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, up_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection( left_up_node1, right_down_node1, src_set, grid) ){
          //std::cout<<"expand node checkout point11.3"<<std::endl;
          candidate_node.push_back(up_node[i]);
         }else if(dest_set.find(up_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, up_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection( left_up_node1, right_down_node1, src_set, grid) and  Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
          candidate_node.push_back(up_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point12"<<std::endl;
    
    if(down_found){
       for(int i=0;i<(int)down_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       left_up_node.clear();
       right_down_node.clear();
       //std::cout<<"expand node checkout point12.1"<<std::endl;
       if(dest_set.find(down_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, down_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection(left_up_node1, right_down_node1, src_set, grid) ){
          //std::cout<<"expand node checkout point12.3"<<std::endl;
          candidate_node.push_back(down_node[i]);
         }else if(dest_set.find(down_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, down_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection(left_up_node1, right_down_node1, src_set, grid) and Check_S_Connection_L(left_up_node1, right_down_node1, dest_set, grid) ){
          candidate_node.push_back(down_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point13"<<std::endl;
    if((int)candidate_node.size()>0){
       //std::cout<<"candidate node Found"<<std::endl;
       return true;
      }else{
       //std::cout<<"candidate node not Found"<<std::endl;
       return false;
      }
};

bool A_star::found_near_node(int left_up, int right_down, int current_node, Grid &grid, std::vector<int> &candidate_node, std::set<int> dest_set){

    std::vector<int> left_up_node;
    std::vector<int> right_down_node;
    int parallel_parameter = Check_Parallel_Rule(left_up, right_down, current_node, left_up_node, right_down_node, grid);
    
    std::vector<int> north_node, south_node, east_node, west_node, up_node, down_node;
    bool north_found, south_found, east_found, west_found, up_found, down_found;

    //std::cout<<"expand node checkout point1"<<std::endl;
    north_found = expand_node(grid.vertices_total[current_node].north, north_node, grid);
    //std::cout<<"expand node checkout point2"<<std::endl;
    south_found = expand_node(grid.vertices_total[current_node].south, south_node, grid);
    //std::cout<<"expand node checkout point3"<<std::endl;
    east_found = expand_node(grid.vertices_total[current_node].east, east_node, grid);
    //std::cout<<"expand node checkout point4"<<std::endl;
    west_found = expand_node(grid.vertices_total[current_node].west, west_node, grid);
    //std::cout<<"expand node checkout point5"<<std::endl;
    if(grid.vertices_total[current_node].via_active_up){
       up_found = expand_node_ud(grid.vertices_total[current_node].up, up_node, grid);
    }else{
       up_found = false;
    }
    //std::cout<<"expand node checkout point6"<<std::endl;
    if(grid.vertices_total[current_node].via_active_down){
      down_found = expand_node_ud(grid.vertices_total[current_node].down, down_node, grid);
    }else{
      down_found = false;
    }
    //std::cout<<"expand node checkout point7"<<std::endl;


    if(parallel_parameter){
    if(north_found){
       for(int i=0;i<(int)north_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(north_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, north_node[i], left_up_node1, right_down_node1, grid)){
         //std::cout<<"expand node checkout point7.1"<<std::endl;
         candidate_node.push_back(north_node[i]);
       }else if(dest_set.find(north_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, north_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(north_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point8"<<std::endl;
    if(south_found){
       for(int i=0;i<(int)south_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(south_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, south_node[i], left_up_node1, right_down_node1, grid)){
         //std::cout<<"expand node checkout point8.1"<<std::endl;
         candidate_node.push_back(south_node[i]);
         }else if(dest_set.find(south_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, south_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(south_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point9"<<std::endl;
    if(west_found){
       for(int i=0;i<(int)west_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(west_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, west_node[i], left_up_node1, right_down_node1, grid)){
         //std::cout<<"expand node checkout point9.1"<<std::endl;
         candidate_node.push_back(west_node[i]);
         }else if(dest_set.find(west_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, west_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(west_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point10"<<std::endl;
    if(east_found){
       for(int i=0;i<(int)east_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       if(dest_set.find(east_node[i])==dest_set.end() and Check_Parallel_Rule(left_up, right_down, east_node[i], left_up_node1, right_down_node1, grid)){
         //std::cout<<"expand node checkout point10.1"<<std::endl;
         candidate_node.push_back(east_node[i]);
         }else if(dest_set.find(east_node[i])!=dest_set.end() and Check_Parallel_Rule(left_up, right_down, east_node[i], left_up_node1, right_down_node1, grid) and Check_S_Connection_L( left_up_node1, right_down_node1, dest_set, grid) ){
         candidate_node.push_back(east_node[i]);
       }
       }
      }
      }
    //std::cout<<"expand node checkout point11"<<std::endl;
    if(up_found){
       for(int i=0;i<(int)up_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       //std::cout<<"expand node checkout point11.1"<<std::endl;
       if(dest_set.find(up_node[i])==dest_set.end() and parallel_parameter and Check_Parallel_Rule(left_up, right_down, up_node[i], left_up_node1, right_down_node1, grid)){
          //std::cout<<"expand node checkout point11.2"<<std::endl;
          if(Check_Connection_Rule(left_up_node, right_down_node, left_up_node1, right_down_node1, grid)){
              //std::cout<<"expand node checkout point11.3"<<std::endl;
              candidate_node.push_back(up_node[i]);
            }
         }else if(dest_set.find(up_node[i])!=dest_set.end() and parallel_parameter and Check_S_Connection( left_up_node, right_down_node, dest_set, grid) ){
         candidate_node.push_back(up_node[i]);
       }
       }
      }

    //std::cout<<"expand node checkout point12"<<std::endl;
    if(down_found){
       for(int i=0;i<(int)down_node.size();i++){
       std::vector<int> left_up_node1;
       std::vector<int> right_down_node1;
       //std::cout<<"expand node checkout point12.1"<<std::endl;
       if(dest_set.find(down_node[i])==dest_set.end() and parallel_parameter and Check_Parallel_Rule(left_up, right_down, down_node[i], left_up_node1, right_down_node1, grid)){
          //std::cout<<"expand node checkout point12.2"<<std::endl;
          if(Check_Connection_Rule(left_up_node, right_down_node, left_up_node1, right_down_node1, grid)){
              //std::cout<<"expand node checkout point12.3"<<std::endl;
              candidate_node.push_back(down_node[i]);
            }
         }else if(dest_set.find(down_node[i])!=dest_set.end() and parallel_parameter and  Check_S_Connection( left_up_node, right_down_node, dest_set, grid) ){
         candidate_node.push_back(down_node[i]);
       }
       }
      }
    //std::cout<<"expand node checkout point13"<<std::endl;
    if((int)candidate_node.size()>0){
       //std::cout<<"candidate node Found"<<std::endl;
       return true;
      }else{
       //std::cout<<"candidate node not Found"<<std::endl;
       return false;
      }
};

// one direction xuanzhuande 
bool A_star::Check_Parallel_SD(int left_up, int right_down, int node_index, std::vector<int> &left_up_node, std::vector<int> &right_down_node, Grid& gird, std::set<int> S_or_D){

  if(gird.vertices_total[node_index].active==0){return 0;}

  if(drc_info.Metal_info[gird.vertices_total[node_index].metal].direct==0){//vertical
 
       int current_node = node_index;

       while(left_up>0){
              
              if((int)gird.vertices_total_full_connected[current_node].west.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].west[0]].active==0){
                 return 0;
                }else if(S_or_D.find(gird.vertices_total_full_connected[current_node].west[0])==S_or_D.end()){
                 return 0;
                }else{
                 current_node = gird.vertices_total_full_connected[current_node].west[0];
                 left_up_node.push_back(current_node);
                 left_up=left_up-1;
                }

            }

        current_node = node_index;
      
       while(right_down>0){
              
              if((int)gird.vertices_total_full_connected[current_node].east.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].east[0]].active==0){
                 return 0;
                }else if(S_or_D.find(gird.vertices_total_full_connected[current_node].east[0])==S_or_D.end()){
                 return 0;
                }else{
                 current_node = gird.vertices_total_full_connected[current_node].east[0];
                 right_down_node.push_back(current_node);
                 right_down=right_down-1;
                }

            }        


     }else{

       int current_node = node_index;

       while(left_up>0){
              
              if((int)gird.vertices_total_full_connected[current_node].north.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].north[0]].active==0){
                 return 0;
                }else if(S_or_D.find(gird.vertices_total_full_connected[current_node].north[0])==S_or_D.end()){
                 return 0;
                }else{
                 current_node = gird.vertices_total_full_connected[current_node].north[0];
                 left_up_node.push_back(current_node);
                 left_up=left_up-1;
                }

            }

        current_node = node_index;
      
       while(right_down>0){
              
              if((int)gird.vertices_total_full_connected[current_node].south.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].south[0]].active==0){
                 return 0;
                }else if(S_or_D.find(gird.vertices_total_full_connected[current_node].south[0])==S_or_D.end()){
                 return 0;
                }else{
                 current_node = gird.vertices_total_full_connected[current_node].south[0];
                 right_down_node.push_back(current_node);
                 right_down=right_down-1;
                }

            }        

     }

  return 1;

};

bool A_star::Check_Parallel_Rule(int left_up, int right_down, int node_index, std::vector<int> &left_up_node, std::vector<int> &right_down_node, Grid& gird){


  if(gird.vertices_total[node_index].active==0){return 0;}

  if(drc_info.Metal_info[gird.vertices_total[node_index].metal].direct==0){//vertical
 
       int current_node = node_index;

       while(left_up>0){
              
              if((int)gird.vertices_total_full_connected[current_node].west.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].west[0]].active==0){
                 return 0;
                }else {
                 current_node = gird.vertices_total_full_connected[current_node].west[0];
                 left_up_node.push_back(current_node);
                 left_up=left_up-1;
                }

            }

        current_node = node_index;
      
       while(right_down>0){
              
              if((int)gird.vertices_total_full_connected[current_node].east.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].east[0]].active==0){
                 return 0;
                }else {
                 current_node = gird.vertices_total_full_connected[current_node].east[0];
                 right_down_node.push_back(current_node);
                 right_down=right_down-1;
                }

            }        


     }else{

       int current_node = node_index;

       while(left_up>0){
              
              if((int)gird.vertices_total_full_connected[current_node].north.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].north[0]].active==0){
                 return 0;
                }else {
                 current_node = gird.vertices_total_full_connected[current_node].north[0];
                 left_up_node.push_back(current_node);
                 left_up=left_up-1;
                }

            }

        current_node = node_index;
      
       while(right_down>0){
              
              if((int)gird.vertices_total_full_connected[current_node].south.size()==0){
                 return 0;
                }else if(gird.vertices_total[gird.vertices_total_full_connected[current_node].south[0]].active==0){
                 return 0;
                }else {
                 current_node = gird.vertices_total_full_connected[current_node].south[0];
                 right_down_node.push_back(current_node);
                 right_down=right_down-1;
                }

            }        

     }

  return 1;
 
};

void A_star::Search_direction(int nodeS, int nodeD, Grid& grid, int &v_search, int &h_search){

     if(grid.vertices_total[nodeS].active==0 or grid.vertices_total[nodeD].active==0){
        v_search = -1;
        h_search = -1;
        return;
       }
      
     if(grid.vertices_total[nodeS].y==grid.vertices_total[nodeD].y){
         v_search = 0;
       }else if(grid.vertices_total[nodeS].y<grid.vertices_total[nodeD].y){
         v_search = 1;
       }else if(grid.vertices_total[nodeS].y>grid.vertices_total[nodeD].y){
         v_search = 2;
       }

     if(grid.vertices_total[nodeS].x==grid.vertices_total[nodeD].x){
         h_search = 0;
       }else if(grid.vertices_total[nodeS].x<grid.vertices_total[nodeD].x){
         h_search = 1;
       }else if(grid.vertices_total[nodeS].x>grid.vertices_total[nodeD].x){
         h_search = 2;
       }

};

bool A_star::L_shape_Connection(int nodeS, int nodeD, Grid& grid){

  std::cout<<"L shape checkpoint 1"<<std::endl;
  std::cout<<"vertice total size "<<grid.vertices_total.size()<<std::endl;
  std::cout<<"nodeS "<<nodeS<<std::endl;
  std::cout<<"nodeD "<<nodeD<<std::endl;
  if(nodeS >(int) grid.vertices_total.size() or nodeD >(int) grid.vertices_total.size() or nodeS <0 or nodeD <0 ){return 0;}
  int metal_index = grid.vertices_total[nodeS].metal;
  int metal_index_next = grid.vertices_total[nodeD].metal;
  int v_search=-1;//0 stay, 1 up, 2 down
  int h_search=-1;//0 stay, 1 left, 2 right
  int v_lock = 0;
  int h_lock = 0;
  
  if(drc_info.Metal_info[metal_index].direct==0){//vertical

     int current_node = nodeS;
     std::cout<<"L shape checkpoint 2"<<std::endl;
     Search_direction(nodeS, nodeD, grid, v_search, h_search);
     std::cout<<"L shape checkpoint 3"<<std::endl;
     int v_search_temp = v_search; 
     int h_search_temp = h_search;
     if(v_search_temp==-1 or h_search_temp==-1){return 0;}
     while(h_search_temp==0 and v_search_temp==0){

            std::cout<<"L shape checkpoint 5"<<std::endl;
            Search_direction(current_node, nodeD, grid, v_search_temp, h_search_temp);
            std::cout<<"L shape checkpoint 6"<<std::endl;

            if(v_search_temp==-1 or h_search_temp==-1){return 0;}

            if(v_lock==0){

               if(v_search ==0 or v_search_temp ==0){

                  if(metal_index_next>metal_index){
                      current_node = grid.vertices_total[current_node].up;
                      v_lock = 1;
                      if(current_node==-1){return 0;}
                     }else{
                      current_node = grid.vertices_total[current_node].down;
                      v_lock = 1;
                      if(current_node==-1){return 0;}
                     }

                 }else if(v_search_temp == v_search){
                   
                    if(v_search_temp==1){

                       int current_x = grid.vertices_total[current_node].x;
                       current_node = current_node + 1;
                       if(current_node>(int)grid.vertices_total.size()){return 0;}
                       int next_x = grid.vertices_total[current_node].x;
                       if(current_x!=next_x){return 0;}

                      }else{

                       int current_x = grid.vertices_total[current_node].x;
                       current_node = current_node -1;
                       if(current_node<0){return 0;}
                       int next_x = grid.vertices_total[current_node].x;
                       if(current_x!=next_x){return 0;}

                      }

                 }else{
 
                       return 0;
               
                 }

              }

            if(v_lock and h_lock==0){

               if(h_search ==0 or h_search_temp ==0){

                  h_lock =1;

                 }else if(h_search_temp == h_search){
                   
                    if(h_search_temp==1){

                       int current_y = grid.vertices_total[current_node].y;
                       current_node = current_node + 1;
                       if(current_node>(int)grid.vertices_total.size()){return 0;}
                       int next_y = grid.vertices_total[current_node].y;
                       if(current_y!=next_y){return 0;}

                      }else{

                       int current_y = grid.vertices_total[current_node].y;
                       current_node = current_node -1;
                       if(current_node<0){return 0;}
                       int next_y = grid.vertices_total[current_node].y;
                       if(current_y!=next_y){return 0;}

                      }

                 }else{
 
                       return 0;
               
                 }
              }
          }

    }else{

     int current_node = nodeS;
     std::cout<<"L shape checkpoint 3"<<std::endl;
     Search_direction(nodeS, nodeD, grid, v_search, h_search);
     std::cout<<"L shape checkpoint 4"<<std::endl;
     int v_search_temp = v_search; 
     int h_search_temp = h_search;
     if(v_search_temp==-1 or h_search_temp==-1){return 0;}
     while(h_search_temp==0 and v_search_temp==0){

            std::cout<<"L shape checkpoint 7"<<std::endl;
            Search_direction(current_node, nodeD, grid, v_search_temp, h_search_temp);
            std::cout<<"L shape checkpoint 8"<<std::endl;

            if(v_search_temp==-1 or h_search_temp==-1){return 0;}

            if(h_lock==0){
//
               if(h_search ==0 or h_search_temp ==0){

                  if(metal_index_next>metal_index){
                      current_node = grid.vertices_total[current_node].up;
                      h_lock = 1;
                      if(current_node==-1){return 0;}
                     }else{
                      current_node = grid.vertices_total[current_node].down;
                      h_lock = 1;
                      if(current_node==-1){return 0;}
                     }

                 }else if(h_search_temp == h_search){
                   
                    if(h_search_temp==1){

                       int current_y = grid.vertices_total[current_node].y;
                       current_node = current_node + 1;
                       if(current_node>(int)grid.vertices_total.size()){return 0;}
                       int next_y = grid.vertices_total[current_node].y;
                       if(current_y!=next_y){return 0;}

                      }else{

                       int current_y = grid.vertices_total[current_node].y;
                       current_node = current_node -1;
                       if(current_node<0){return 0;}
                       int next_y = grid.vertices_total[current_node].y;
                       if(current_y!=next_y){return 0;}

                      }

                 }else{
 
                       return 0;
               
                 }
//
              }

            if(h_lock and v_lock==0){

               if(v_search ==0 or v_search_temp ==0){

                  v_lock =1;

                 }else if(v_search_temp == v_search){
                   
                    if(v_search_temp==1){

                       int current_x = grid.vertices_total[current_node].x;
                       current_node = current_node + 1;
                       if(current_node>(int)grid.vertices_total.size()){return 0;}
                       int next_x = grid.vertices_total[current_node].x;
                       if(current_x!=next_x){return 0;}

                      }else{

                       int current_x = grid.vertices_total[current_node].x;
                       current_node = current_node -1;
                       if(current_node<0){return 0;}
                       int next_x = grid.vertices_total[current_node].x;
                       if(current_x!=next_x){return 0;}

                      }

                 }else{
 
                       return 0;
               
                 }

              }
          }

    }

  return 1;


};

//you xuan connection rule
bool A_star::Check_Connection_Rule(std::vector<int> &left_up1, std::vector<int> &right_up1, std::vector<int> &left_up2, std::vector<int> &right_up2, Grid& grid){

   for(int i=0;i<(int)left_up1.size();i++){

       if(!L_shape_Connection(left_up1[i],left_up2[i],grid)){return 0;}

      }

   for(int i=0;i<(int)right_up1.size();i++){

       if(!L_shape_Connection(right_up1[i],right_up2[i],grid)){return 0;}

      }

   return 1;

};

int A_star::trace_back(int current_node, Grid& grid){

  int first_node_same_layer = current_node; //maybe src...

  bool trace_back_flag = true;

  int dummy_node = current_node;

  while(trace_back_flag){

    int last_node = grid.vertices_total[dummy_node].parent;

    if(last_node<0 or last_node>=grid.vertices_total.size()){
      trace_back_flag = false;
    }else if(grid.vertices_total[last_node].metal == grid.vertices_total[dummy_node].metal){
      first_node_same_layer = last_node;
      dummy_node = last_node;
    }else{
      trace_back_flag = false;
    }

  }

  return first_node_same_layer;


};

void A_star::CheckExtendable(std::vector<int> &candidate_node, int current_node, Grid& grid){
  
  std::cout<<"start CheckExtendable"<<std::endl;
  std::vector<int> feasible_node;

  for(unsigned int i=0;i<candidate_node.size();i++){

     int next_node = candidate_node[i];
     if(grid.vertices_total[current_node].metal==grid.vertices_total[next_node].metal){
       feasible_node.push_back(next_node);
     }else{
       std::cout<<"start trace_back"<<std::endl;
       int first_node_same_layer = trace_back(current_node,grid);
       std::cout<<"end trace_back"<<std::endl;
       int metal = grid.vertices_total[current_node].metal;
       int length = abs(grid.vertices_total[current_node].x - grid.vertices_total[first_node_same_layer].x) + abs(grid.vertices_total[current_node].y - grid.vertices_total[first_node_same_layer].y);
       int minL = drc_info.Metal_info[metal].minL;
       int delta_length = length - minL;

       int current_node_length = 0;
       int next_node_length = 0;
       int current_node_expand = 0;
       int next_node_expand = 0;

       if(grid.vertices_total[current_node].metal<grid.vertices_total[next_node].metal){

         int via_index = grid.vertices_total[current_node].metal;
         int metal_direct = drc_info.Metal_info[via_index].direct;
         std::vector<PnRDB::point> temp_points_lower = drc_info.Via_model[via_index].LowerRect;
         std::vector<PnRDB::point> temp_points_upper = drc_info.Via_model[via_index].UpperRect;
         current_node_expand = drc_info.Metal_info[via_index].dist_ee;
         next_node_expand = drc_info.Metal_info[via_index+1].dist_ee;
         if(metal_direct==1){//H
           current_node_length = temp_points_lower[1].x - temp_points_lower[0].x;
           next_node_length = temp_points_upper[1].y - temp_points_upper[0].y;
         }else{
           current_node_length = temp_points_lower[1].y - temp_points_lower[0].y;
           next_node_length = temp_points_upper[1].x - temp_points_upper[0].x;
         }

       }else{

         int via_index = grid.vertices_total[next_node].metal;
         int metal_direct = drc_info.Metal_info[via_index].direct;
         std::vector<PnRDB::point> temp_points_lower = drc_info.Via_model[via_index].LowerRect;
         std::vector<PnRDB::point> temp_points_upper = drc_info.Via_model[via_index].UpperRect;
         current_node_expand = drc_info.Metal_info[via_index+1].dist_ee;
         next_node_expand = drc_info.Metal_info[via_index].dist_ee;
         
         if(metal_direct==1){//H
           current_node_length = temp_points_upper[1].y - temp_points_upper[0].y;
           next_node_length = temp_points_lower[1].x - temp_points_lower[0].x;
         }else{
           current_node_length = temp_points_upper[1].x - temp_points_upper[0].x;
           next_node_length = temp_points_lower[1].y - temp_points_lower[0].y;
         }

       }

       current_node_length = 2*current_node_expand + current_node_length;
       next_node_length = 2*next_node_expand + next_node_length;
       std::cout<<"check via current_node_length "<<current_node_length<<std::endl;
       std::cout<<"check via next_length "<<next_node_length<<std::endl;
       if(delta_length<0){
           //std::cout<<"start CheckExendable_With_Certain_Length"<<std::endl;
           bool feasible = CheckExendable_With_Certain_Length(first_node_same_layer,current_node,length,minL,grid);
           if(feasible==0){
             std::cout<<"Length infeasible"<<std::endl;
           }
           Check_via_AV(current_node,current_node,0,current_node_length,grid,feasible);
           Check_via_AV(next_node,next_node,0,next_node_length,grid,feasible);
           //std::cout<<"End CheckExendable_With_Certain_Length"<<std::endl;
           if(feasible){
               feasible_node.push_back(next_node);
             }else{
               std::cout<<"Up/down infeasible case 1"<<std::endl;
             }           

         }else{
            bool feasible = 1;
            Check_via_AV(current_node,current_node,0,current_node_length,grid,feasible);
            Check_via_AV(next_node,next_node,0,next_node_length,grid,feasible);
            if(feasible){
              feasible_node.push_back(next_node);
             }else{
              std::cout<<"Up/down infeasible case 2"<<std::endl;
             }
         }
     }
  }

  candidate_node = feasible_node;

  std::cout<<"End CheckExtendable"<<std::endl;

};

bool A_star::CheckExendable_With_Certain_Length(int first_node_same_layer,int current_node,int length,int minL,Grid &grid){

  int half_minL = ceil( ( (double) minL -  (double) length) / 2 );

  bool feasible = true;
  
  int first_direction = 0;

  int current_direction = 0;
 
  if(first_node_same_layer<=current_node){

     first_direction = -1;
     current_direction = 1;

  }else{

     first_direction = 1;
     current_direction = -1;

  }

  bool search_flag = true;
  int culmulated_length = 0;
  int dummy_node = first_node_same_layer;
  while(search_flag){
     if(culmulated_length>=half_minL){
        search_flag = false;
     }else{
       int next_node = dummy_node + first_direction;
       if(next_node<0 or next_node>=grid.vertices_total.size() ) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[first_node_same_layer].x and grid.vertices_total[next_node].y != grid.vertices_total[first_node_same_layer].y) or grid.vertices_total[next_node].metal != grid.vertices_total[first_node_same_layer].metal ){
          search_flag = false;
          feasible = false;
       }else {
          culmulated_length = abs(grid.vertices_total[next_node].x-grid.vertices_total[first_node_same_layer].x) + abs( grid.vertices_total[next_node].y-grid.vertices_total[first_node_same_layer].y);
          dummy_node = next_node;
       }
     }
  }

  culmulated_length = 0;
  search_flag = true;
  dummy_node = current_node;
  while(search_flag){
     if(culmulated_length>=half_minL){
        search_flag = false;
     }else{
       int next_node = dummy_node + current_direction;
       if(next_node<0 or next_node>=grid.vertices_total.size() ) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[current_node].x and grid.vertices_total[next_node].y != grid.vertices_total[current_node].y) or grid.vertices_total[next_node].metal != grid.vertices_total[current_node].metal){
          search_flag = false;
          feasible = false;
       }else {
          culmulated_length = abs(grid.vertices_total[next_node].x-grid.vertices_total[current_node].x) + abs( grid.vertices_total[next_node].y-grid.vertices_total[current_node].y);
          dummy_node = next_node;
       }
     }
  }

  return feasible;

};

bool A_star::Check_via_AV(int first_node_same_layer,int current_node,int length,int minL,Grid &grid, bool &feasible){

  if(feasible==0){return feasible;}

  int half_minL = ceil( ( (double) minL -  (double) length) / 2 );
  
  int first_direction = 0;

  int current_direction = 0;
 
  if(first_node_same_layer<=current_node){

     first_direction = -1;
     current_direction = 1;

  }else{

     first_direction = 1;
     current_direction = -1;

  }

  bool search_flag = true;
  int culmulated_length = 0;
  int dummy_node = first_node_same_layer;
  while(search_flag){
     if(culmulated_length>=half_minL){
        search_flag = false;
     }else{
       int next_node = dummy_node + first_direction;
       if(next_node<0 or next_node>=grid.vertices_total.size() ) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[first_node_same_layer].x and grid.vertices_total[next_node].y != grid.vertices_total[first_node_same_layer].y) or grid.vertices_total[next_node].metal != grid.vertices_total[first_node_same_layer].metal ){
          search_flag = false;
          feasible = false;
       }else {
          culmulated_length = abs(grid.vertices_total[next_node].x-grid.vertices_total[first_node_same_layer].x) + abs( grid.vertices_total[next_node].y-grid.vertices_total[first_node_same_layer].y);
          dummy_node = next_node;
       }
     }
  }

  culmulated_length = 0;
  search_flag = true;
  dummy_node = current_node;
  while(search_flag){
     if(culmulated_length>=half_minL){
        search_flag = false;
     }else{
       int next_node = dummy_node + current_direction;
       if(next_node<0 or next_node>=grid.vertices_total.size() ) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[current_node].x and grid.vertices_total[next_node].y != grid.vertices_total[current_node].y) or grid.vertices_total[next_node].metal != grid.vertices_total[current_node].metal){
          search_flag = false;
          feasible = false;
       }else {
          culmulated_length = abs(grid.vertices_total[next_node].x-grid.vertices_total[current_node].x) + abs( grid.vertices_total[next_node].y-grid.vertices_total[current_node].y);
          dummy_node = next_node;
       }
     }
  }

  return feasible;

};

std::vector<int> A_star::A_star_algorithm(Grid& grid, int left_up, int right_down){

  // how to back trace?

  int via_expand_effort = 100;

  //std::cout<<"A start checkout point1"<<std::endl;

  std::set<std::pair<int,int>, RouterDB::pairComp> L_list;
  std::pair<int,int> temp_pair; //temp_pair.first is the cost, temp_pair.second is the index of graph

  std::set<int> src_index;
  for(int i=0;i<(int)source.size();i++){
    
      src_index.insert(source[i]);

     }
  
  std::set<int> dest_index;
  for(int i=0;i<(int)dest.size();i++){
    
      dest_index.insert(dest[i]);

     }

  //initial source  Q1//jugde whether source works
  //initial_source(grid, L_list);
  initial_source(grid, L_list, src_index, left_up, right_down);

  bool found = 0;
  int current_node = -1;

  //std::cout<<"A start checkout point2"<<std::endl;
  
  while(!L_list.empty() and !found){
    //std::cout<<"L_list size"<<L_list.size()<<std::endl;
    std::set<std::pair<int,int>, RouterDB::pairComp>::iterator it;
    it = L_list.begin();
    current_node = it->second;
    L_list.erase(it);
    
    //judge whether dest found Q2// judge whether dest works
    if(dest_index.find(current_node)!=dest_index.end()){
       found=1;
       continue;
      }

    //found the candidates nodes
    std::vector<int> candidate_node;
    //std::cout<<"A start checkout point3"<<std::endl;
    //std::cout<<"check point near node 1"<<std::endl;
    bool near_node_exist;
    if(src_index.find(current_node)==src_index.end()){
        near_node_exist =found_near_node(left_up, right_down, current_node, grid, candidate_node, dest_index);
       }else{
        near_node_exist =found_near_node_S(left_up, right_down, current_node, grid, candidate_node, src_index, dest_index);
       }
    //std::cout<<"check point near node 2"<<std::endl;
    if(!near_node_exist){
       continue;
      }else{
      //       std::cout<<"near_node_exist"<<std::endl;
      }
    //std::cout<<"A start checkout point3.1"<<std::endl;
  //for sheilding and multi-connection
    CheckExtendable(candidate_node, current_node, grid); //new code
    //for each node judge whether can be expand or not; Q3 expandable?
    //bool expandable = 0;
    //std::vector<int> expand_candidate_node;
    for(int i=0;i<(int)candidate_node.size();i++){
       //judge whether this node can be expanded or not
       // not all node can be expanded?
       // if()?
       //std::cout<<"A start checkout point3.2"<<std::endl;
       int M_dis = Manhattan_distan(candidate_node[i], grid);
       //std::cout<<"A start checkout point3.3"<<std::endl;
       grid.vertices_total[candidate_node[i]].Cost = grid.vertices_total[current_node].Cost + abs(grid.vertices_total[current_node].x - grid.vertices_total[candidate_node[i]].x) + abs(grid.vertices_total[current_node].y - grid.vertices_total[candidate_node[i]].y) + via_expand_effort*abs(grid.vertices_total[candidate_node[i]].metal-grid.vertices_total[current_node].metal);
       int dis = grid.vertices_total[candidate_node[i]].Cost + M_dis;
       grid.vertices_total[candidate_node[i]].parent = current_node;
       temp_pair.first = dis;
       temp_pair.second = candidate_node[i];
       L_list.insert(temp_pair);
       }

  }
  //std::cout<<"A start checkout point4"<<std::endl;
  std::vector<int> temp_path; //Q4 return sheilding and parallel path?  sheild and parallel should be recovered in outer loop???
  if(found==0){
     std::cout<<"A_star fails to find a feasible path"<<std::endl;
    }else{
     //trace back and find a path
     temp_path.push_back(current_node);
     int temp_parent = grid.vertices_total[current_node].parent;
     while(temp_parent!=-1){
           temp_path.push_back(temp_parent);
           temp_parent = grid.vertices_total[temp_parent].parent;
          }
    }
   //std::cout<<"A start checkout point5"<<std::endl;
   refreshGrid(grid);

   std::vector<int> reserse_path;
   for(int i=(int)temp_path.size()-1;i>=0;i--){

       reserse_path.push_back(temp_path[i]);

      }
   return reserse_path;
    
};

void A_star::YX_search(int start_point, int end_point, std::vector<int>& left_path, bool down_up, Grid &grid){

  std::cout<<"start YX_search"<<std::endl;

  std::cout<<"Metal Index Start Point "<<grid.vertices_total[start_point].metal <<"Start Point "<<grid.vertices_total[start_point].x<<" "<<grid.vertices_total[start_point].y <<std::endl;
  std::cout<<"Metal Index End Point "<<grid.vertices_total[end_point].metal <<"End Point "<<grid.vertices_total[end_point].x<<" "<<grid.vertices_total[end_point].y <<std::endl;
  std::cout<<"down_up "<<down_up<<std::endl;

//YX search here means |-

  //down_up, 1 up, 0 down
  int direction_y = -1;
  int direction_x = -1;
  int down_up_lock = 0;

  while(direction_y!=0 and direction_x!=0){

      //std::cout<<"direction_y "<<direction_y<<"direction_x "<<direction_x<<std::endl;

       if(direction_y!=0){
          if(grid.vertices_total[start_point].y<grid.vertices_total[end_point].y){
               direction_y = 1;
          }else if(grid.vertices_total[start_point].y>grid.vertices_total[end_point].y){
               direction_y = -1;
          }else{
               direction_y = 0;
          }
          start_point = start_point + direction_y;
          left_path.push_back(start_point);
          //std::cout<<"insert temp_int metal "<<grid.vertices_total[start_point].metal<<std::endl;
         }

       if(direction_y==0 and direction_x!=0 ){

           if(down_up_lock==0){
                if(down_up==0){
                start_point = grid.vertices_total[start_point].down;
                }else{
                start_point = grid.vertices_total[start_point].up;
                }
                down_up_lock=1;
                if(start_point==-1){
                     std::cout<<"copy path error 1"<<std::endl;
                   }else{
                     left_path.push_back(start_point);
                     //std::cout<<"insert temp_int metal "<<grid.vertices_total[start_point].metal<<std::endl;
                   }
              }
                       
            if(grid.vertices_total[start_point].x<grid.vertices_total[end_point].x){
                 direction_x = 1;
               }else if(grid.vertices_total[start_point].x>grid.vertices_total[end_point].x){
                 direction_x = -1;
               }else{
                 direction_x = 0;
               }
             start_point = start_point + direction_x;
             left_path.push_back(start_point);
             //std::cout<<"insert temp_int metal "<<grid.vertices_total[start_point].metal<<std::endl;
            }
         }

  std::cout<<"start YX_search"<<std::endl;

};

void A_star::XY_search(int start_point, int end_point, std::vector<int>& left_path, bool down_up, Grid &grid){

  std::cout<<"start XY_search"<<std::endl;

//XY search here means -|

  //down_up, 1 up, 0 down
  int direction_y = -1;
  int direction_x = -1;
  int down_up_lock = 0;

  std::cout<<"Metal Index Start Point "<<grid.vertices_total[start_point].metal <<"Start Point "<<grid.vertices_total[start_point].x<<" "<<grid.vertices_total[start_point].y <<std::endl;
  std::cout<<"Metal Index End Point "<<grid.vertices_total[end_point].metal <<"End Point "<<grid.vertices_total[end_point].x<<" "<<grid.vertices_total[end_point].y <<std::endl;
  std::cout<<"down_up "<<down_up<<std::endl;

  while(direction_y!=0 and direction_x!=0){

       //std::cout<<"direction_x "<<direction_x<<"direction_y "<<direction_y<<std::endl;

       if(direction_x!=0){
          if(grid.vertices_total[start_point].x<grid.vertices_total[end_point].x){
               direction_x = 1;
          }else if(grid.vertices_total[start_point].x>grid.vertices_total[end_point].x){
               direction_x = -1;
          }else{
               direction_x = 0;
          }
          start_point = start_point + direction_x;
          left_path.push_back(start_point);
          //std::cout<<"insert temp_int metal "<<grid.vertices_total[start_point].metal<<std::endl;
         }

       if(direction_x==0 and direction_y!=0 ){

           if(down_up_lock==0){
                if(down_up==0){
                start_point = grid.vertices_total[start_point].down;
                }else{
                start_point = grid.vertices_total[start_point].up;
                }
                down_up_lock=1;
                if(start_point==-1){
                     std::cout<<"copy path error 1"<<std::endl;
                   }else{
                     left_path.push_back(start_point);
                     //std::cout<<"insert temp_int metal "<<grid.vertices_total[start_point].metal<<std::endl;
                   }
              }
                       
            if(grid.vertices_total[start_point].y<grid.vertices_total[end_point].y){
                 direction_y = 1;
               }else if(grid.vertices_total[start_point].y>grid.vertices_total[end_point].y){
                 direction_y = -1;
               }else{
                 direction_y = 0;
               }
             start_point = start_point + direction_y;
             left_path.push_back(start_point);
             //std::cout<<"insert temp_int metal "<<grid.vertices_total[start_point].metal<<std::endl;
            }
         }


  std::cout<<"end XY_search"<<std::endl;

};


void A_star::Down_up_path(int end_index, Grid& grid, int down_up, std::vector<int>& path){

  //down_up down 0, up 1
  if(down_up){

      int temp_int = grid.vertices_total[end_index].up;
      if(temp_int==-1){
         std::cout<<"up node error"<<std::endl;
        }else{
         path.push_back(temp_int);
        }

    }else{

      int temp_int = grid.vertices_total[end_index].down;
      if(temp_int==-1){
         std::cout<<"up node error"<<std::endl;
        }else{
         path.push_back(temp_int);
        }

    }
  
};


void A_star::left_path_SD(int end_index, int number, Grid& grid, std::vector<int>& path){

  if(drc_info.Metal_info[grid.vertices_total[end_index].metal].direct==0){//v

      int current_int = end_index;
      int index = number;
      int up =1;
      int down =1;
      std::vector<int> up_path;
      std::vector<int> down_path;
      up_path.push_back(current_int);
      down_path.push_back(current_int);

      while(index>0){
         current_int = current_int -1;
         if(current_int<0 or grid.vertices_total[current_int].active==0){up=0;down=0;}
         up_path.push_back(current_int);
         down_path.push_back(current_int);
         index = index -1;
      }

      int future_int = grid.vertices_total[current_int].up;
      if(future_int==-1){
          up = 0;
        }else{
          up_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int + 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                up=0;
                //break_flag = 1;
                continue;
               }else{
                up_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(up==1 and grid.vertices_total[future_int].down!=-1){
                up_path.push_back(grid.vertices_total[future_int].down);
          }else{
             up=0;
          }
        }

      future_int = grid.vertices_total[current_int].down;
      if(future_int==-1){
          down = 0;
        }else{
          down_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int + 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                down=0;
                //break_flag = 1;
                continue;
               }else{
                down_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(down==1 and grid.vertices_total[future_int].up!=-1){
                down_path.push_back(grid.vertices_total[future_int].up);
          }else{
             down=0;
          }
        }

       if(up==0 and down==0){
     
          std::cout<<"Down_up_SD error"<<std::endl;

         }else if(up==1){
   
          for(int i=(int)up_path.size()-1;i>-1;i--){
               path.push_back(up_path[i]);
              }

         }else{

          for(int i=(int)down_path.size()-1;i>-1;i--){
               path.push_back(down_path[i]);
              }
        
         }

    }else{//h
      
      int current_int = end_index;
      int index = number;
      int up =1;
      int down =1;
      std::vector<int> up_path;
      std::vector<int> down_path;
      up_path.push_back(current_int);
      down_path.push_back(current_int);

      while(index>0){
         current_int = current_int -1;
         up_path.push_back(current_int);
         down_path.push_back(current_int);
         index = index -1;
      }

      int future_int = grid.vertices_total[current_int].up;
      if(future_int==-1){
          up = 0;
        }else{
          up_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int - 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                up=0;
                //break_flag = 1;
                continue;
               }else{
                up_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(up==1 and grid.vertices_total[future_int].down!=-1){
                up_path.push_back(grid.vertices_total[future_int].down);
          }else{
             up=0;
          }
        }

      future_int = grid.vertices_total[current_int].down;
      if(future_int==-1){
          down = 0;
        }else{
          down_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int - 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                down=0;
                //break_flag = 1;
                continue;
               }else{
                down_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(down==1 and grid.vertices_total[future_int].up!=-1){
                down_path.push_back(grid.vertices_total[future_int].up);
          }else{
             down=0;
          }
        }

       if(up==0 and down==0){
     
          std::cout<<"Down_up_SD error"<<std::endl;

         }else if(up==1){
   
          for(int i=(int)up_path.size()-1;i>-1;i--){
               path.push_back(up_path[i]);
              }

         }else{

          for(int i=(int)down_path.size()-1;i>-1;i--){
               path.push_back(down_path[i]);
              }
        
         }

    }
  
};

void A_star::right_path_SD(int end_index, int number, Grid& grid, std::vector<int>& path){

  if(drc_info.Metal_info[grid.vertices_total[end_index].metal].direct==0){//v

      int current_int = end_index;
      int index = number;
      int up =1;
      int down =1;
      std::vector<int> up_path;
      std::vector<int> down_path;
      up_path.push_back(current_int);
      down_path.push_back(current_int);

      while(index>0){
         current_int = current_int +1;
         up_path.push_back(current_int);
         down_path.push_back(current_int);
         index = index -1;
      }

      int future_int = grid.vertices_total[current_int].up;
      if(future_int==-1){
          up = 0;
        }else{
          up_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int - 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                up=0;
                //break_flag = 1;
                continue;
               }else{
                up_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(up==1 and grid.vertices_total[future_int].down!=-1){
                up_path.push_back(grid.vertices_total[future_int].down);
          }else{
             up=0;
          }
        }

      future_int = grid.vertices_total[current_int].down;
      if(future_int==-1){
          down = 0;
        }else{
          down_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int - 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                down=0;
                //break_flag = 1;
                continue;
               }else{
                down_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(down==1 and grid.vertices_total[future_int].up!=-1){
                down_path.push_back(grid.vertices_total[future_int].up);
          }else{
             down=0;
          }
        }

       if(up==0 and down==0){
     
          std::cout<<"Down_up_SD error"<<std::endl;

         }else if(up==1){
   
          for(int i=(int)up_path.size()-1;i>-1;i--){
               path.push_back(up_path[i]);
              }

         }else{

          for(int i=(int)down_path.size()-1;i>-1;i--){
               path.push_back(down_path[i]);
              }
        
         }

    }else{//h
      
      int current_int = end_index;
      int index = number;
      int up =1;
      int down =1;
      std::vector<int> up_path;
      std::vector<int> down_path;
      up_path.push_back(current_int);
      down_path.push_back(current_int);

      while(index>0){
         current_int = current_int +1;
         up_path.push_back(current_int);
         down_path.push_back(current_int);
         index = index -1;
      }

      int future_int = grid.vertices_total[current_int].up;
      if(future_int==-1){
          up = 0;
        }else{
          up_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int + 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                up=0;
                //break_flag = 1;
                continue;
               }else{
                up_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(up==1 and grid.vertices_total[future_int].down!=-1){
                up_path.push_back(grid.vertices_total[future_int].down);
          }else{
             up=0;
          }
        }

      future_int = grid.vertices_total[current_int].down;
      if(future_int==-1){
          down = 0;
        }else{
          down_path.push_back(future_int);
          int index = number;
          //int break_flag = 0;
          while(index>0){
             future_int = future_int + 1;
             if(grid.vertices_total[future_int].active==0){
                index=0;
                down=0;
                //break_flag = 1;
                continue;
               }else{
                down_path.push_back(future_int);
                index = index -1;
               }  
          }
          if(down==1 and grid.vertices_total[future_int].up!=-1){
                down_path.push_back(grid.vertices_total[future_int].up);
          }else{
             down=0;
          }
        }

       if(up==0 and down==0){
     
          std::cout<<"Down_up_SD error"<<std::endl;

         }else if(up==1){
   
          for(int i=(int)up_path.size()-1;i>-1;i--){
               path.push_back(up_path[i]);
              }

         }else{

          for(int i=(int)down_path.size()-1;i>-1;i--){
               path.push_back(down_path[i]);
              }
        
         }

    }
  
};


void A_star::Left_path(std::vector<int> &temp_path, Grid& grid, int number, std::vector<int> &left_path){

   int temp_int;

   for(int i=0;i<(int)temp_path.size();i++){

        std::cout<<"Checkpoint1"<<std::endl;

        std::cout<<"current node metal "<<grid.vertices_total[temp_path[i]].metal<<std::endl;
        if(i>0){std::cout<<"last node metal "<<grid.vertices_total[temp_path[i-1]].metal<<std::endl;}

        std::cout<<"metal "<<grid.vertices_total[temp_path[i]].metal<<"direction "<<drc_info.Metal_info[grid.vertices_total[temp_path[i]].metal].direct<<std::endl;

        if(drc_info.Metal_info[grid.vertices_total[temp_path[i]].metal].direct==0){//vertical
 
           std::cout<<"Checkpoint2"<<std::endl;

           int index = number;
           temp_int = temp_path[i];
/*
           while(index>0){
                 temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                 index = index -1;
                }
*/
           std::cout<<"Checkpoint3"<<std::endl;

           if(i==0){

             //source part
             if((int)temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i+1]].metal){

                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint4"<<std::endl;

                     left_path_SD(temp_int, number, grid, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==-1){

                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].north[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint5"<<std::endl;
                     Down_up_path(temp_int, grid, 0, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==1){

                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].north[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint6"<<std::endl;
                     Down_up_path(temp_int, grid, 1, left_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;
                 continue;
               }
             
             }

           if(i==(int)temp_path.size()-1){

             //dest part
             if((int)temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i-1]].metal){

                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint7"<<std::endl;
                     left_path_SD(temp_int, number, grid, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==-1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].north[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint7"<<std::endl;
                     Down_up_path(temp_int, grid, 0, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].north[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint8"<<std::endl;
                     Down_up_path(temp_int, grid, 1, left_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;
                 continue;

               }
             
             }

           std::cout<<"Checkpoint9"<<std::endl;
           int end_size =(int) left_path.size()-1;

           while(index>0){
                 temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                 index = index -1;
                }  
         
           if(grid.vertices_total[temp_int].metal == grid.vertices_total[left_path[end_size]].metal){
             
               left_path.push_back(temp_int);
            
             }else if(grid.vertices_total[temp_int].metal > grid.vertices_total[left_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[left_path[end_size]].metal ==1){ //up
              
               XY_search(left_path[end_size], temp_int, left_path, 1, grid);

             }else if(grid.vertices_total[temp_int].metal < grid.vertices_total[left_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[left_path[end_size]].metal ==-1){//down

               XY_search(left_path[end_size], temp_int, left_path, 0, grid);
               
             }


          }else{

           std::cout<<"Checkpoint2.1"<<std::endl;
           int index = number;
           temp_int = temp_path[i];

           std::cout<<"Checkpoint2.2"<<std::endl;
           if(i==0){

             //source part
             if((int)temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i+1]].metal){

                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].north[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint10"<<std::endl;
                     left_path_SD(temp_int, number, grid, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==-1){

                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint11"<<std::endl;
                     Down_up_path(temp_int, grid, 0, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==1){

                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint12"<<std::endl;
                     Down_up_path(temp_int, grid, 1, left_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;
                 continue;

               }
             
             }

           if(i==(int)temp_path.size()-1){

             //dest part
             if(temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i-1]].metal){

                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].north[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint13"<<std::endl;
                     left_path_SD(temp_int, number, grid, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==-1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint14"<<std::endl;
                     Down_up_path(temp_int, grid, 0, left_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].west[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint15"<<std::endl;
                     Down_up_path(temp_int, grid, 1, left_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;
                 continue;
               }
             
             }

           std::cout<<"Checkpoint16"<<std::endl;
           int end_size =(int) left_path.size()-1;

           while(index>0){
                 std::cout<<"north point size "<<grid.vertices_total_full_connected[temp_int].north.size()<<std::endl;
                 /*
                 if(grid.vertices_total_full_connected[temp_int].north.size()==0){
                   std::cout<<"Bug for north"<<std::endl;
                   return;
                   }
                 */
                 temp_int = grid.vertices_total_full_connected[temp_int].north[0];
                 index = index -1;
                }
           
           if(grid.vertices_total[temp_int].metal == grid.vertices_total[left_path[end_size]].metal){
             
               left_path.push_back(temp_int);
            
             }else if(grid.vertices_total[temp_int].metal > grid.vertices_total[left_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[left_path[end_size]].metal==1){ //up

               YX_search(left_path[end_size], temp_int, left_path, 1, grid);

             }else if(grid.vertices_total[temp_int].metal < grid.vertices_total[left_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[left_path[end_size]].metal==-1){//down

               YX_search(left_path[end_size], temp_int, left_path, 0, grid);
             }           

          }
      }

};

void A_star::Right_path(std::vector<int> &temp_path, Grid& grid, int number, std::vector<int> &right_path){

   int temp_int;

   for(int i=0;i<(int)temp_path.size();i++){

        std::cout<<"current node metal "<<grid.vertices_total[temp_path[i]].metal<<std::endl;
        std::cout<<"i"<<i<<std::endl;
        if(i>0){
          std::cout<<grid.vertices_total.size()<<std::endl;
          std::cout<<"temp_path[i]"<<temp_path[i]<<"temp_path[i-1]"<<temp_path[i-1]<<std::endl;
          std::cout<<"last node metal "<<grid.vertices_total[temp_path[i-1]].metal<<std::endl;
          }

        if(drc_info.Metal_info[grid.vertices_total[temp_path[i]].metal].direct==0){//vertical
           std::cout<<"check poing s 1.1"<<std::endl;
           int index = number;
           temp_int = temp_path[i];

           if(i==0){

             //source part
             if((int)temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i+1]].metal){
                     std::cout<<"checkpoint s 1"<<std::endl;
                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].east[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint17"<<std::endl;
                     right_path_SD(temp_int, number, grid, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==-1){
                     std::cout<<"checkpoint s 2"<<std::endl;
                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].south[0];
                         index = index -1;
                       }

                     std::cout<<"Checkpoint18"<<std::endl;
                     Down_up_path(temp_int, grid, 0, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==1){
                     std::cout<<"checkpoint s 3"<<std::endl;
                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].south[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint19"<<std::endl;
                     Down_up_path(temp_int, grid, 1, right_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;

               }
             
             }

           if(i==(int)temp_path.size()-1){

             //dest part
             if((int)temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i-1]].metal){

                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].east[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint20"<<std::endl;
                     right_path_SD(temp_int, number, grid, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==-1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].south[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint21"<<std::endl;
                     Down_up_path(temp_int, grid, 0, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].south[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint22"<<std::endl;
                     Down_up_path(temp_int, grid, 1, right_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;

               }
             
             }           

           std::cout<<"Checkpoint23"<<std::endl;

           while(index>0){
                 temp_int = grid.vertices_total_full_connected[temp_int].east[0];
                 index = index -1;
                }

           int end_size =(int) right_path.size()-1;

           if(grid.vertices_total[temp_int].metal == grid.vertices_total[right_path[end_size]].metal){
             
               right_path.push_back(temp_int);
            
             }else if(grid.vertices_total[temp_int].metal > grid.vertices_total[right_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[right_path[end_size]].metal==1){ //up
              
               XY_search(right_path[end_size], temp_int, right_path, 1, grid);

             }else if(grid.vertices_total[temp_int].metal < grid.vertices_total[right_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[right_path[end_size]].metal==-1){//down

               XY_search(right_path[end_size], temp_int, right_path, 0, grid);
               
             }


          }else{

           int index = number;
           temp_int = temp_path[i];

           if(i==0){

             //source part
             if((int)temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i+1]].metal){

                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].south[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint24"<<std::endl;
                     right_path_SD(temp_int, number, grid, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==-1){

                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].east[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint25"<<std::endl;
                     Down_up_path(temp_int, grid, 0, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i+1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i+1]].metal==1){

                     int index = number;
                     temp_int = temp_path[i+1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].east[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint26"<<std::endl;
                     Down_up_path(temp_int, grid, 1, right_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;

               }
             
             }

           if(i==(int)temp_path.size()-1){

             //dest part
             if((int)temp_path.size()>2){

                 if(grid.vertices_total[temp_path[i]].metal==grid.vertices_total[temp_path[i-1]].metal){

                     int index = number;
                     temp_int = temp_path[i];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].south[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint27"<<std::endl;
                     right_path_SD(temp_int, number, grid, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal<grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==-1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].east[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint28"<<std::endl;
                     Down_up_path(temp_int, grid, 0, right_path);
                     continue;

                   }else if(grid.vertices_total[temp_path[i]].metal>grid.vertices_total[temp_path[i-1]].metal and grid.vertices_total[temp_path[i]].metal-grid.vertices_total[temp_path[i-1]].metal==1){

                     int index = number;
                     temp_int = temp_path[i-1];

                     while(index>0){
                         temp_int = grid.vertices_total_full_connected[temp_int].east[0];
                         index = index -1;
                       }
                     std::cout<<"Checkpoint29"<<std::endl;
                     Down_up_path(temp_int, grid, 1, right_path);
                     continue;

                   }
                 
               }else{
  
                 std::cout<<"Path error, source and dest are the same point"<<std::endl;

               }
             
             }    
           std::cout<<"Checkpoint30"<<std::endl;

           while(index>0){
                 temp_int = grid.vertices_total_full_connected[temp_int].south[0];
                 index = index -1;
                }

           int end_size =(int) right_path.size()-1;
           if(grid.vertices_total[temp_int].metal == grid.vertices_total[right_path[end_size]].metal){
             
               right_path.push_back(temp_int);
            
             }else if(grid.vertices_total[temp_int].metal > grid.vertices_total[right_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[right_path[end_size]].metal==1){ //up

               YX_search(right_path[end_size], temp_int, right_path, 1, grid);

             }else if(grid.vertices_total[temp_int].metal < grid.vertices_total[right_path[end_size]].metal and grid.vertices_total[temp_int].metal - grid.vertices_total[right_path[end_size]].metal==-1){//down

               YX_search(right_path[end_size], temp_int, right_path, 0, grid);
             }           

          }
      }

};

void A_star::CovertToShieldingNet(Grid& grid, std::vector<int> &real_path, std::vector<int> &temp_path){

  std::cout<<"start shielding path "<<"temp_path number "<<temp_path.size()<<std::endl;
  
  std::vector<int> temp_shielding_path;
  
  for(int i=1;i<(int)temp_path.size()-1;i++){

       temp_shielding_path.push_back(temp_path[i]);

     }

  std::cout<<"temp shielding number "<<temp_shielding_path.size()<<std::endl;

  if((int)real_path.size()<2){std::cout<<"Path Error"<<std::endl;return;}

  int shielding_start_point = real_path[1];
  int shielding_end_point = real_path[(int)real_path.size()-2];

  std::vector<int> start_to_end_path;
  int se_lock=1;
  
  for(int i=0;i<(int)temp_shielding_path.size();i++){

      if(se_lock==0){start_to_end_path.push_back(temp_shielding_path[i]);}

      if(se_lock and drc_info.Metal_info[grid.vertices_total[shielding_start_point].metal].direct==0){//vertical

          if(grid.vertices_total[temp_shielding_path[i]].metal == grid.vertices_total[shielding_start_point].metal and grid.vertices_total[temp_shielding_path[i]].y == grid.vertices_total[shielding_start_point].y){

             se_lock=0;
             start_to_end_path.push_back(temp_shielding_path[i]); 

            }

        }else if(se_lock and drc_info.Metal_info[grid.vertices_total[shielding_start_point].metal].direct==1){

          if(grid.vertices_total[temp_shielding_path[i]].metal == grid.vertices_total[shielding_start_point].metal and grid.vertices_total[temp_shielding_path[i]].x == grid.vertices_total[shielding_start_point].x){

             se_lock=0;
             start_to_end_path.push_back(temp_shielding_path[i]); 

            }
        }
 
     }

  std::cout<<"start end shielding number "<<start_to_end_path.size()<<std::endl;

  std::vector<int> end_to_start_path;
  int es_lock=1;

  for(int i=(int)start_to_end_path.size()-1;i>-1;i--){

      if(es_lock==0){end_to_start_path.push_back(start_to_end_path[i]);}

      if(es_lock and drc_info.Metal_info[grid.vertices_total[shielding_end_point].metal].direct==0){//vertical

          if(grid.vertices_total[start_to_end_path[i]].metal == grid.vertices_total[shielding_end_point].metal and grid.vertices_total[start_to_end_path[i]].y == grid.vertices_total[shielding_end_point].y){

             es_lock=0;
             end_to_start_path.push_back(start_to_end_path[i]); 

            }

        }else if(es_lock and drc_info.Metal_info[grid.vertices_total[shielding_end_point].metal].direct==1){

          if(grid.vertices_total[start_to_end_path[i]].metal == grid.vertices_total[shielding_end_point].metal and grid.vertices_total[start_to_end_path[i]].x == grid.vertices_total[shielding_end_point].x){

             es_lock=0;
             end_to_start_path.push_back(start_to_end_path[i]); 

            }
        }
 
     }

  std::set<int> src_index;
  std::set<int> dest_index;
  for(int i=0;i<(int)source.size();i++){
      src_index.insert(source[i]);
     }
  for(int i=0;i<(int)dest.size();i++){
      dest_index.insert(dest[i]);
     }
  std::vector<int> shielding_path;
  for(int i=0;i<(int)end_to_start_path.size();i++){

      if(src_index.find(end_to_start_path[i])==src_index.end() and dest_index.find(end_to_start_path[i])==dest_index.end()){
   
         shielding_path.push_back(end_to_start_path[i]);

         }

     }
  

  temp_path = shielding_path;
  
  std::cout<<"End shielding path "<<" shielding path number "<<end_to_start_path.size()<<std::endl;

};

void A_star::CopyPath(Grid& grid, int left_up, int right_down){

  std::cout<<"start copy path"<<std::endl;

  std::vector<int> real_path;

  if((int)Path.size()>0){

  real_path = Path[0];

  }else{

   return;
   
  }

  std::vector<int> temp_path;

  for(int i=0;i<left_up;i++){

      Left_path(real_path, grid, i+1, temp_path);

      if(shielding and i==left_up-1){
  
        CovertToShieldingNet(grid,real_path,temp_path);

        }

      Path.push_back(temp_path);
      temp_path.clear();
      
     }

  for(int i=0;i<right_down;i++){

      Right_path(real_path, grid, i+1, temp_path);

      if(shielding and i==right_down-1){

        CovertToShieldingNet(grid,real_path,temp_path);

        }

      Path.push_back(temp_path);
      temp_path.clear();
      
     }

  std::cout<<"end copy path"<<std::endl;

};

void A_star::refreshGrid(Grid& grid){

  for(int i=0;i<(int)grid.vertices_total.size();i++){
       grid.vertices_total[i].Cost = -1;
       grid.vertices_total[i].parent = -1;
     }
};

std::vector<std::vector<int>> A_star::GetPath(){
  std::vector<std::vector<int>> path(Path);
  return (path);
}
