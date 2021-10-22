#include "A_star.h"
#include "spdlog/spdlog.h"

//Q: via active up/down is not considered yet
//Q: NO parallel routing, maybe just repeatly routing for a net is a better solution. This is an important problem
//Q: parrallel routing, but with some post routing processing
//Q: what about shiedling and symmetry routing 



A_star::A_star(Grid& grid, bool shielding):drc_info(grid.drc_info){

  this->path_number=1;
  source = grid.Source;
  dest = grid.Dest;
  this->shielding = shielding;

};


bool A_star::FindFeasiblePath(Grid& grid, int pathNo, int left_up, int right_down) {

  auto logger = spdlog::default_logger()->clone("router.A_star.FindFeasiblePath");

  bool mark=false;
  for(int i =0;i<pathNo;++i){

     logger->debug("Path No {0} current path index {1}",pathNo,i);

     std::vector<std::vector<int> > temp_path;
     logger->debug("start A_star");

     temp_path = A_star_algorithm(grid, left_up, right_down);// grid.Source grid.dest
     logger->debug("end A_star");

     if((int)temp_path.size()>0) {
       Path = temp_path;
       mark=true;
     } else {
       mark=(mark || false);
       logger->warn("Router-Warning: feasible path might not be found");
     }
  }
  return mark;

}

bool A_star::FindFeasiblePath_sym(Grid& grid, int pathNo, int left_up, int right_down, std::vector<RouterDB::Metal> &sym_path) {

  auto logger = spdlog::default_logger()->clone("router.A_star.FindFeasiblePath");

  bool mark=false;
  for(int i =0;i<pathNo;++i){

     logger->debug("Path No {0} current path index {1}",pathNo,i);

     std::vector<std::vector<int> > temp_path;
     logger->debug("start A_star");

     temp_path = A_star_algorithm_Sym(grid, left_up, right_down, sym_path);// grid.Source grid.dest
     logger->debug("end A_star");

     if((int)temp_path.size()>0) {
       Path = temp_path;
       mark=true;
     } else {
       mark=(mark || false);
       logger->warn("Router-Warning: feasible path might not be found");
     }
  }
  return mark;

}

void A_star::print_path(){

  auto logger = spdlog::default_logger()->clone("router.A_star.print_path");

  for(unsigned int i=0;i<Path.size();i++){
     for(unsigned int j =0; j<Path.size();j++){
        logger->debug("{0} ",Path[i][j]);
     }
  }


};

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
           if(j<(int) Path[i].size()-1 && grid.vertices_total[Path[i][j]].metal!=grid.vertices_total[Path[i][j+1]].metal){
              flag_start_write = 1;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              temp_metal.width = grid.drc_info.Metal_info[grid.vertices_total[Path[i][j]].metal].width;
              temp_physical_path.push_back(temp_metal);
            }
            if(j==(int) Path[i].size()-1 && flag_start_write == 0){

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

std::vector<std::vector<int> > A_star::GetExtendLabel(){
  return Extend_labels;
}

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

void A_star::initial_source(Grid& grid, std::set<std::pair<int,int>, RouterDB::pairComp>& L_list, std::vector<int> &source){
  
  for(int i=0;i<(int)source.size();i++){

         int Mdis = Manhattan_distan(source[i], grid);
         grid.vertices_total[source[i]].Cost = 0;
         int dis = grid.vertices_total[source[i]].Cost + Mdis;
         std::pair<int,int> temp_pair;
         temp_pair.first = dis;
         temp_pair.second = source[i];
         L_list.insert(temp_pair);

     }

};

bool A_star::expand_node_ud(int direction, std::vector<int> &temp_node, Grid &grid){

  //if( direction!= -1 && grid.vertices_total[direction].active && grid.vertices_total[direction].Cost==-1){
  if( direction!= -1 && grid.vertices_total[direction].active){
     temp_node.push_back(direction);
    }

  if((int)temp_node.size()>0){
    return true;
    }else{
    return false;
    }

};

bool A_star::found_near_node(int current_node, Grid &grid, std::vector<int> &candidate_node){

    
    std::vector<int> north_node, south_node, east_node, west_node, up_node, down_node;
    bool north_found, south_found, east_found, west_found, up_found, down_found;

    north_found = expand_node(grid.vertices_total[current_node].north, north_node, grid);
    south_found = expand_node(grid.vertices_total[current_node].south, south_node, grid);
    east_found = expand_node(grid.vertices_total[current_node].east, east_node, grid);
    west_found = expand_node(grid.vertices_total[current_node].west, west_node, grid);

    if(grid.vertices_total[current_node].via_active_up){
       up_found = expand_node_ud(grid.vertices_total[current_node].up, up_node, grid);
    }else{
       up_found = false;
    }
    if(grid.vertices_total[current_node].via_active_down){
      down_found = expand_node_ud(grid.vertices_total[current_node].down, down_node, grid);
    }else{
      down_found = false;
    }

    if(north_found){
       for(int i=0;i<(int)north_node.size();i++){
         //if(grid.vertices_total[current_node].parent!=north_node[i])
         candidate_node.push_back(north_node[i]);
       }
      }
    if(south_found){
       for(int i=0;i<(int)south_node.size();i++){
         //if(grid.vertices_total[current_node].parent!=south_node[i])
         candidate_node.push_back(south_node[i]);
       }
      }
    if(west_found){
       for(int i=0;i<(int)west_node.size();i++){
         //if(grid.vertices_total[current_node].parent!=west_node[i])
         candidate_node.push_back(west_node[i]);
       }
      }

    if(east_found){
       for(int i=0;i<(int)east_node.size();i++){
         //if(grid.vertices_total[current_node].parent!=east_node[i])
         candidate_node.push_back(east_node[i]);
       }
      }

    if(up_found){
       for(int i=0;i<(int)up_node.size();i++){
         //if(grid.vertices_total[current_node].parent!=up_node[i])
         candidate_node.push_back(up_node[i]);
       }
      }

    if(down_found){
       for(int i=0;i<(int)down_node.size();i++){
         //if(grid.vertices_total[current_node].parent!=down_node[i])
         candidate_node.push_back(down_node[i]);
       }
      }

    if((int)candidate_node.size()>0){
       return true;
      }else{
       return false;
      }
};

bool A_star::expand_node(std::vector<int> &direction, std::vector<int> &temp_node, Grid &grid){

  for(int i=0;i<(int)direction.size();i++){
 
       //if(grid.vertices_total[direction[i]].active && grid.vertices_total[direction[i]].Cost==-1){
       if(grid.vertices_total[direction[i]].active){
       temp_node.push_back(direction[i]);
       }
     }

  if((int)temp_node.size()>0){
    return true;
    }else{
    return false;
    }

};


int A_star::trace_back_node_parent(int current_node, Grid& grid, std::set<int> &source_index){

  auto logger = spdlog::default_logger()->clone("router.A_star.trace_back_node_parent");

  int first_node_same_layer = current_node;

  std::set<int> last_nodes;
  last_nodes.insert(current_node);

  bool trace_back_flag = true;

  int dummy_node = current_node;
  logger->debug("trace back node {0} metal {1}",current_node,grid.vertices_total[dummy_node].metal);

  while(trace_back_flag){

    int last_node = grid.vertices_total[dummy_node].parent;

    if(last_node<0 || last_node>=int(grid.vertices_total.size())){
      trace_back_flag = false;
    }else if(grid.vertices_total[last_node].metal == grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      first_node_same_layer = last_node;
      dummy_node = last_node;
    }else if(grid.vertices_total[last_node].metal != grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      trace_back_flag = false;
    }

/*
    if(last_node<0 || last_node>=grid.vertices_total.size()){
      trace_back_flag = false;
    }else if(grid.vertices_total[last_node].metal == grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      first_node_same_layer = last_node;
      dummy_node = last_node;
    }else if(grid.vertices_total[last_node].metal != grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      trace_back_flag = false;
    }else if(last_nodes.find(last_node)!=last_nodes.end() && source_index.find(last_node)!=source_index.end()){
      first_node_same_layer = last_node;
      trace_back_flag = false;
    }else if(last_nodes.find(last_node)!=last_nodes.end() && source_index.find(last_node)==source_index.end()){
      assert(0);
    }
    last_nodes.insert(last_node);
*/
  }

  return first_node_same_layer;


};

int A_star::trace_back_node(int current_node, Grid& grid, std::set<int> &source_index){

  auto logger = spdlog::default_logger()->clone("router.A_star.trace_back_node");

  int first_node_same_layer = current_node;

  std::set<int> last_nodes;
  last_nodes.insert(current_node);

  bool trace_back_flag = true;

  int dummy_node = current_node;
  logger->debug("trace back node {0} metal {1}",current_node,grid.vertices_total[dummy_node].metal);

  while(trace_back_flag){

    int last_node = grid.vertices_total[dummy_node].trace_back_node;

    if(last_node<0 || last_node>=int(grid.vertices_total.size())){
      trace_back_flag = false;
    }else if(grid.vertices_total[last_node].metal == grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      first_node_same_layer = last_node;
      dummy_node = last_node;
    }else if(grid.vertices_total[last_node].metal != grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      trace_back_flag = false;
    }

/*
    if(last_node<0 || last_node>=grid.vertices_total.size()){
      trace_back_flag = false;
    }else if(grid.vertices_total[last_node].metal == grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      first_node_same_layer = last_node;
      dummy_node = last_node;
    }else if(grid.vertices_total[last_node].metal != grid.vertices_total[dummy_node].metal && last_nodes.find(last_node)==last_nodes.end()){
      trace_back_flag = false;
    }else if(last_nodes.find(last_node)!=last_nodes.end() && source_index.find(last_node)!=source_index.end()){
      first_node_same_layer = last_node;
      trace_back_flag = false;
    }else if(last_nodes.find(last_node)!=last_nodes.end() && source_index.find(last_node)==source_index.end()){
      assert(0);
    }
    last_nodes.insert(last_node);
*/
  }

  return first_node_same_layer;


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
       if(next_node<0 || next_node>=int(grid.vertices_total.size()) ) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[first_node_same_layer].x && grid.vertices_total[next_node].y != grid.vertices_total[first_node_same_layer].y) || grid.vertices_total[next_node].metal != grid.vertices_total[first_node_same_layer].metal ){
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
       if(next_node<0 || next_node>=int(grid.vertices_total.size() )) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[current_node].x && grid.vertices_total[next_node].y != grid.vertices_total[current_node].y) || grid.vertices_total[next_node].metal != grid.vertices_total[current_node].metal){
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

bool A_star::CheckExendable_With_Certain_Length_Head_Extend(int first_node_same_layer,int current_node,int length,int minL,Grid &grid, int &direction){

  int half_minL = ceil( ( (double) minL -  (double) length) );

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
       if(next_node<0 || next_node>=int(grid.vertices_total.size()) ) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[first_node_same_layer].x && grid.vertices_total[next_node].y != grid.vertices_total[first_node_same_layer].y) || grid.vertices_total[next_node].metal != grid.vertices_total[first_node_same_layer].metal ){
          search_flag = false;
          feasible = false;
       }else {
          culmulated_length = abs(grid.vertices_total[next_node].x-grid.vertices_total[first_node_same_layer].x) + abs( grid.vertices_total[next_node].y-grid.vertices_total[first_node_same_layer].y);
          dummy_node = next_node;
       }
     }
  }
  direction = first_direction;
  return feasible;

};

bool A_star::CheckExendable_With_Certain_Length_Tail_Extend(int first_node_same_layer,int current_node,int length,int minL,Grid &grid, int &direction){

  int half_minL = ceil( ( (double) minL -  (double) length) );

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

  int culmulated_length = 0;
  bool search_flag = true;
  int dummy_node = current_node;
  while(search_flag){
     if(culmulated_length>=half_minL){
        search_flag = false;
     }else{
       int next_node = dummy_node + current_direction;
       if(next_node<0 || next_node>=int(grid.vertices_total.size() )) {
          search_flag = false;
          feasible = false;
       }else if(grid.vertices_total[next_node].active==0) {
          search_flag = false;
          feasible = false;
       }else if( (grid.vertices_total[next_node].x != grid.vertices_total[current_node].x && grid.vertices_total[next_node].y != grid.vertices_total[current_node].y) || grid.vertices_total[next_node].metal != grid.vertices_total[current_node].metal){
          search_flag = false;
          feasible = false;
       }else {
          culmulated_length = abs(grid.vertices_total[next_node].x-grid.vertices_total[current_node].x) + abs( grid.vertices_total[next_node].y-grid.vertices_total[current_node].y);
          dummy_node = next_node;
       }
     }
  }
  direction = current_direction;
  return feasible;

};




int A_star::Calculate_Interval_number(Grid& grid, int node){

  auto logger = spdlog::default_logger()->clone("router.A_star.Calculate_Interval_number");

  int interval_number = 1;
  int metal = grid.vertices_total[node].metal;
  int via_space_length = 0;
  int pitches = 0;

  if(drc_info.Metal_info[metal].direct==0){//V

    via_space_length = drc_info.Via_info[metal].width + drc_info.Via_info[metal].dist_ss;
    pitches = drc_info.Metal_info[metal].grid_unit_x;
    interval_number = ceil( (double) via_space_length / pitches);
    logger->debug("metal {0} via_space_length {1} pitches {2}", metal,via_space_length,pitches);
    logger->debug("interval_number 1 {0}",interval_number); 
    //assert(0);

  }else{

    via_space_length = drc_info.Via_info[metal].width_y + drc_info.Via_info[metal].dist_ss_y;
    pitches = drc_info.Metal_info[metal].grid_unit_y;
    interval_number = ceil( (double) via_space_length / pitches);
    logger->debug("metal {0} via_space_length {1} pitches {2}", metal,via_space_length,pitches);
    logger->debug("interval_number 2 {0}",interval_number);  
    //assert(0);

  }

  return interval_number;


};

bool A_star::find_nodes_north(Grid& grid, int node, int number, std::vector<int>& temp_nodes){

  int interval_number = Calculate_Interval_number(grid, node);
  temp_nodes.push_back(node);
  //int current_node = -1;
  while(number!=0){

     int current_node = temp_nodes.back();
     int temp_number = interval_number;
     int n = -1;
     while(temp_number!=0){
        
        if(grid.vertices_total_full_connected[current_node].north.size()>0){ // vertices_total_full_connected // vertices_total
           n = grid.vertices_total_full_connected[current_node].north[0];
        }else{
           n = -1;
        }
        if(n<0 || n>int(grid.vertices_total_full_connected.size()-1)){
          return false;
        }else{
          current_node = n;
        }
        
        temp_number = temp_number - 1;
     }
     
     temp_nodes.push_back(n);

     number = number - 1;

  }

  reverse(temp_nodes.begin(),temp_nodes.end());

  temp_nodes.pop_back();
  return true;

};

bool A_star::find_nodes_east(Grid& grid, int node, int number, std::vector<int>& temp_nodes){

  int interval_number = Calculate_Interval_number(grid, node);
  temp_nodes.push_back(node);
  //int current_node = -1;
  while(number!=0){

     int current_node = temp_nodes.back();
     int temp_number = interval_number;
     int n = -1;
     while(temp_number!=0){
        
        if(grid.vertices_total_full_connected[current_node].east.size()>0){
           n = grid.vertices_total_full_connected[current_node].east[0];
        }else{
           n = -1;
        }
        if(n<0 || n>int(grid.vertices_total_full_connected.size()-1)){
          return false;
        }else{
          current_node = n;
        }
        
        temp_number = temp_number - 1;
     }
     
     temp_nodes.push_back(n);

     number = number - 1;

  }

  reverse(temp_nodes.begin(),temp_nodes.end());

  temp_nodes.pop_back();
  return true;

};

bool A_star::find_nodes_west(Grid& grid, int node, int number, std::vector<int>& temp_nodes){

  int interval_number = Calculate_Interval_number(grid, node);
  temp_nodes.push_back(node);
  //int current_node = -1;
  while(number!=0){

     int current_node = temp_nodes.back();
     int temp_number = interval_number;
     int n = -1;
     while(temp_number!=0){
        
        if(grid.vertices_total_full_connected[current_node].west.size()>0){
           n = grid.vertices_total_full_connected[current_node].west[0];
        }else{
           n = -1;
        }
        if(n<0 || n>int(grid.vertices_total_full_connected.size()-1)){
          return false;
        }else{
          current_node = n;
        }
        
        temp_number = temp_number - 1;
     }
     
     temp_nodes.push_back(n);

     number = number - 1;

  }

  reverse(temp_nodes.begin(),temp_nodes.end());

  temp_nodes.pop_back();
  return true;

};

bool A_star::find_nodes_south(Grid& grid, int node, int number, std::vector<int>& temp_nodes){

  int interval_number = Calculate_Interval_number(grid, node);
  temp_nodes.push_back(node);
  //int current_node = -1;
  while(number!=0){

     int current_node = temp_nodes.back();
     int temp_number = interval_number;
     int n = -1;
     while(temp_number!=0){
        
        if(grid.vertices_total_full_connected[current_node].south.size()>0){
           n = grid.vertices_total_full_connected[current_node].south[0];
        }else{
           n = -1;
        }
        if(n<0 || n>int(grid.vertices_total_full_connected.size()-1)){
          return false;
        }else{
          current_node = n;
        }
        
        temp_number = temp_number - 1;
     }
     
     temp_nodes.push_back(n);

     number = number - 1;

  }

  reverse(temp_nodes.begin(),temp_nodes.end());

  temp_nodes.pop_back();
  return true;

};

bool A_star::Check_Src_Dest(std::vector<int> &nodes, std::set<int> &src_dest){


  for(unsigned int i=0;i<nodes.size();i++){
     if(src_dest.find(nodes[i])==src_dest.end()){
       return false;
     }
  }
  return true;

};

bool A_star::find_succsive_parallel_node(Grid& grid, int current_node, int left, int right, int mode, std::vector<int> &nodes, std::set<int> &src_index, int &cost){

  int penety = 0; // 100000
  //int hide_mode = 0;

  if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==0){//v

    vector<int> temp_nodes;
    int exist = 0;
    if(mode==0){
/*
      if(hide_mode){
        exist = find_nodes_west(grid, current_node, left, temp_nodes);
        exist = Check_Src_Dest(temp_nodes, src_index);
      }
*/
      if(!exist){
         temp_nodes.clear();
         exist = find_nodes_south(grid, current_node, left, temp_nodes);
         cost = penety;
        }

    if(exist)
      exist = Check_Src_Dest(temp_nodes, src_index);
    }else{
      exist = find_nodes_west(grid, current_node, left, temp_nodes);
    }

    if(exist){
      nodes.insert(nodes.end(),temp_nodes.begin(),temp_nodes.end());
    }else{
     return false;
    }
    
  }else{

    vector<int> temp_nodes;
    int exist=0;
    if(mode==0){
/*
      if(hide_mode){
        exist = find_nodes_south(grid, current_node, left, temp_nodes);
        exist = Check_Src_Dest(temp_nodes, src_index);
        }
*/
      if(!exist){
         temp_nodes.clear();
         exist = find_nodes_west(grid, current_node, left, temp_nodes);
         cost = penety;
        }

      if(exist)
      exist = Check_Src_Dest(temp_nodes, src_index);
    }else{
      exist = find_nodes_south(grid, current_node, left, temp_nodes);
    }

    if(exist){
      nodes.insert(nodes.end(),temp_nodes.begin(),temp_nodes.end());
    }else{
     return false;
    }

  }

  nodes.push_back(current_node);


  if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==0){//v

    vector<int> temp_nodes;
    int exist=0;

    if(mode==0){
/*      if(hide_mode){
        exist = find_nodes_east(grid, current_node, right, temp_nodes);
        exist = Check_Src_Dest(temp_nodes, src_index);
      }
*/
      if(!exist){
         temp_nodes.clear();
         exist = find_nodes_north(grid, current_node, right, temp_nodes);
         cost = penety;
      }

      if(exist)
      exist = Check_Src_Dest(temp_nodes, src_index);
    }else{
      exist = find_nodes_east(grid, current_node, right, temp_nodes);
    }

    if(exist){
      nodes.insert(nodes.end(),temp_nodes.begin(),temp_nodes.end());
    }else{
     return false;
    }
    
  }else{

    vector<int> temp_nodes;
    int exist=0;
    if(mode==0){
/*
      if(hide_mode){
        exist = find_nodes_north(grid, current_node, right, temp_nodes);
        exist = Check_Src_Dest(temp_nodes, src_index);
      }
*/
      if(!exist){
        temp_nodes.clear();
        exist = find_nodes_east(grid, current_node, right, temp_nodes);
        cost = penety;
      }

      if(exist)
      exist = Check_Src_Dest(temp_nodes, src_index);
    }else{
      exist = find_nodes_north(grid, current_node, right, temp_nodes);
    }

    if(exist){
      nodes.insert(nodes.end(),temp_nodes.begin(),temp_nodes.end());
    }else{
     return false;
    }

  }

  return true;

};

bool A_star::parallel_routing(Grid& grid, int current_node, int next_node, int left, int right, std::set<int> &src_index, std::set<int> &dest_index, std::vector<std::vector<int> > &node_L_path, int &cost){

  auto logger = spdlog::default_logger()->clone("router.A_star.parallel_routing");

  std::vector<int> start_points;
  std::vector<int> end_points;
  bool found_s;
  bool found_e;  

  if(src_index.find(current_node)!=src_index.end()){
    int mode = 0; //succsive

    found_s = find_succsive_parallel_node(grid, current_node, left, right, mode, start_points, src_index, cost);

  }else{
    int mode = 1; //parallel
    found_s = find_succsive_parallel_node(grid, current_node, left, right, mode, start_points, src_index, cost);
  }

  if(dest_index.find(next_node)!=dest_index.end()){
    int mode = 0; //succsive

    found_e = find_succsive_parallel_node(grid, next_node, left, right, mode, end_points, dest_index, cost);

  }else{
    int mode = 1; //parallel

    found_e = find_succsive_parallel_node(grid, next_node, left, right, mode, end_points, dest_index, cost);
  }



  if(found_s && found_e){

     //assert(0);
     logger->debug("L shape connection 1");
     if(grid.vertices_total[current_node].metal!=grid.vertices_total[next_node].metal){
        if(!Extention_check_prime(grid, current_node, next_node, src_index)){
           return false;
         }
     }
     bool found = L_shape_Connection(grid, start_points, end_points, node_L_path);
     logger->debug("L shape connection 2");
     return found;
  }else{
    return false;
  }

};


bool A_star::L_shape_Connection(Grid& grid, std::vector<int> &start_points, std::vector<int> &end_points, std::vector<std::vector<int> > &node_L_path){

  for(unsigned int i=0;i<start_points.size();i++){
      int s_node = start_points[i];
      int e_node = end_points[i];
      std::vector<int> node_set;
      bool connection = L_shape_Connection_Check(grid,s_node,e_node,node_set);
      node_L_path.push_back(node_set);
      if(!connection){return false;}

  }

  return true;

};


bool A_star::L_shape_Connection_Check(Grid& grid, int start_points, int end_points, std::vector<int> &node_set){

  auto logger = spdlog::default_logger()->clone("router.A_star.L_shape_Connection_Check");

  std::vector<int> node_set_up;
  std::set<int> unit_node_set_up;
  node_set_up.push_back(start_points);
  //int count = 10;
  while(node_set_up.back()!=end_points){ // QQQ: might be stacked here

    int current_node = node_set_up.back();
    if(unit_node_set_up.find(current_node)!=unit_node_set_up.end()){
       return false;
    }
    unit_node_set_up.insert(current_node);

    int x = grid.vertices_total[end_points].x - grid.vertices_total[current_node].x;
    if(x>0){x=1;}else if(x<0){x=-1;}
    int y = grid.vertices_total[end_points].y - grid.vertices_total[current_node].y;
    if(y>0){y=1;}else if(y<0){y=-1;}
    int metal = grid.vertices_total[end_points].metal - grid.vertices_total[current_node].metal;
    if(metal>0){metal=1;}else if(metal<0){metal=-1;}
    int dummy_layer = 1; // go up

    int next = find_next_node(grid, current_node, x, y, metal, dummy_layer);

    //assert(0);
    if(next <0 || next>= int(grid.vertices_total.size())){
      return false;
    }else if(next>=0 && next< int(grid.vertices_total.size()) ){
      node_set_up.push_back(next); 
    }else{
      logger->error("L shape connection check bug, next node is out of grid");
      assert(0);
    }
    
  }


  std::vector<int> node_set_down;
  std::set<int> unit_node_set_down;
  node_set_down.push_back(start_points);

  while(node_set_down.back()!=end_points){ // QQQ: might be stacked here

    int current_node = node_set_down.back();
    if(unit_node_set_down.find(current_node)!=unit_node_set_down.end()){
       return false;
    }
    unit_node_set_down.insert(current_node);

    int x = grid.vertices_total[end_points].x - grid.vertices_total[current_node].x;
    if(x>0){x=1;}else if(x<0){x=-1;}
    int y = grid.vertices_total[end_points].y - grid.vertices_total[current_node].y;
    if(y>0){y=1;}else if(y<0){y=-1;}
    int metal = grid.vertices_total[end_points].metal - grid.vertices_total[current_node].metal;
    if(metal>0){metal=1;}else if(metal<0){metal=-1;}
    int dummy_layer = -1; // go down
    int next = find_next_node(grid, current_node, x, y, metal, dummy_layer);
    if(next <0 || next>= int(grid.vertices_total.size())){
      return false;
    }else if(next>=0 && next< int(grid.vertices_total.size() )){
      //grid.vertices_total[next].trace_back_node = current_node;
      node_set_down.push_back(next); 
    }else{
      logger->error("L shape connection check bug, next node is out of grid");
      assert(0);
    }
    
  }

  //bool extend_up = Extention_checks(grid, node_set_up);
  //bool extend_down = Extention_checks(grid, node_set_down);
  //bool extend_up = 1;
  //bool extend_down = 1;

  bool activa_up = Check_activa_via_active(grid, node_set_up);
  bool activa_down = Check_activa_via_active(grid, node_set_down);
  //bool activa_up = 1;
  //bool activa_down = 1;
  

  if( ( activa_up) || (activa_down)){
    if(( activa_up)) node_set = node_set_up;
    if(( activa_down)) node_set = node_set_down;
    return true;
  }else{
    return false;
  }

};

int A_star::find_next_node( Grid& grid, int current_node, int x, int y, int layer, int dummy_layer){

  int next_node = -1;

  if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==1 && x!=0){//h
    next_node = current_node + x;
  }else if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==1 && x==0 && layer!=0){
    if(layer>0){
      next_node = grid.vertices_total[current_node].up;
    }else{
      next_node = grid.vertices_total[current_node].down;
    }
  }else if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==1 && x==0 && layer==0){
    if(dummy_layer>0){
      next_node = grid.vertices_total[current_node].up;
    }else{
      next_node = grid.vertices_total[current_node].down;
    }
  }else if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==0 && y!=0){//v
    next_node = current_node + y;
  }else if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==0 && y==0 && layer!=0){
    if(layer>0){
      next_node = grid.vertices_total[current_node].up;
    }else{
      next_node = grid.vertices_total[current_node].down;
    }
  }else if(drc_info.Metal_info[grid.vertices_total[current_node].metal].direct==0 && y==0 && layer==0){
    if(dummy_layer>0){
      next_node = grid.vertices_total[current_node].up;
    }else{
      next_node = grid.vertices_total[current_node].down;
    }
  }

  return next_node;


};

/*
bool A_star::Check_activa_via_active(Grid& grid, std::vector<int> &nodes){

  for(int i=0;i<nodes.size();i++){

     int parent = grid.vertices_total[nodes[i]].parent;
     if(parent==-1){
        continue;
     }else if(parent <0 || parent> grid.vertices_total.size() -1){
        logger->error("Check active via active bug, parent out of grid");
     }
     int parent_metal = grid.vertices_total[parent].metal;
     int current_metal = grid.vertices_total[nodes[i]].metal;
     if(parent_metal == current_metal && !grid.vertices_total[nodes[i]].active){
       return false;
     }else if(parent_metal > current_metal && (!grid.vertices_total[nodes[i]].active || !grid.vertices_total[nodes[i]].via_active_up || !grid.vertices_total[parent].active || !grid.vertices_total[parent].via_active_down)){
       return false;
     }else if(parent_metal < current_metal && (!grid.vertices_total[nodes[i]].active || !grid.vertices_total[nodes[i]].via_active_down || !grid.vertices_total[parent].active || !grid.vertices_total[parent].via_active_up)){
       return false;
     }
     
  }
  
  return true;
  

};
*/

bool A_star::Check_activa_via_active(Grid& grid, std::vector<int> &nodes){

  if(nodes.size()==0 || !grid.vertices_total[nodes[0]].active){
    return false;
  }

  for(unsigned int i=1;i<nodes.size();i++){

     if(nodes[i]<0 || nodes[i]>int(grid.vertices_total.size() -1) || !grid.vertices_total[nodes[i]].active){
        return false;
     }
     //Q here is a bug?
     //Q other extention way?
     int parent = nodes[i-1]; //there is a bug when nodes is only one, should use trace_back_node
     int parent_metal = grid.vertices_total[parent].metal;
     int current_metal = grid.vertices_total[nodes[i]].metal;

     if(parent_metal == current_metal && !grid.vertices_total[nodes[i]].active){
       return false;
     }else if(parent_metal > current_metal && (!grid.vertices_total[nodes[i]].active || !grid.vertices_total[nodes[i]].via_active_up || !grid.vertices_total[parent].active || !grid.vertices_total[parent].via_active_down)){
       return false;
     }else if(parent_metal < current_metal && (!grid.vertices_total[nodes[i]].active || !grid.vertices_total[nodes[i]].via_active_down || !grid.vertices_total[parent].active || !grid.vertices_total[parent].via_active_up)){
       return false;
     }
    
  }
  
  return true;
  

};


bool A_star::Extention_checks(Grid& grid, std::vector<int> &nodes, std::set<int> &source_index){

  for(unsigned int i=0;i<nodes.size();i++){
     if(!Extention_check(grid, nodes[i], source_index)){
        return false;
     }
  }

  return true;

};

bool A_star::Extention_check_prime(Grid& grid, int current_node, int next_node, std::set<int> &source_index){

  
  int node_same_layer = trace_back_node_parent(current_node,grid, source_index);
  if(source_index.find(node_same_layer)!=source_index.end()) return true;
  int metal = grid.vertices_total[current_node].metal;
  int length = abs(grid.vertices_total[current_node].x - grid.vertices_total[node_same_layer].x) + abs(grid.vertices_total[current_node].y - grid.vertices_total[node_same_layer].y);
  int minL = drc_info.Metal_info[metal].minL;
  int delta_length = length - minL;
  int temp_parent = grid.vertices_total[node_same_layer].parent;
  int via_space_length = 0;
  if(temp_parent != -1){
     if(grid.vertices_total[temp_parent].metal==grid.vertices_total[next_node].metal){
        int via_index = 0;
        int metal_index = grid.vertices_total[current_node].metal;
        int metal_direct =  drc_info.Metal_info[metal_index].direct;
        if(grid.vertices_total[current_node].metal<grid.vertices_total[next_node].metal){
             via_index = grid.vertices_total[current_node].metal;
           }else{
             via_index = grid.vertices_total[next_node].metal;
           }
        if(metal_direct==1){//H
             via_space_length = drc_info.Via_info[via_index].width + drc_info.Via_info[via_index].dist_ss;
          }else{
             via_space_length = drc_info.Via_info[via_index].width_y + drc_info.Via_info[via_index].dist_ss_y;
          }
        }
      }

  if(delta_length<0 && length >= via_space_length){
       int direction;
       bool feasible_half = CheckExendable_With_Certain_Length(node_same_layer,current_node,length,minL,grid);
       bool feasible_head = CheckExendable_With_Certain_Length_Head_Extend(node_same_layer,current_node,length,minL,grid,direction);
       bool feasible_tail = CheckExendable_With_Certain_Length_Tail_Extend(node_same_layer,current_node,length,minL,grid,direction);
       return feasible_half or feasible_head or feasible_tail;
    }else if(length >= via_space_length){
       return true;
    }else{
       return false;
    }
  

};

bool A_star::Extention_check(Grid& grid, int current_node, std::set<int> &source_index){

  auto logger = spdlog::default_logger()->clone("router.A_star.Extention_check");

  int parent = grid.vertices_total[current_node].trace_back_node;

  //if(parent==-1 || source_index.find(parent)!=source_index.end()){
  if(parent==-1 ){
    return true;
  }
  if(parent>=0 && parent<int(grid.vertices_total.size())){

    if(grid.vertices_total[current_node].metal==grid.vertices_total[parent].metal){
      return true;
    }else{
       int node_same_layer = trace_back_node(parent,grid, source_index);
       if(source_index.find(node_same_layer)!=source_index.end()) return true;
       int metal = grid.vertices_total[parent].metal;
       int length = abs(grid.vertices_total[parent].x - grid.vertices_total[node_same_layer].x) + abs(grid.vertices_total[parent].y - grid.vertices_total[node_same_layer].y);
       int minL = drc_info.Metal_info[metal].minL;
       //int minL = 0;
       int delta_length = length - minL;
       int temp_parent = grid.vertices_total[node_same_layer].trace_back_node;
       int via_space_length = 0;
       if(temp_parent != -1){
          if(grid.vertices_total[temp_parent].metal==grid.vertices_total[current_node].metal){
            int via_index = 0;
            int metal_index = grid.vertices_total[parent].metal;
            int metal_direct =  drc_info.Metal_info[metal_index].direct;
            if(grid.vertices_total[parent].metal<grid.vertices_total[current_node].metal){
                via_index = grid.vertices_total[parent].metal;
              }else{
                via_index = grid.vertices_total[current_node].metal;
              }
            if(metal_direct==1){//H
                via_space_length = drc_info.Via_info[via_index].width + drc_info.Via_info[via_index].dist_ss;
              }else{
                via_space_length = drc_info.Via_info[via_index].width_y + drc_info.Via_info[via_index].dist_ss_y;
              }
          }
       }
       if(delta_length<0 && length >= via_space_length){
           int direction;
           bool feasible_half = CheckExendable_With_Certain_Length(node_same_layer,parent,length,minL,grid);
           bool feasible_head = CheckExendable_With_Certain_Length_Head_Extend(node_same_layer,parent,length,minL,grid,direction);
           bool feasible_tail = CheckExendable_With_Certain_Length_Tail_Extend(node_same_layer,parent,length,minL,grid,direction);
           return feasible_half or feasible_head or feasible_tail;
       }else if(length >= via_space_length){
           return true;
       }

    }
 
  }else{
    logger->error("Extention check bug parent node is out of grid");
    assert(0);
  }
  return true;
};

std::vector<int> A_star::extend_manner_direction_check(std::vector<int> temp_path, Grid &grid){

  std::vector<std::pair<int,int> > path_pairs;
  int temp_metel = -1;
  std::pair<int,int> temp_pair;
  temp_pair.first = -1;

  //std::cout<<"a star path "<<temp_path.size()<<std::endl;

  for(int i=0;i<temp_path.size();++i){

     //std::cout<<temp_path[i]<<" ";

     if(grid.vertices_total[temp_path[i]].metal!=temp_metel){
        if(temp_pair.first!=-1){
           path_pairs.push_back(temp_pair);
        }
        temp_pair.first = temp_path[i];
        temp_pair.second = temp_path[i];
        temp_metel = grid.vertices_total[temp_path[i]].metal;
     }else{
        temp_pair.second = temp_path[i];
     }

     if(i==temp_path.size()-1){
        path_pairs.push_back(temp_pair);
     }
  }
  //std::cout<<std::endl;

  //std::cout<<"a star path_pairs "<<path_pairs.size()<<std::endl;

  std::vector<int> extend_index; //0 not extend, 1 double side, 2 head extend, 3 tail extend, 4 bug case
  for(int i=0;i<path_pairs.size();++i){

     //std::cout<<"<"<<path_pairs[i].first<<","<<path_pairs[i].second<<"> ";
     int direction;
     if(i==0||i==path_pairs.size()-1){
        extend_index.push_back(0);
     }else{
        int length = abs(grid.vertices_total[path_pairs[i].first].x - grid.vertices_total[path_pairs[i].second].x) + abs(grid.vertices_total[path_pairs[i].first].y - grid.vertices_total[path_pairs[i].second].y);
        int metal = grid.vertices_total[path_pairs[i].first].metal;
        int minL = drc_info.Metal_info[metal].minL;
        if(length>=minL){
           extend_index.push_back(0);
        }else if(CheckExendable_With_Certain_Length(path_pairs[i].first,path_pairs[i].second,length,minL,grid)){
          extend_index.push_back(1);
        }else if(CheckExendable_With_Certain_Length_Head_Extend(path_pairs[i].first,path_pairs[i].second,length,minL,grid,direction)){
          if(direction==1)extend_index.push_back(2);
          if(direction==-1)extend_index.push_back(3);
        }else if(CheckExendable_With_Certain_Length_Tail_Extend(path_pairs[i].first,path_pairs[i].second,length,minL,grid,direction)){
          if(direction==1)extend_index.push_back(2);
          if(direction==-1)extend_index.push_back(3);
        }else{
          extend_index.push_back(4);
        }
     }
  }

  //std::cout<<std::endl;
  return extend_index;

};

void A_star::erase_candidate_node(std::set<int> &Close_set, std::vector<int> &candidate){

  std::vector<int> temp_candidate;

  for(unsigned int i = 0;i < candidate.size();i++){

     if(Close_set.find(candidate[i])==Close_set.end()){
         
         temp_candidate.push_back(candidate[i]);
     }

  }

  candidate = temp_candidate;

};

std::vector<std::vector<int> > A_star::A_star_algorithm_Sym(Grid& grid, int left_up, int right_down, vector<RouterDB::Metal> &sym_path){

  auto logger = spdlog::default_logger()->clone("router.A_star.A_star_algorithm_Sym");

  int via_expand_effort = 100;
  std::set<std::pair<int,int>, RouterDB::pairComp> L_list;
  std::set<int> close_set;
  std::pair<int,int> temp_pair; 

  std::set<int> src_index;
  
  logger->debug("source size {0}",source.size());
  logger->debug("dest size {0} ",dest.size());
  
  
  logger->debug("A star source info");
  for(int i=0;i<(int)source.size();i++){
    
      src_index.insert(source[i]);
      logger->debug("Source {0} {1} {2} ",grid.vertices_total[source[i]].metal,grid.vertices_total[source[i]].x,grid.vertices_total[source[i]].y);
      close_set.insert(source[i]);

     }
  
  std::set<int> dest_index;
  for(int i=0;i<(int)dest.size();i++){
      logger->debug("Dest {0} {1} {2}",grid.vertices_total[dest[i]].metal,grid.vertices_total[dest[i]].x,grid.vertices_total[dest[i]].y);
      dest_index.insert(dest[i]);

     }

  initial_source(grid, L_list, source);

  bool found = 0;
  int current_node = -1;

  while(!L_list.empty() && !found){

    std::set<std::pair<int,int>, RouterDB::pairComp>::iterator it;
    it = L_list.begin();
    current_node = it->second;
    L_list.erase(it);
    
    //judge whether dest found Q2// judge whether dest works
    if(dest_index.find(current_node)!=dest_index.end()){

       bool extend = Pre_trace_back(grid, current_node, left_up, right_down, src_index,dest_index); //add pre_trace_back and extendtion check here?

       if(extend){
         found=1;
       }
       continue;
      }
    
    close_set.insert(current_node);


    //found the candidates nodes
    std::vector<int> candidate_node;
    bool near_node_exist =found_near_node(current_node, grid, candidate_node);
    erase_candidate_node(close_set, candidate_node);
    if(!near_node_exist){
       continue;
      }

    std::vector<int> temp_candidate_node;
    std::vector<int> temp_candidate_cost;
    for(unsigned int i=0;i<candidate_node.size();i++){
       std::vector<std::vector<int> > node_L_path;
       int cost = 0;
       bool parallel = parallel_routing(grid, current_node, candidate_node[i], left_up, right_down, src_index, dest_index,node_L_path, cost); //check parents
       //bool parallel = 1;
       if(parallel){
         //assert(0);
         temp_candidate_node.push_back(candidate_node[i]);
         temp_candidate_cost.push_back(cost);
       }
    }

    candidate_node = temp_candidate_node;
    
    if(candidate_node.size()==0){
       //grid.vertices_total[current_node].Cost = INT_MAX;
       continue;
      }


    //std::vector<int> expand_candidate_node;
    for(int i=0;i<(int)candidate_node.size();i++){

       int M_dis = Manhattan_distan(candidate_node[i], grid);
       int temp_cost = grid.vertices_total[current_node].Cost + abs(grid.vertices_total[current_node].x - grid.vertices_total[candidate_node[i]].x) + abs(grid.vertices_total[current_node].y - grid.vertices_total[candidate_node[i]].y) + via_expand_effort*abs(grid.vertices_total[candidate_node[i]].metal-grid.vertices_total[current_node].metal)+temp_candidate_cost[i];
       if(temp_cost < grid.vertices_total[candidate_node[i]].Cost ){

          int sym_cost = Find_Symmetry_Cost(grid,candidate_node[i],sym_path);
          //std::cout<<"sym cost "<<sym_cost<<" sym path size "<<sym_path.size()<<std::endl;
          int sym_factor = 0;

          temp_pair.first = grid.vertices_total[candidate_node[i]].Cost + M_dis +sym_factor*sym_cost;
          temp_pair.second = candidate_node[i];
          if(L_list.find(temp_pair)!=L_list.end()){
              auto temp_l_list = L_list.find(temp_pair);
              L_list.erase(temp_l_list);
            }

          grid.vertices_total[candidate_node[i]].Cost = temp_cost;

          int dis = grid.vertices_total[candidate_node[i]].Cost + M_dis + sym_factor*sym_cost;
          grid.vertices_total[candidate_node[i]].parent = current_node;
          //grid.vertices_total[candidate_node[i]].trace_back_node = current_node;
          temp_pair.first = dis;
          temp_pair.second = candidate_node[i];
          L_list.insert(temp_pair);

         }
      
       }


  }

  std::vector<std::vector<int> > temp_path; //Q4 return sheilding and parallel path?  sheild and parallel should be recovered in outer loop???
  if(found==0){
     logger->debug("A_star fails to find a feasible path");
    }else{
     logger->debug("Trace back paths");
     logger->debug("Source {0}, {1}, {2}",grid.vertices_total[current_node].metal,grid.vertices_total[current_node].x,grid.vertices_total[current_node].y);
     temp_path = Trace_Back_Paths(grid, current_node, left_up, right_down, src_index, dest_index);
    }
   refreshGrid(grid);


   return temp_path;
    
};

int A_star::Find_Symmetry_Cost(Grid& grid, int current_node, vector<RouterDB::Metal> &sym_path){

  int sym_cost = 0;
  if(sym_path.size()==0){
    return sym_cost;
  }else{
    sym_cost = INT_MAX;
    for(unsigned int i=0;i<sym_path.size();++i){
       int sym_cost_temp = Find_Symmetry_cost(grid, current_node, sym_path[i]);
       if(sym_cost_temp<sym_cost){
          sym_cost = sym_cost_temp;
        }
    }
    return sym_cost;
  }
};

int A_star::Find_Symmetry_cost(Grid& grid, int current_node, RouterDB::Metal &temp_path){

  int layer_cost = 100;

  int x = grid.vertices_total[current_node].x;
  int y = grid.vertices_total[current_node].y;
  int metal = grid.vertices_total[current_node].metal;
  
  int metal_cost = abs(metal-temp_path.MetalIdx)*layer_cost;
  int length_cost = 0;

  int direct = drc_info.Metal_info[temp_path.MetalIdx].direct;

  if(direct==1){//H
    length_cost = abs(y-temp_path.LinePoint[0].y);
    int min_x = std::min(temp_path.LinePoint[0].x,temp_path.LinePoint[1].x);
    int max_x = std::max(temp_path.LinePoint[0].x,temp_path.LinePoint[1].x);
    if(x<=max_x && x>=min_x){
      length_cost +=0;
    }else{
      length_cost += std::min(abs(x-min_x),abs(x-max_x));
    }
  }else{
    length_cost = abs(x-temp_path.LinePoint[0].x);
    int min_y = std::min(temp_path.LinePoint[0].y,temp_path.LinePoint[1].y);
    int max_y = std::max(temp_path.LinePoint[0].y,temp_path.LinePoint[1].y);
    if(y<=max_y && y>=min_y){
      length_cost +=0;
    }else{
      length_cost += std::min(abs(y-min_y),abs(y-max_y));
    }

  }
  return metal_cost+length_cost;
};

std::vector<std::vector<int> > A_star::A_star_algorithm(Grid& grid, int left_up, int right_down){

  auto logger = spdlog::default_logger()->clone("router.A_star.A_star_algorithm");

  int via_expand_effort = 100;

  std::set<std::pair<int,int>, RouterDB::pairComp> L_list;
  std::set<int> close_set;
  std::pair<int,int> temp_pair; 

  std::set<int> src_index;
  
  logger->debug("source size {0}",source.size());
  logger->debug("dest size {0} ",dest.size());
  
  logger->debug("A star source info");
  for(int i=0;i<(int)source.size();i++){
    
      src_index.insert(source[i]);
      logger->debug("Source {0} {1} {2} ",grid.vertices_total[source[i]].metal,grid.vertices_total[source[i]].x,grid.vertices_total[source[i]].y);
      close_set.insert(source[i]);

     }
  std::set<int> dest_index;
  for(int i=0;i<(int)dest.size();i++){
      logger->debug("Dest {0} {1} {2}",grid.vertices_total[dest[i]].metal,grid.vertices_total[dest[i]].x,grid.vertices_total[dest[i]].y);
      dest_index.insert(dest[i]);

     }

  initial_source(grid, L_list, source);

  bool found = 0;
  int current_node = -1;

  while(!L_list.empty() && !found){

    std::set<std::pair<int,int>, RouterDB::pairComp>::iterator it;
    it = L_list.begin();
    current_node = it->second;
    L_list.erase(it);

    //judge whether dest found Q2// judge whether dest works
    if(dest_index.find(current_node)!=dest_index.end()){

       bool extend = Pre_trace_back(grid, current_node, left_up, right_down, src_index,dest_index); //add pre_trace_back and extendtion check here?

       if(extend){
         found=1;
       }
       continue;
      }

    //close_set.insert(current_node);


    //found the candidates nodes
    std::vector<int> candidate_node;
    bool near_node_exist =found_near_node(current_node, grid, candidate_node);
    erase_candidate_node(close_set, candidate_node);
    if(!near_node_exist){
       continue;
      }

    std::vector<int> temp_candidate_node;
    std::vector<int> temp_candidate_cost;
    for(unsigned int i=0;i<candidate_node.size();i++){
       std::vector<std::vector<int> > node_L_path;
       int cost = 0;
       bool parallel = parallel_routing(grid, current_node, candidate_node[i], left_up, right_down, src_index, dest_index,node_L_path, cost); //check parents
       //bool parallel = 1;
       if(parallel){
         //assert(0);
         temp_candidate_node.push_back(candidate_node[i]);
         temp_candidate_cost.push_back(cost);
       }
    }

    candidate_node = temp_candidate_node;
    
    if(candidate_node.size()==0){
       continue;
      }


    //std::vector<int> expand_candidate_node;
    for(int i=0;i<(int)candidate_node.size();i++){

       int M_dis = Manhattan_distan(candidate_node[i], grid);
       int temp_cost = grid.vertices_total[current_node].Cost + abs(grid.vertices_total[current_node].x - grid.vertices_total[candidate_node[i]].x) + abs(grid.vertices_total[current_node].y - grid.vertices_total[candidate_node[i]].y) + via_expand_effort*abs(grid.vertices_total[candidate_node[i]].metal-grid.vertices_total[current_node].metal)+temp_candidate_cost[i];
       if(temp_cost < grid.vertices_total[candidate_node[i]].Cost ){
          temp_pair.first = grid.vertices_total[candidate_node[i]].Cost + M_dis;
          temp_pair.second = candidate_node[i];
          if(L_list.find(temp_pair)!=L_list.end()){
              auto temp_l_list = L_list.find(temp_pair);
              L_list.erase(temp_l_list);
            }
          grid.vertices_total[candidate_node[i]].Cost = temp_cost;
          int dis = grid.vertices_total[candidate_node[i]].Cost + M_dis;
          grid.vertices_total[candidate_node[i]].parent = current_node;
          //grid.vertices_total[candidate_node[i]].trace_back_node = current_node;
          temp_pair.first = dis;
          L_list.insert(temp_pair);

         }
      
       }

  }


  std::vector<std::vector<int> > temp_path; //Q4 return sheilding and parallel path?  sheild and parallel should be recovered in outer loop???
  if(found==0){
     logger->debug("A_star fails to find a feasible path");
    }else{
     logger->debug("Trace back paths");
     logger->debug("Source {0}, {1}, {2}",grid.vertices_total[current_node].metal,grid.vertices_total[current_node].x,grid.vertices_total[current_node].y);
     temp_path = Trace_Back_Paths(grid, current_node, left_up, right_down, src_index, dest_index);
    }
   refreshGrid(grid);


   return temp_path;
    
};

void A_star::compact_path(std::vector<std::vector<int> > &Node_Path){

  auto logger = spdlog::default_logger()->clone("router.A_star.compact_path");

  std::vector<std::vector<int> > temp_Node_Path;

  for(unsigned int i=0;i<Node_Path.size();i++){
   
    std::vector<int> temp_path;
    if(Node_Path[i].size()==0){
      logger->error("Node path bug");
      assert(0);
    }
    temp_path.push_back(Node_Path[i][0]);
    for(unsigned int j =1;j<Node_Path[i].size();j++){
       if(Node_Path[i][j]!=Node_Path[i][j-1]){
          temp_path.push_back(Node_Path[i][j]);
       }
    }
    temp_Node_Path.push_back(temp_path);
  }
  
  Node_Path = temp_Node_Path;

};


void A_star::rm_cycle_path(std::vector<std::vector<int> > &Node_Path){

  compact_path(Node_Path);
  std::vector<std::vector<int> > temp_Node_Path;
  
  for(unsigned int i=0; i<Node_Path.size(); i++){
     std::vector<int> temp_path;
     std::vector<int> circle_path_flag(Node_Path[i].size(),0);
     std::set<int> unit_set;
     std::set<int> cycle_set;
     for(unsigned int j =0; j < Node_Path[i].size(); j++){
         if(unit_set.find(Node_Path[i][j])==unit_set.end()){
            unit_set.insert(Node_Path[i][j]);
         }else{
            cycle_set.insert(Node_Path[i][j]);
         }
     }

     for(auto it = cycle_set.begin();it!=cycle_set.end();++it){

        int first_node = -1;
        int end_node = -1;
        for(unsigned int j =0; j < Node_Path[i].size(); j++){
           if(Node_Path[i][j]==*it && first_node==-1){
              first_node = j+1;
           }else if(Node_Path[i][j]==*it){
              end_node = j;
           }  
        }

        for(int j =first_node; j <= end_node; j++){
         circle_path_flag[j] = 1;
        }  

      
      }

     for(unsigned int j =0; j < circle_path_flag.size(); j++){
         if(circle_path_flag[j]==0){
           temp_path.push_back(Node_Path[i][j]);
         }
     }      
     
     temp_Node_Path.push_back(temp_path);
  }

  Node_Path = temp_Node_Path;
};

/*
void A_star::rm_cycle_path(std::vector<std::vector<int> > &Node_Path){

  compact_path(Node_Path);
  std::vector<std::vector<int> > temp_Node_Path;

  for(int i=0; i<Node_Path.size(); i++){
     std::vector<int> temp_path;

     std::set<int> unit_set;
     std::set<int> cycle_set;
     
     for(int j =0; j < Node_Path[i].size(); j++){
         if(unit_set.find(Node_Path[i][j])==unit_set.end()){
            unit_set.insert(Node_Path[i][j]);
         }else{
            cycle_set.insert(Node_Path[i][j]);
         }
     }
     int cycle_flag = 0;
     int cycle_node = 0;  
     for(int j=0; j < Node_Path[i].size();j++){
        if(cycle_flag==0){
          temp_path.push_back(Node_Path[i][j]);
          if(cycle_set.find(Node_Path[i][j])!=cycle_set.end()){
             cycle_flag = 1;
             cycle_node = Node_Path[i][j];
          }
        }else if(Node_Path[i][j] == cycle_node){
             cycle_flag = 0;
        }
     }
     temp_Node_Path.push_back(temp_path);
  }

  Node_Path = temp_Node_Path;
};
*/
void A_star::lable_father(Grid& grid, std::vector<std::vector<int> > &Node_Path){

  for(unsigned int i =0; i<Node_Path.size();i++){
      grid.vertices_total[Node_Path[i][0]].trace_back_node = -1;
      for(unsigned int j =1;j<Node_Path[i].size();j++){
         //grid.vertices_total[Node_Path[i][j]].parent = Node_Path[i][j-1];
         grid.vertices_total[Node_Path[i][j]].trace_back_node = Node_Path[i][j-1];
      }
  }


};

bool A_star::Check_Path_Extension(Grid& grid, std::vector<std::vector<int> >& node_path, std::set<int> &source_index){

  for(unsigned int i=0;i<node_path.size();i++){
     bool Extendable = Extention_checks(grid, node_path[i], source_index);
     if(!Extendable){
         return false;
       }
  }
  return true;

};


bool A_star::Pre_trace_back(Grid& grid, int current_node, int left, int right, std::set<int> &src_index, std::set<int> &dest_index){

  auto logger = spdlog::default_logger()->clone("router.A_star.Pre_trace_back");

  std::vector<int> temp_path = Trace_Back_Path_parent(grid, current_node, src_index);


  std::vector<std::vector<int> > Node_Path(left+right+1);



  if(src_index.find(current_node)!=src_index.end()){

     return true;

  }

  

  for(unsigned int i=0;i<temp_path.size() - 1; i++){

    std::vector<std::vector<int> > node_L_path;
    int cost = 0;
    parallel_routing(grid, temp_path[i], temp_path[i+1], left, right, src_index, dest_index, node_L_path, cost);

    for(unsigned int j=0;j<Node_Path.size();j++){

       //if(node_L_path.size()==Node_Path.size())
       Node_Path[j].insert(Node_Path[j].end(),node_L_path[j].begin(),node_L_path[j].end());

    }

  }

  logger->debug("Pre trace 1");
  rm_cycle_path(Node_Path);

  logger->debug("Pre trace 1");
  lable_father(grid, Node_Path);

  logger->debug("Pre trace 1");
  //bool extend = 1;
  logger->debug("Check extention 1");

  bool extend = Check_Path_Extension(grid, Node_Path, src_index);
  logger->debug("Check extention 2");

  return extend;
 
};

std::vector<std::vector<int> > A_star::Trace_Back_Paths(Grid& grid, int current_node, int left, int right, std::set<int> &src_index, std::set<int> &dest_index){

  auto logger = spdlog::default_logger()->clone("router.A_star.Trace_Back_Paths");

  std::vector<std::vector<int> > temp_paths;
  std::vector<std::vector<int> > extend_labels;
  int mode = 0;
  std::vector<int> nodes;
  //Pre_trace_back(grid, current_node, left, right, src_index,dest_index);
  int cost = 0;
  bool found = find_succsive_parallel_node(grid, current_node, left, right, mode, nodes, dest_index, cost);
  if(!found){
    logger->error("Trace_Back_Paths bug 1 ");
    assert(0);
  }
  logger->debug("trace back flag3");

  logger->debug("src_index");

  for(auto it=src_index.begin();it!=src_index.end();++it){
      logger->debug("{0}",*it);
  }

  logger->debug("dest_index");

  for(auto it=dest_index.begin();it!=dest_index.end();++it){
      logger->debug("{0}",*it);
  }

  for(unsigned int i=0;i<nodes.size();i++){

     logger->debug("trace back flag3.1");
     logger->debug("trace back node nodes {0} {1} {2} metal {3} i {4} ",nodes[i],grid.vertices_total[nodes[i]].x,grid.vertices_total[nodes[i]].y,grid.vertices_total[nodes[i]].metal,i);
     std::vector<int> temp_path = Trace_Back_Path_trace_back_node(grid, nodes[i], src_index);
     //std::vector<int> temp_path = Trace_Back_Path_parent(grid, nodes[i], src_index);
     if(temp_path.size()<2){
        logger->debug("temp_path size {0} ",temp_path.size());
        logger->debug("Trace_Back_Paths bug 2 ");
        //assert(0);      
     }
     temp_paths.push_back(temp_path);
     std::vector<int> extend_label = extend_manner_direction_check(temp_path,grid);
     extend_labels.push_back(extend_label);
  }
  if(shielding){
    if(temp_paths.size()>2){
      int path_size = int(temp_paths.size()-1);
      std::vector<int> temp_path_l = CovertToShieldingNet(grid, temp_paths[0]);
      std::vector<int> temp_extend_label_l = CovertToShieldingNet(grid, extend_labels[0]);
      extend_labels[0] = temp_extend_label_l;
      temp_paths[0] = temp_path_l;
      std::vector<int> temp_path_r = CovertToShieldingNet(grid, temp_paths[path_size]);
      std::vector<int> temp_extend_label_r = CovertToShieldingNet(grid, extend_labels[path_size]);
      temp_paths[path_size] = temp_path_r;
      extend_labels[path_size] = temp_extend_label_r;
    }
  }
  Extend_labels.clear();
  Extend_labels = extend_labels;
  //std::cout<<"a star temp_path length ";
  //for(int i=0;i<temp_paths.size();i++){
     //std::cout<<temp_paths[i].size()<<" "; 
  //}
  //std::cout<<std::endl;

  //std::cout<<"a star Extend_labels length ";
  //for(int i=0;i<Extend_labels.size();i++){
     //std::cout<<Extend_labels[i].size()<<" "; 
  //}
  //std::cout<<std::endl;


  return temp_paths;

};


std::vector<int> A_star::Trace_Back_Path_parent(Grid& grid, int current_node, std::set<int> &src_index){

  std::vector<int> temp_path;
  //std::set<int> temp_parents;
  temp_path.push_back(current_node);
  int temp_parent = current_node;
  //temp_parents.insert(temp_parent);
  int count = 0;
  //src_index.insert(-1);
  while(src_index.find(temp_parent)==src_index.end()){
  //while(temp_parent!=-1){
      //if(count == 20) assert(0);
      count = count + 1;
      //temp_parents.insert(temp_parent);
      temp_parent = grid.vertices_total[temp_parent].parent;
      temp_path.push_back(temp_parent);
      //temp_parent = grid.vertices_total[temp_parent].parent;
      //temp_parent = grid.vertices_total[temp_parent].parent;
      }

  std::vector<int> reserse_path;
  for(int i=(int)temp_path.size()-1;i>=0;i--){
     reserse_path.push_back(temp_path[i]);
    }
  return reserse_path;

};


std::vector<int> A_star::Trace_Back_Path_trace_back_node(Grid& grid, int current_node, std::set<int> &src_index){

  std::vector<int> temp_path;
  //std::set<int> temp_parents;
  temp_path.push_back(current_node);
  int temp_parent = current_node;
  //temp_parents.insert(temp_parent);
  int count = 0;
  src_index.insert(-1);
  while(src_index.find(temp_parent)==src_index.end()){
  //while(temp_parent!=-1){

      //if(count == 20) assert(0);
      count = count + 1;
      //temp_parents.insert(temp_parent);
      temp_parent = grid.vertices_total[temp_parent].trace_back_node;
      temp_path.push_back(temp_parent);
      //temp_parent = grid.vertices_total[temp_parent].parent;
      //temp_parent = grid.vertices_total[temp_parent].parent;
      }

  std::vector<int> reserse_path;
  for(int i=(int)temp_path.size()-1;i>=0;i--){
     reserse_path.push_back(temp_path[i]);
    }

  
  return reserse_path;

};


std::vector<int> A_star::CovertToShieldingNet(Grid& grid, std::vector<int> &temp_path){

  std::vector<int> temp_shielding_path;
  
  for(int i=1;i<(int)temp_path.size()-1;i++){

       temp_shielding_path.push_back(temp_path[i]);

     }

  //missing L shape remove visually

  return temp_shielding_path;

};

void A_star::refreshGrid(Grid& grid){

  for(int i=0;i<(int)grid.vertices_total.size();i++){
       grid.vertices_total[i].Cost = INT_MAX;
       grid.vertices_total[i].parent = -1;
     }
};

std::vector<std::vector<int>> A_star::GetPath(){
  std::vector<std::vector<int>> path(Path);
  return (path);
}
