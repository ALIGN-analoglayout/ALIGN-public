#include "Graph.h"
#include "spdlog/spdlog.h"
#include "assert.h"

Graph::Graph(Grid& grid):path_number(1) {

  auto logger = spdlog::default_logger()->clone("router.Graph.Graph");

  logger->debug("Start Creating adjacent list (graph)");
  CreateAdjacentList(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  logger->debug("End Creating adjacent list (graph)");

};

Graph::Graph(Grid& grid, bool Power_grid):path_number(1) {

  auto logger = spdlog::default_logger()->clone("router.Graph.Graph");

  this->source=-1; this->dest=-1;
  logger->debug("Start Creating power grid (graph)");
  CreatePower_Grid(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  logger->debug("End creating power grid (graph)");

};

bool Graph::FindFeasiblePath(Grid& grid, int pathNo) {

  auto logger = spdlog::default_logger()->clone("router.Graph.FindFeasiblePath");

  bool mark=false;
  for(int i =0;i<pathNo;++i){
    
     //find one shortest path

     std::vector<int> temp_path;
     logger->debug("start dijkstra");
     temp_path = dijkstra();// grid.Source grid.dest
     logger->debug("end dijkstra");

     if(temp_path.size()>0) {
     //update weight
     UpdateEdgeWeight(temp_path);
     
     //recover path from graph to total
     Path_graph_total(grid,temp_path);

     //return the shortest path
     Path.push_back(temp_path);
     mark=true;
     } else {
       mark=(mark || false);
       logger->warn("Router-Warning: feasible path might not be found");
     }
  }
  return mark;

}

Graph::Graph(Grid& grid, int pathNo) {

  auto logger = spdlog::default_logger()->clone("router.Graph.Graph");

  logger->debug("Start Creating adjacent list (graph),");
  CreateAdjacentList(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  logger->debug("End creating adjacent list (graph)");

  this->path_number=pathNo;
  for(int i =0;i<pathNo;++i){
    
     //find one shortest path

     std::vector<int> temp_path;

     temp_path = dijkstra();// grid.Source grid.dest

     //update weight
     UpdateEdgeWeight(temp_path);
     
     //recover path from graph to total
     Path_graph_total(grid,temp_path);

     //return the shortest path
     Path.push_back(temp_path);

  }


};


void Graph::CreatePower_Grid(Grid& grid){ //grid function needs to be changed..... or 

  std::set<RouterDB::Metal, RouterDB::MetalComp> VddPower_Set;
  std::set<RouterDB::Metal, RouterDB::MetalComp> GndPower_Set;
  std::set<RouterDB::Via, RouterDB::ViaComp> VddVia_Set;
  std::set<RouterDB::Via, RouterDB::ViaComp> GndVia_Set;

  std::set<RouterDB::Metal, RouterDB::MetalComp>::iterator metallowx, metalupx, metalx;
  std::set<RouterDB::Via, RouterDB::ViaComp>::iterator vialowx, viaupx, viax;
  
  RouterDB::Metal temp_metal;
  RouterDB::Via temp_via;
  RouterDB::point LL_point;
  RouterDB::point UR_point;

  //std::cout<<"Connection_Check_Power_Grid 1"<<std::endl;
  Connection_Check_Power_Grid(grid,1); //check vdd
  //std::cout<<"Connection_Check_Power_Grid 2"<<std::endl;
  Connection_Check_Power_Grid(grid,0); //check gnd
  //std::cout<<"Connection_Check_Power_Grid 3"<<std::endl;

  auto adjust_line = [&](auto& graph_index){

       UR_point.x = grid.vertices_graph[graph_index].x;
       UR_point.y = grid.vertices_graph[graph_index].y;
       if(LL_point.x == UR_point.x){
           if(LL_point.y<=UR_point.y){
               temp_metal.LinePoint.push_back(LL_point);
               temp_metal.LinePoint.push_back(UR_point);
             }else{
               temp_metal.LinePoint.push_back(UR_point);
               temp_metal.LinePoint.push_back(LL_point);
             }
       }else{
           if(LL_point.x<=UR_point.x){
               temp_metal.LinePoint.push_back(LL_point);
               temp_metal.LinePoint.push_back(UR_point);
             }else{
               temp_metal.LinePoint.push_back(UR_point);
               temp_metal.LinePoint.push_back(LL_point);
             }
       }
  };

  auto collect_vdd_gnd = [&](auto &i, auto&temp_vector){

       for(unsigned int j=0;j<temp_vector.size();++j) 
          {   
             temp_metal.LinePoint.clear();
             if(grid.total2graph.find(temp_vector[j])!=grid.total2graph.end())
               {
                  int graph_index = grid.total2graph[temp_vector[j]];
                  if(grid.vertices_graph[graph_index].active == 1 && grid.vertices_graph[i].power == 1 && grid.vertices_graph[graph_index].power==1) 
                    {  
                      adjust_line(graph_index);
                      VddPower_Set.insert(temp_metal);
                    }

                  if(grid.vertices_graph[graph_index].active == 1 && grid.vertices_graph[i].power == 0 && grid.vertices_graph[graph_index].power==0) 
                   {  
                      adjust_line(graph_index);
                      GndPower_Set.insert(temp_metal);
                   }
               }
                   
         }

  };

  auto collect_vdd_gnd_via = [&](auto &i, auto& temp_index){

       if(temp_index!=-1)
         {
            if(grid.total2graph.find(temp_index)!=grid.total2graph.end()){
                 int graph_index = grid.total2graph[temp_index];
                 if(grid.vertices_graph[graph_index].active == 1 && grid.vertices_graph[i].power == 1 && grid.vertices_graph[graph_index].power==1 && CheckActive(grid,graph_index) && CheckActive(grid,i)) 
                   { 
                     if(grid.vertices_graph[i].metal<grid.vertices_graph[graph_index].metal){
                        temp_via.model_index = grid.vertices_graph[i].metal;
                       }else{
                        temp_via.model_index = grid.vertices_graph[graph_index].metal;
                       }
                     VddVia_Set.insert(temp_via);
                     //VddPower_Set.insert(temp_metal);
                   }

                 if(grid.vertices_graph[graph_index].active == 1 && grid.vertices_graph[i].power == 0 && grid.vertices_graph[graph_index].power==0 && CheckActive(grid,graph_index) && CheckActive(grid,i)) 
                   { 
                       if(grid.vertices_graph[i].metal<grid.vertices_graph[graph_index].metal){
                        temp_via.model_index = grid.vertices_graph[i].metal;
                       }else{
                        temp_via.model_index = grid.vertices_graph[graph_index].metal;
                       }
                     GndVia_Set.insert(temp_via);
                     //GndPower_Set.insert(temp_metal);
                   }
               }
           }
  };
  
  for(unsigned int i=0;i<grid.vertices_graph.size();++i)
     {
        if(grid.vertices_graph[i].active == 1)
          {

             temp_metal.MetalIdx = grid.vertices_graph[i].metal;
             temp_metal.width = grid.drc_info.Metal_info[grid.vertices_graph[i].metal].width;
             LL_point.x = grid.vertices_graph[i].x;
             LL_point.y = grid.vertices_graph[i].y;
             temp_via.position = LL_point;
             collect_vdd_gnd(i,grid.vertices_graph[i].north);
             collect_vdd_gnd(i,grid.vertices_graph[i].south);
             collect_vdd_gnd(i,grid.vertices_graph[i].east);
             collect_vdd_gnd(i,grid.vertices_graph[i].west);
	     collect_vdd_gnd_via(i,grid.vertices_graph[i].down);
             collect_vdd_gnd_via(i,grid.vertices_graph[i].up);
             //graph.push_back(tempNode); 
          }
     }

  metallowx = VddPower_Set.begin();
  metalupx = VddPower_Set.end();
  for(metalx=metallowx;metalx!=metalupx;++metalx){
     Vdd_grid.metals.push_back(*metalx); 
     }

  metallowx = GndPower_Set.begin();
  metalupx = GndPower_Set.end();
  for(metalx=metallowx;metalx!=metalupx;++metalx){
      Gnd_grid.metals.push_back(*metalx); 
     }

  vialowx = VddVia_Set.begin();
  viaupx = VddVia_Set.end();
  for(viax=vialowx;viax!=viaupx;++viax){
      Vdd_grid.vias.push_back(*viax);
     }

  vialowx = GndVia_Set.begin();
  viaupx = GndVia_Set.end();
  for(viax=vialowx;viax!=viaupx;++viax){
      Gnd_grid.vias.push_back(*viax);
     }

};

void Graph::collect_nodes(Grid &grid, vector<int> temp_vector, vector<int>& adjacent_nodes, int power){

  auto logger = spdlog::default_logger()->clone("router.Graph.collect_nodes");

       for(unsigned int j=0;j<temp_vector.size();++j) 
          {   
             if(grid.total2graph.find(temp_vector[j])!=grid.total2graph.end())
               {
                  int index = grid.total2graph[temp_vector[j]];
                  logger->debug("temp {0} index {1} ",temp_vector[j],index);
                  logger->debug("index edge {0} graph size {1} temp_vector[j] {2} ", index,grid.vertices_graph.size(),temp_vector[j]);
                  if( index<grid.vertices_graph.size() && index>=0 && grid.vertices_graph[index].active && grid.vertices_graph[index].power == power && grid.vertices_graph[index].graph_index==-1) 
                    {  
                      adjacent_nodes.push_back(index);
                    }
               }
                   
         }
};

void Graph::collect_node(Grid &grid, int temp_vector, vector<int>& adjacent_nodes, int power){
   
             if(grid.total2graph.find(temp_vector)!=grid.total2graph.end())
               {
                  int index = grid.total2graph[temp_vector];
                  if( index<grid.vertices_graph.size() && index>=0 && grid.vertices_graph[index].active && grid.vertices_graph[index].power == power && grid.vertices_graph[index].graph_index==-1) 
                    {  
                      adjacent_nodes.push_back(index);
                    }
               }

};

void Graph::power_grid_dsf(Grid& grid, int i, int graph_index, int& connection_graph_number, int power){

  if(i<0 || i>grid.vertices_graph.size()-1){
     return;
  }

  //std::cout<<"power_grid_dsf checkpoint 1"<<std::endl;

  //std::cout<<"i "<<i<<" "<<grid.vertices_graph.size()<<std::endl;

  grid.vertices_graph[i].graph_index = graph_index;

  connection_graph_number++;

  std::vector<int> adjacent_nodes;

  /*
  auto collect_nodes = [&](auto&temp_vector){

       for(unsigned int j=0;j<temp_vector.size();++j) 
          {   
             if(grid.total2graph.find(temp_vector[j])!=grid.total2graph.end())
               {
                  int index = grid.total2graph[temp_vector[j]];
                  //std::cout<<"temp "<<temp_vector[j]<<"index"<<index<<std::endl;
                  std::cout<<"index edge "<<index<<" graph size "<<grid.vertices_graph.size()<<" temp_vector[j] "<<temp_vector[j]<<std::endl;
                  if( index<grid.vertices_graph.size() && index>=0 && grid.vertices_graph[index].active && grid.vertices_graph[index].power == power && grid.vertices_graph[index].graph_index==-1) 
                    {  
                      adjacent_nodes.push_back(index);
                    }
               }
                   
         }

  };

  auto collect_node = [&](auto&temp_vector){
  
             if(grid.total2graph.find(temp_vector)!=grid.total2graph.end())
               {
                  int index = grid.total2graph[temp_vector];
                  //std::cout<<"temp down/up"<<temp_vector<<"index"<<index<<std::endl;
                  std::cout<<"index via "<<index<<" graph size "<<grid.vertices_graph.size()<<std::endl;
                  if( index<grid.vertices_graph.size() && index>=0 && grid.vertices_graph[index].active && grid.vertices_graph[index].power == power && grid.vertices_graph[index].graph_index==-1) 
                    {  
                      adjacent_nodes.push_back(index);
                    }
               }
                   
  };
  */

  //std::cout<<"power_grid_dsf checkpoint 2"<<std::endl;
  //std::cout<<"north"<<std::endl;
  //std::cout<<"north size "<<grid.vertices_graph[i].north.size()<<std::endl;
  collect_nodes(grid,grid.vertices_graph[i].north,adjacent_nodes,power);

  //std::cout<<"power_grid_dsf checkpoint 3"<<std::endl;
  //std::cout<<"south"<<std::endl;
  //std::cout<<"south size "<<grid.vertices_graph[i].south.size()<<std::endl;  
  collect_nodes(grid,grid.vertices_graph[i].south,adjacent_nodes,power);

  //std::cout<<"power_grid_dsf checkpoint 4"<<std::endl;
  //std::cout<<"east"<<std::endl;
  //std::cout<<"east size "<<grid.vertices_graph[i].east.size()<<std::endl;
  collect_nodes(grid,grid.vertices_graph[i].east,adjacent_nodes,power);

  //std::cout<<"power_grid_dsf checkpoint 5"<<std::endl;
  //std::cout<<"west"<<std::endl;
  //std::cout<<"west size "<<grid.vertices_graph[i].west.size()<<std::endl;
  collect_nodes(grid,grid.vertices_graph[i].west,adjacent_nodes,power);

  //std::cout<<"power_grid_dsf checkpoint 6"<<std::endl;
  //std::cout<<"up"<<std::endl;
  //std::cout<<"up size "<<grid.vertices_graph[i].up<<std::endl;
  collect_node(grid,grid.vertices_graph[i].up,adjacent_nodes,power);

  //std::cout<<"power_grid_dsf checkpoint 7"<<std::endl;
  //std::cout<<"down"<<std::endl;
  //std::cout<<"down size "<<grid.vertices_graph[i].down<<std::endl;
  collect_node(grid,grid.vertices_graph[i].down,adjacent_nodes,power);

  //std::cout<<"power_grid_dsf checkpoint 8"<<std::endl;

  //std::cout<<"power_grid_dsf checkpoint 8.5"<<std::endl;

  for(unsigned int j=0;j<adjacent_nodes.size();++j){

     //std::cout<<"power_grid_dsf checkpoint 8.6"<<std::endl;

     power_grid_dsf(grid,adjacent_nodes[j],graph_index,connection_graph_number,power);

  }

 //std::cout<<"power_grid_dsf checkpoint 9"<<std::endl;
  
};


void Graph::Connection_Check_Power_Grid(Grid& grid, int power){

  std::vector<int> number_connection_graph;
  int graph_index = 0;

  //std::cout<<"Connection_Check_Power_Grid checkpoint1"<<std::endl;
  for(unsigned int i=0;i<grid.vertices_graph.size();++i){
      
      if(grid.vertices_graph[i].graph_index==-1 && grid.vertices_graph[i].power==power && grid.vertices_graph[i].active){
          int connection_graph_number = 0;
          //std::cout<<"start dsf"<<std::endl;
          power_grid_dsf(grid,i,graph_index,connection_graph_number,power);
          //std::cout<<"end dsf"<<std::endl;
          graph_index++;
          number_connection_graph.push_back(connection_graph_number);
        }

  }
  //std::cout<<"Connection_Check_Power_Grid checkpoint2"<<std::endl;
  int max_index = -1;
  int max_number = -1;

  for(unsigned int i=0;i<number_connection_graph.size();++i){
     
      if(number_connection_graph[i]>max_number){
         max_number = number_connection_graph[i];
         max_index = i;
       }

  }
  //std::cout<<"Connection_Check_Power_Grid checkpoint3"<<std::endl;

  //std::cout<<"max_index "<<max_index<<" max number "<<number_connection_graph[max_index]<<std::endl;
  //assert(0);

  for(unsigned int i=0;i<grid.vertices_graph.size();++i){

      if(grid.vertices_graph[i].power==power && grid.vertices_graph[i].graph_index!=max_index){
          grid.vertices_graph[i].active = false;
        }

  }
  //std::cout<<"Connection_Check_Power_Grid checkpoint4"<<std::endl;
};

bool Graph::CheckActive(Grid& grid, int index){

  bool found = false;

  auto check_one_direction = [&](auto&temp_vector){

       for(unsigned int j=0;j<temp_vector.size();++j) 
          {   
          
             if(grid.total2graph.find(temp_vector[j])!=grid.total2graph.end())
               {
                  int graph_index = grid.total2graph[temp_vector[j]];
                  if(graph_index>=0 && graph_index< grid.vertices_graph.size() && grid.vertices_graph[graph_index].active == 1) 
                    {  
                       found = true;
                    }
               }
                   
         }

  };

  check_one_direction(grid.vertices_graph[index].north);
  check_one_direction(grid.vertices_graph[index].south);
  check_one_direction(grid.vertices_graph[index].east);
  check_one_direction(grid.vertices_graph[index].west);

  if(found==false){
     //std::cout<<"Power Via Bug "<<found<<std::endl;
    }else{
     //std::cout<<"Power Via Bug "<<found<<std::endl;
    }

  return found;

};


Graph::Graph(std::vector<std::pair<int,int> > &global_path, std::vector<std::vector<int> > &conectedTile, std::vector<int> &Tile_Source, std::vector<int> &Tile_Dest):path_number(1){

  std::map<int,int> tile_graph_map;
  std::map<int,int> graph_tile_map;
  CreateAdjacentList_Global_Path(global_path,conectedTile,Tile_Source,Tile_Dest,tile_graph_map,graph_tile_map); //create adjacentList base gird.LL_graph and gird.UR_graph
  std::vector<int> temp_path = dijkstra();
  std::vector<int> global_path_return;
  
  for(unsigned int i=0;i<temp_path.size();++i){

     global_path_return.push_back(graph_tile_map[temp_path[i]]);

  }

  Path.push_back(global_path_return); 

};


void Graph::CreateAdjacentList_Global_Path(std::vector<std::pair<int,int> > &global_path, std::vector<std::vector<int> > &conectedTile, std::vector<int> &Tile_Source, std::vector<int> &Tile_Dest,   std::map<int,int> &tile_graph_map,std::map<int,int> &graph_tile_map){

  std::set<int> temp_set;
  
  for(unsigned int i=0;i<global_path.size();++i){
     temp_set.insert(global_path[i].first);
     temp_set.insert(global_path[i].second);
  }

  for(unsigned int i=0;i<conectedTile.size();++i){
     for(unsigned int j=0;j<conectedTile[i].size();++j){
        temp_set.insert(conectedTile[i][j]);
     }
  }

  std::set<int>::iterator it,it_low,it_up;

  int tile_index = 0; 

  for(it=temp_set.begin();it!=temp_set.end();++it){
  
     tile_graph_map[*it] = tile_index;
     graph_tile_map[tile_index] = *it;
     tile_index = tile_index + 1;
     Node tempNode;
     tempNode.src = *it;
     graph.push_back(tempNode);

  }

  for(unsigned int i=0;i<global_path.size();++i){

     Edge tempEdge;
     int start_index = tile_graph_map[global_path[i].first];
     int end_index = tile_graph_map[global_path[i].second];
     bool found = false;
     if(start_index!=end_index){
        for(unsigned int j=0;j<graph[start_index].list.size();++j){
           if(graph[start_index].list[j].dest==end_index){
              found = true;
              break;
           }
        }
        if(found==false){
           tempEdge.dest = end_index;
           tempEdge.weight = 1;
           graph[start_index].list.push_back(tempEdge);
           tempEdge.dest = start_index;
           graph[end_index].list.push_back(tempEdge);
        }         
      }
  }

  for(unsigned int i=0;i<conectedTile.size();++i){

     for(unsigned int j=0;j<conectedTile[i].size()-1;++j){

        Edge tempEdge;
        int start_index = tile_graph_map[conectedTile[i][j]];
        int end_index = tile_graph_map[conectedTile[i][j+1]];

        bool found = false;
        if(start_index!=end_index){
          for(unsigned int j=0;j<graph[start_index].list.size();++j){
             if(graph[start_index].list[j].dest==end_index){
                found = true;
                break;
             }
          }
          if(found==false){
             tempEdge.dest = end_index;
             tempEdge.weight = 1;
             graph[start_index].list.push_back(tempEdge);
             tempEdge.dest = start_index;
             graph[end_index].list.push_back(tempEdge);
          }         
        }
     }
  }

  source = graph.size();
  dest = source + 1;
     
  Node tempNodeS;
  tempNodeS.src = source;
     
  for(unsigned int i=0;i<Tile_Source.size();++i)
     {
          
        Edge tempEdge;
        int graph_index = tile_graph_map[Tile_Source[i]];
        tempEdge.dest = graph_index;
        tempEdge.weight = 1;
        tempNodeS.list.push_back(tempEdge);
        tempEdge.dest = source;
        graph[graph_index].list.push_back(tempEdge);

     }
  graph.push_back(tempNodeS);

  Node tempNodeD;
  tempNodeD.src = dest;
     
  for(unsigned int i=0;i<Tile_Dest.size();++i)
     {
       
        Edge tempEdge;
        int graph_index = tile_graph_map[Tile_Dest[i]];
        tempEdge.dest = graph_index;
        tempEdge.weight = 1;
        tempNodeD.list.push_back(tempEdge);
        tempEdge.dest = dest;
        graph[graph_index].list.push_back(tempEdge);

     }
   graph.push_back(tempNodeD);

};



void Graph::CreateAdjacentList(Grid& grid){

  for(unsigned int i=0;i<grid.vertices_graph.size();++i)
     {
        if(grid.vertices_graph[i].active == 1)
          {
             Node tempNode;
             tempNode.src=i;
             Edge tempEdge;

	     auto fx = [&](RouterDB::vertex& u, RouterDB::vertex& v) {
	       return (double) abs(v.x-u.x)*grid.drc_info.metal_weight[u.metal];
	     };
	     auto fy = [&](RouterDB::vertex& u, RouterDB::vertex& v) {
	       return (double) abs(v.y-u.y)*grid.drc_info.metal_weight[u.metal];
	     };
	     auto f1 = [&](RouterDB::vertex& u, RouterDB::vertex& v) {
	       return (double) 1.0;
	     };

	     auto process = [&](RouterDB::vertex& u, int index, auto f) {
	       auto it = grid.total2graph.find(index);
	       if(it!=grid.total2graph.end())
		 {
		   int graph_index = it->second;
		   auto v = grid.vertices_graph[graph_index];
		   if(v.active == 1) 
		     {  
		       tempEdge.dest=graph_index;
		       tempEdge.weight = f( u, v);
		       tempNode.list.push_back(tempEdge);	
		     }
		 }
	     };

             for(unsigned int j=0;j<grid.vertices_graph[i].north.size();++j) 
	       process( grid.vertices_graph[i], grid.vertices_graph[i].north[j], fy);

             for(unsigned int j=0;j<grid.vertices_graph[i].south.size();++j) 
	       process( grid.vertices_graph[i], grid.vertices_graph[i].south[j], fy);

             for(unsigned int j=0;j<grid.vertices_graph[i].east.size();++j) 
	       process( grid.vertices_graph[i], grid.vertices_graph[i].east[j], fx);

             for(unsigned int j=0;j<grid.vertices_graph[i].west.size();++j) 
	       process( grid.vertices_graph[i], grid.vertices_graph[i].west[j], fx);
 	
             if(grid.vertices_graph[i].down!=-1)
	       process( grid.vertices_graph[i], grid.vertices_graph[i].down, f1);

             if(grid.vertices_graph[i].up!=-1)
	       process( grid.vertices_graph[i], grid.vertices_graph[i].up, f1);

             graph.push_back(tempNode); 
          }
     }

  //Dummy node for source
  source = graph.size();
  dest = source + 1;
     
  Node tempNodeS;
  tempNodeS.src = source;
     
  for(unsigned int i=0;i<grid.Source.size();++i)
     {
       if(grid.total2graph.find(grid.Source[i])!=grid.total2graph.end()){
           int graph_index = grid.total2graph[grid.Source[i]];
           Edge tempEdge;
           tempEdge.dest = graph_index;
           tempEdge.weight = 1;
           tempNodeS.list.push_back(tempEdge);
           tempEdge.dest = source;
           graph[graph_index].list.push_back(tempEdge);
           //std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
         }
     }
  graph.push_back(tempNodeS);

  Node tempNodeD;
  tempNodeD.src = dest;
     
  for(unsigned int i=0;i<grid.Dest.size();++i)
     {
       if(grid.total2graph.find(grid.Dest[i])!=grid.total2graph.end()){
           int graph_index = grid.total2graph[grid.Dest[i]];
           Edge tempEdge;
           tempEdge.dest = graph_index;
           tempEdge.weight = 1;
           tempNodeD.list.push_back(tempEdge);
           tempEdge.dest = dest;
           graph[graph_index].list.push_back(tempEdge);
           //std::cout<<"graph D "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
         }
     }
   graph.push_back(tempNodeD);

};

void Graph::RemovefromMultMap(std::multimap<double, int>& mmap, double dist, int idx) {
  auto logger = spdlog::default_logger()->clone("router.Graph.RemovefromMultMap");

  std::multimap<double, int>::iterator low=mmap.lower_bound(dist);
  std::multimap<double, int>::iterator high=mmap.upper_bound(dist);
  std::multimap<double, int>::iterator tar;
  bool mark=false;
  //  unsigned int count=0;
  for(tar=low; tar!=high; ++tar) {
    //    ++count;
    if(tar->second==idx) {mark=true; break;}
  }
  if(mark) {mmap.erase(tar);}
  else {logger->debug("Graph-Info: cannot found element in map");}
  //  std::cout << "RemovefromMultMap: searched through " << count << " multmap nodes." << std::endl;
}

void Graph::UpdateMultMap(std::multimap<double, int>& mmap, double olddist, int idx, double newdist) {
  this->RemovefromMultMap(mmap, olddist, idx);
  mmap.insert(std::pair<double, int>(newdist, idx));
}

std::vector<int> Graph::minDistancefromMultiMap(std::multimap<double, int> &mmap)
{
  std::vector<int> min_index;
  std::multimap<double, int>::iterator miter=mmap.begin();
  double min = miter->first;
  std::multimap<double, int>::iterator low=mmap.lower_bound(min);
  std::multimap<double, int>::iterator high=mmap.upper_bound(min);
  for(std::multimap<double, int>::iterator it=low; it!=high; ++it) {
    min_index.push_back(it->second);
    break; // only using the first later on, so we will stop early
  }
  return min_index; // Has zero or one entry.
};

std::vector<int>  Graph::dijkstra(){

  std::vector<int> temp_path;

 

  std::vector<double> dist;
  dist.resize(graph.size());
  //double dist[graph.size()];

  std::vector<int> parent;
  parent.resize(graph.size());
  //int parent[graph.size()];


  std::vector<int> status;
  status.resize(graph.size());
  //int status[graph.size()];


  std::multimap<double, int> distMap;
    
  for(unsigned int i = 0; i < graph.size(); ++i)
     {
        parent[i] = -1;
        dist[i] = INT_MAX;
        status[i] = 0;
     }

  dist[source] = 0;
  status[source] = 1;
  distMap.insert ( std::pair<double,int>(dist[source], source) );
  int count=0;
  int v;
  //std::cout<<"graph source "<<source<<" vs graph dest "<<dest<<std::endl;
  while(status[dest]!=2 && count<(int)graph.size()-1)
       {
          std::vector<int> ulist = minDistancefromMultiMap (distMap);
          //std::cout<<"size of Q: "<<ulist.size()<<std::endl;
          if(ulist.empty()) {temp_path.clear(); return temp_path;}
          int u=ulist[0];
          RemovefromMultMap(distMap, dist[u], u);
          //std::cout<<"check u: "<<u<<" x: "<<grid.vertices_graph[u].x<<" y: "<<grid.vertices_graph[u].y <<std::endl;
          status[u] = 2;
          
          for (unsigned int j = 0; j < graph[u].list.size(); ++j)
              {
                 v=graph[u].list[j].dest;
                 if(v!=u)
                   {
                      if(status[v]==0)
                        {
                           parent[v] = u;
                           dist[v] = dist[u]+graph[u].list[j].weight;
                           status[v]=1;
                           distMap.insert( std::pair<double,int>(dist[v], v) );
                         }
                      else if (status[v]==1 && dist[v]>dist[u]+graph[u].list[j].weight)
                         {
                            parent[v] = u;
                            double olddist=dist[v];
                            dist[v] = dist[u]+graph[u].list[j].weight;
                            UpdateMultMap(distMap, olddist, v, dist[v]);
                         }
                    }
               }
          count++;
       }

  printPath(parent, dest, graph.size(), temp_path);
  //std::cout<<"temp path"<<std::endl;
  //for(int i=0;i<temp_path.size();i++) {std::cout<<temp_path[i]<<" "<<std::endl;}
  return temp_path;

};

std::vector<int>  Graph::dijkstraRetire(Grid& grid){

  std::vector<int> temp_path;

 

  std::vector<double> dist;
  dist.resize(graph.size());
  //double dist[graph.size()];


  std::vector<int> parent;
  parent.resize(graph.size());
  //int parent[graph.size()];


  std::vector<int> status;
  status.resize(graph.size());
  //int status[graph.size()];



  for(unsigned int i = 0; i < graph.size(); ++i)
     {
        parent[i] = -1;
        dist[i] = INT_MAX;
        status[i] = 0;
     }


  dist[source] = 0;
  status[source] = 1;

  int count=0;
  int v;
  //std::cout<<"graph source "<<source<<" vs graph dest "<<dest<<std::endl;
  while(status[dest]!=2 && count<(int)graph.size()-1)
       {
          std::vector<int> ulist = minDistance(dist, status, graph.size());
          //std::cout<<"size of Q: "<<ulist.size()<<std::endl;
          if(ulist.empty()) {temp_path.clear(); return temp_path;}
          int u=ulist[0];
          //std::cout<<"check u: "<<u<<" x: "<<grid.vertices_graph[u].x<<" y: "<<grid.vertices_graph[u].y <<std::endl;
          status[u] = 2;
          
          for (unsigned int j = 0; j < graph[u].list.size(); ++j)
              {
                 v=graph[u].list[j].dest;
                 if(v!=u)
                   {
                      if(status[v]==0)
                        {
                           parent[v] = u;
                           dist[v] = dist[u]+graph[u].list[j].weight;
                           status[v]=1;
                         }
                      else if (status[v]==1 && dist[v]>dist[u]+graph[u].list[j].weight)
                         {
                            parent[v] = u;
                            dist[v] = dist[u]+graph[u].list[j].weight;
                         }
                    }
               }
          count++;
       }


  printPath(parent, dest, graph.size(), temp_path);

  //std::cout<<"temp path"<<std::endl;
  //for(int i=0;i<temp_path.size();i++) {std::cout<<temp_path[i]<<" "<<std::endl;}
  return temp_path;

};

void Graph::printPath(std::vector<int> &parent, int j, int Vsize, std::vector<int> & temp_path)
{
  if(j == -1)
    {
      return;
    }
  printPath(parent, parent[j], Vsize, temp_path);
  if( !(j==source || j==dest))
    { 
       temp_path.push_back(j);
       //std::cout<<"path push "<<j<<std::endl;
    }
}

std::vector<int> Graph::minDistance(std::vector<double> &dist, std::vector<int> &status, int V)
{
  double min = INT_MAX;
  std::vector<int> min_index;
  for(int v = 0; v < V; ++v) 
     {
        if(status[v] == 1)//only fringe node
          {
             if(dist[v]<min) 
               {
            	  min=dist[v];
            	  min_index.clear();
            	  min_index.push_back(v);
               }
               else if (dist[v]==min) 
               {
            	  min_index.push_back(v);
               }
          }
     }

  return min_index;
};

void Graph::UpdateEdgeWeight(std::vector<int>& path){
  
  int alpha = 2;

  //based on path update edgeweight in graph
  for(int i=0;i<(int)path.size()-1;++i){
    for(unsigned int j=0;j<graph[path[i]].list.size();++j){
      if(graph[path[i]].list[j].dest == path.at(i+1)){
	graph[path[i]].list[j].weight = alpha * graph[path[i]].list[j].weight;
      }
    } 
  }

  //SMB fix out of range error
  for(int i=(int)path.size()-1;i>0;i--){
    for(unsigned int j=0;j<graph[path[i]].list.size();++j){
      if(graph[path[i]].list[j].dest == path.at(i-1)){
	graph[path[i]].list[j].weight = alpha * graph[path[i]].list[j].weight;
      }
    } 
  }

};

void Graph::Path_graph_total(Grid& grid, std::vector<int> &temp_path){

  for(unsigned int i=0; i<temp_path.size(); ++i){
        temp_path[i] = grid.vertices_graph[temp_path[i]].index;
     }

};

std::vector<std::vector<int> > Graph::GetShorestPath(){

  return Path;

};

std::vector<std::vector<RouterDB::Metal> >  Graph::ConvertPathintoPhysical(Grid& grid){

  std::vector<std::vector<RouterDB::Metal> > Phsical_Path;
  for(unsigned int i= 0; i<Path.size();++i){
      std::vector<RouterDB::Metal> temp_physical_path;
      //int start_index = 0;
      //int end_index = 0;
      int flag_start_write = 1;
      //int flag_end_write = 0;
      RouterDB::point temp_point;
      RouterDB::Metal temp_metal;
      for(unsigned int j=0;j<Path[i].size();++j){
          if(flag_start_write == 1){
              temp_metal.LinePoint.clear();
              temp_metal.MetalIdx = grid.vertices_total[Path[i][j]].metal;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              flag_start_write = 0;
            }
 	  if(j+1<Path[i].size() && grid.vertices_total[Path[i][j]].metal!=grid.vertices_total[Path[i][j+1]].metal){
              flag_start_write = 1;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              temp_metal.width = grid.drc_info.Metal_info[grid.vertices_total[Path[i][j]].metal].width;
              temp_physical_path.push_back(temp_metal);
            }
	  if(j+1==Path[i].size() && flag_start_write == 0){

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
