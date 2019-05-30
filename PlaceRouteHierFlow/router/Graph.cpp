#include "Graph.h"

Graph::Graph(Grid& grid) {
  //this->grid=grid; 
  //std::cout<<"~~~~~Before list \n";
  //this->grid.CheckVerticesTotal();
  //use grid information to create adjacentlist
  this->path_number=1;
  std::cout<<"Start Creating adjacent list (graph), ";
  CreateAdjacentList(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  std::cout<<"End creating adjacent list (graph)"<<std::endl;
  //std::cout<<"~~~~~After list \n";
  //this->grid.CheckVerticesTotal();
};

Graph::Graph(Grid& grid, bool Power_grid){
  //this->grid=grid; 
  //std::cout<<"~~~~~Before list \n";
  //this->grid.CheckVerticesTotal();
  //use grid information to create adjacentlist
  this->path_number=1;
  std::cout<<"Start Creating power grid (graph), ";
  CreatePower_Grid(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  std::cout<<"End creating power grid (graph)"<<std::endl;
  //std::cout<<"~~~~~After list \n";
  //this->grid.CheckVerticesTotal();
};

bool Graph::FindFeasiblePath(Grid& grid, int pathNo) {
  bool mark=false;
  for(int i =0;i<pathNo;++i){
    
     std::cout<<"Path No "<<pathNo<<" current path index "<<i<<std::endl;
     //find one shortest path

     std::vector<int> temp_path;
     
     std::cout<<"start dijkstra, "<<std::endl;

     temp_path = dijkstra(grid);// grid.Source grid.dest
     
     std::cout<<"end dijkstra"<<std::endl; 
     if(temp_path.size()>0) {
     //update weight
     UpdateEdgeWeight(temp_path);
     
     //recover path from graph to total
     Path_graph_total(grid,temp_path);

     //return the shortest path
     Path.push_back(temp_path);
     mark=true;
     } else {
       mark=(mark or false);
       std::cout<<"Router-Warning: feasible path might not be found\n";
     }
  }
  return mark;

}

Graph::Graph(Grid& grid, int pathNo) {
  //this->grid=grid; 
  //std::cout<<"~~~~~Before list \n";
  //this->grid.CheckVerticesTotal();
  //use grid information to create adjacentlist
  std::cout<<"Start Creating adjacent list (graph), ";
  CreateAdjacentList(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  std::cout<<"End creating adjacent list (graph)"<<std::endl;
  //std::cout<<"~~~~~After list \n";
  //this->grid.CheckVerticesTotal();
  //find shortest path based source and dest
  this->path_number=pathNo;
  for(int i =0;i<pathNo;++i){
    
     std::cout<<"Path No "<<pathNo<<" current path index "<<i<<std::endl;
     //find one shortest path

     std::vector<int> temp_path;
     
     std::cout<<"start dijkstra, "<<std::endl;

     temp_path = dijkstra(grid);// grid.Source grid.dest

     std::cout<<"end dijkstra"<<std::endl; 
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
  
  for(int i=0;i<grid.vertices_graph.size();++i)
     {
        if(grid.vertices_graph[i].active == 1)
          {
             //Node tempNode;
             //tempNode.src=i;
             //Edge tempEdge;
             temp_metal.MetalIdx = grid.vertices_graph[i].metal;
             temp_metal.width = grid.drc_info.Metal_info[grid.vertices_graph[i].metal].width;
             LL_point.x = grid.vertices_graph[i].x;
             LL_point.y = grid.vertices_graph[i].y;
             temp_via.position = LL_point;

             for(int j=0;j<grid.vertices_graph[i].north.size();++j) 
                {   
                   temp_metal.LinePoint.clear();
                   if(grid.total2graph.find(grid.vertices_graph[i].north[j])!=grid.total2graph.end())
                     {
                       int graph_index = grid.total2graph[grid.vertices_graph[i].north[j]];
                       if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 1 and grid.vertices_graph[graph_index].power==1) 
                          {  
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
                            VddPower_Set.insert(temp_metal);
                           }

                          if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 0 and grid.vertices_graph[graph_index].power==0) 
                          {  
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
                            GndPower_Set.insert(temp_metal);
                           }
                      }
                   
                }

             for(int j=0;j<grid.vertices_graph[i].south.size();++j) 
                {   
                   temp_metal.LinePoint.clear();
                   if(grid.total2graph.find(grid.vertices_graph[i].south[j])!=grid.total2graph.end())
                     {
                       int graph_index = grid.total2graph[grid.vertices_graph[i].south[j]];
                       if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 1 and grid.vertices_graph[graph_index].power==1) 
                          {  
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
                            VddPower_Set.insert(temp_metal);
                           }

                          if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 0 and grid.vertices_graph[graph_index].power==0) 
                          {  
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
                            GndPower_Set.insert(temp_metal);
                           }
                      }
                   
                }
             

             for(int j=0;j<grid.vertices_graph[i].east.size();++j) 
                {   
                   temp_metal.LinePoint.clear();
                   if(grid.total2graph.find(grid.vertices_graph[i].east[j])!=grid.total2graph.end())
                     {
                       int graph_index = grid.total2graph[grid.vertices_graph[i].east[j]];
                       if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 1 and grid.vertices_graph[graph_index].power==1) 
                          {  
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
                            VddPower_Set.insert(temp_metal);
                           }

                          if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 0 and grid.vertices_graph[graph_index].power==0) 
                          {  
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
                            GndPower_Set.insert(temp_metal);
                           }
                      }
                   
                }

             for(int j=0;j<grid.vertices_graph[i].west.size();++j) 
                {   
                   temp_metal.LinePoint.clear();
                   if(grid.total2graph.find(grid.vertices_graph[i].west[j])!=grid.total2graph.end())
                     {
                       int graph_index = grid.total2graph[grid.vertices_graph[i].west[j]];
                       if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 1 and grid.vertices_graph[graph_index].power==1) 
                          {  
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
                            VddPower_Set.insert(temp_metal);
                           }

                          if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 0 and grid.vertices_graph[graph_index].power==0) 
                          {  
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
                            GndPower_Set.insert(temp_metal);
                           }
                      }
                   
                }

 	
             if(grid.vertices_graph[i].down!=-1)
               {  
                  if(grid.total2graph.find(grid.vertices_graph[i].down)!=grid.total2graph.end()){
                      int graph_index = grid.total2graph[grid.vertices_graph[i].down];
                      if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 1 and grid.vertices_graph[graph_index].power==1) 
                          { 
                            temp_via.model_index = grid.vertices_graph[graph_index].metal;
                            VddVia_Set.insert(temp_via);
                            //VddPower_Set.insert(temp_metal);
                           }

                          if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 0 and grid.vertices_graph[graph_index].power==0) 
                          { 
                            temp_via.model_index = grid.vertices_graph[graph_index].metal; 
                            GndVia_Set.insert(temp_via);
                            //GndPower_Set.insert(temp_metal);
                           }
                    }
                }

             if(grid.vertices_graph[i].up!=-1)
               {
                  if(grid.total2graph.find(grid.vertices_graph[i].up)!=grid.total2graph.end()){
                        int graph_index = grid.total2graph[grid.vertices_graph[i].up];
                        if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 1 and grid.vertices_graph[graph_index].power==1) 
                          { 
                            temp_via.model_index = grid.vertices_graph[i].metal;
                            VddVia_Set.insert(temp_via);
                            //VddPower_Set.insert(temp_metal);
                           }

                          if(grid.vertices_graph[graph_index].active == 1 and grid.vertices_graph[i].power == 0 and grid.vertices_graph[graph_index].power==0) 
                          { 
                            temp_via.model_index = grid.vertices_graph[i].metal; 
                            GndVia_Set.insert(temp_via);
                            //GndPower_Set.insert(temp_metal);
                           }
                     }
                }
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

void Graph::CreateAdjacentList(Grid& grid){

  for(int i=0;i<grid.vertices_graph.size();++i)
     {
        if(grid.vertices_graph[i].active == 1)
          {
             Node tempNode;
             tempNode.src=i;
             Edge tempEdge;

             for(int j=0;j<grid.vertices_graph[i].north.size();++j) 
                {  	
                   if(grid.total2graph.find(grid.vertices_graph[i].north[j])!=grid.total2graph.end())
                     {
                       int graph_index = grid.total2graph[grid.vertices_graph[i].north[j]];
                       if(grid.vertices_graph[graph_index].active == 1) 
                          {  
                             tempEdge.dest=graph_index;
                             tempEdge.weight = (double) abs(grid.vertices_graph[graph_index].y-grid.vertices_graph[i].y)*grid.drc_info.metal_weight[grid.vertices_graph[i].metal];
                             tempNode.list.push_back(tempEdge);	
                           }
                      }
                   
                }
             

             for(int j=0;j<grid.vertices_graph[i].south.size();++j) 
                {  	
                   if(grid.total2graph.find(grid.vertices_graph[i].south[j])!=grid.total2graph.end())
                     {
                        int graph_index = grid.total2graph[grid.vertices_graph[i].south[j]];
                        if(grid.vertices_graph[graph_index].active == 1) 
                          {	
                             tempEdge.dest=graph_index;
                             tempEdge.weight = (double) abs(grid.vertices_graph[graph_index].y-grid.vertices_graph[i].y)*grid.drc_info.metal_weight[grid.vertices_graph[i].metal];
                             tempNode.list.push_back(tempEdge);	
                          }
                      }
                   
                 }

             for(int j=0;j<grid.vertices_graph[i].east.size();++j) 
                {  	
                   if(grid.total2graph.find(grid.vertices_graph[i].east[j])!=grid.total2graph.end())
                     {
                        int graph_index = grid.total2graph[grid.vertices_graph[i].east[j]];
                        if(grid.vertices_graph[graph_index].active == 1) 
                          {	
                             tempEdge.dest=graph_index;
                             tempEdge.weight = (double) abs(grid.vertices_graph[graph_index].x-grid.vertices_graph[i].x)*grid.drc_info.metal_weight[grid.vertices_graph[i].metal];
                             tempNode.list.push_back(tempEdge);	
                          }
                      }
                   
                 }

             for(int j=0;j<grid.vertices_graph[i].west.size();++j) 
                {  	
                   if(grid.total2graph.find(grid.vertices_graph[i].west[j])!=grid.total2graph.end())
                     {
                        int graph_index = grid.total2graph[grid.vertices_graph[i].west[j]];
                        if(grid.vertices_graph[graph_index].active == 1) 
                          {	
                             tempEdge.dest=graph_index;
                             tempEdge.weight = (double) abs(grid.vertices_graph[graph_index].x-grid.vertices_graph[i].x)*grid.drc_info.metal_weight[grid.vertices_graph[i].metal];
                             tempNode.list.push_back(tempEdge);	
                          }
                      }
                   
                 }

 	
             if(grid.vertices_graph[i].down!=-1)
               {  
                  if(grid.total2graph.find(grid.vertices_graph[i].down)!=grid.total2graph.end()){
                      int graph_index = grid.total2graph[grid.vertices_graph[i].down];
                      if(grid.vertices_graph[graph_index].active == 1) 
                        {	
                          tempEdge.dest=graph_index;
                          tempEdge.weight = (double) 1;
                          tempNode.list.push_back(tempEdge);	
                        }
                    }
                }

             if(grid.vertices_graph[i].up!=-1)
               {
                  if(grid.total2graph.find(grid.vertices_graph[i].up)!=grid.total2graph.end()){
                        int graph_index = grid.total2graph[grid.vertices_graph[i].up];
                        if(grid.vertices_graph[graph_index].active == 1) 
                          {	
                            tempEdge.dest=graph_index;
                            tempEdge.weight = (double) 1;
                            tempNode.list.push_back(tempEdge);	
                          }
                     }
                }
             graph.push_back(tempNode); 
          }
     }

  //Dummy node for source
  source = graph.size();
  dest = source + 1;
     
  Node tempNodeS;
  tempNodeS.src = source;
     
  for(int i=0;i<grid.Source.size();++i)
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
     
  for(int i=0;i<grid.Dest.size();++i)
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

std::vector<int>  Graph::dijkstra(Grid& grid){

  std::vector<int> temp_path;
  double dist[graph.size()];
  int parent[graph.size()];
  int status[graph.size()];
    
  for(int i = 0; i < graph.size(); ++i)
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
  while(status[dest]!=2 and count<graph.size()-1)
       {
          std::vector<int> ulist = minDistance(dist, status, graph.size());
          //std::cout<<"size of Q: "<<ulist.size()<<std::endl;
          if(ulist.empty()) {temp_path.clear(); return temp_path;}
          int u=ulist[0];
          //std::cout<<"check u: "<<u<<" x: "<<grid.vertices_graph[u].x<<" y: "<<grid.vertices_graph[u].y <<std::endl;
          status[u] = 2;
          
          for (int j = 0; j < graph[u].list.size(); ++j)
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
                      else if (status[v]==1 and dist[v]>dist[u]+graph[u].list[j].weight)
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

void Graph::printPath(int parent[], int j, int Vsize, std::vector<int> & temp_path)
{
  if(j == -1)
    {
      return;
    }
  printPath(parent, parent[j], Vsize, temp_path);
  if( !(j==source or j==dest))
    { 
       temp_path.push_back(j);
       //std::cout<<"path push "<<j<<std::endl;
    }
}

std::vector<int> Graph::minDistance(double dist[], int status[], int V)
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
  for(int i=0;i<path.size()-1;++i){
      for(int j=0;j<graph[path[i]].list.size();++j){
            if(graph[path[i]].list[j].dest == path[i+1]){
               graph[path[i]].list[j].weight = alpha * graph[path[i]].list[j].weight;
              }
         } 
     }

  for(int i=path.size()-1;i>-1;i--){
      for(int j=0;j<graph[path[i]].list.size();++j){
            if(graph[path[i]].list[j].dest == path[i-1]){
               graph[path[i]].list[j].weight = alpha * graph[path[i]].list[j].weight;
              }
         } 
     }

};

void Graph::Path_graph_total(Grid& grid, std::vector<int> &temp_path){

  for(int i=0; i<temp_path.size(); ++i){
        temp_path[i] = grid.vertices_graph[temp_path[i]].index;
     }

};

std::vector<std::vector<int> > Graph::GetShorestPath(){

  return Path;

};

std::vector<std::vector<RouterDB::Metal> >  Graph::ConvertPathintoPhysical(Grid& grid){

  std::vector<std::vector<RouterDB::Metal> > Phsical_Path;
  for(int i= 0; i<Path.size();++i){
      std::vector<RouterDB::Metal> temp_physical_path;
      //int start_index = 0;
      //int end_index = 0;
      int flag_start_write = 1;
      //int flag_end_write = 0;
      RouterDB::point temp_point;
      RouterDB::Metal temp_metal;
      for(int j=0;j<Path[i].size();++j){
          if(flag_start_write == 1){
              temp_metal.LinePoint.clear();
              temp_metal.MetalIdx = grid.vertices_total[Path[i][j]].metal;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              flag_start_write = 0;
            }
           if(j<Path[i].size()-1 and grid.vertices_total[Path[i][j]].metal!=grid.vertices_total[Path[i][j+1]].metal){
              flag_start_write = 1;
              temp_point.x = grid.vertices_total[Path[i][j]].x;
              temp_point.y = grid.vertices_total[Path[i][j]].y;
              temp_metal.LinePoint.push_back(temp_point);
              temp_metal.width = grid.drc_info.Metal_info[grid.vertices_total[Path[i][j]].metal].width;
              temp_physical_path.push_back(temp_metal);
            }
            if(j==Path[i].size()-1 and flag_start_write == 0){

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
