#include "GlobalGraph.h"

GlobalGraph::GlobalGraph(GlobalGrid& grid):path_number(1) {
  //this->grid=grid; 
  //std::cout<<"~~~~~Before list \n";
  //this->grid.CheckVerticesTotal();
  //use grid information to create adjacentlist
  //this->path_number=1;
  std::cout<<"Start Creating adjacent list (graph), ";
  CreateAdjacentList(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  std::cout<<"End creating adjacent list (graph)"<<std::endl;
  //std::cout<<"~~~~~After list \n";
  //this->grid.CheckVerticesTotal();
};

void GlobalGraph::clearPath(){

  Path.clear();

};

void GlobalGraph::FindSTs(GlobalGrid& grid, int pathNo, std::vector<int> &stiner_node) {
  //this->grid=grid; &
  //std::cout<<"~~~~~Before list \n";
  //this->grid.CheckVerticesTotal();
  //use grid information to create adjacentlist
  //std::cout<<"Start Creating adjacent list (graph), ";
  //CreateAdjacentList(grid); //create adjacentList base gird.LL_graph and gird.UR_graph
  //std::cout<<"End creating adjacent list (graph)"<<std::endl;
  //std::cout<<"~~~~~After list \n";
  //this->grid.CheckVerticesTotal();
  //find shortest path based source and dest

  this->path_number=pathNo;

  std::vector<std::vector<int> >temp_terminals = Pin_terminals;

  for(int i =0;i<pathNo;++i){

     Pin_terminals = temp_terminals;

     std::vector<std::pair<int,int> > temp_path;
     //std::cout<<"Start iterate steiner"<<std::endl;
     Iterated_Steiner(grid,stiner_node); 
     //std::cout<<"End iterate steiner"<<std::endl;
     int weight;    

     std::cout<<"Start MST1"<<std::endl;
     std::cout<<"Pin number "<<Pin_terminals.size()<<std::endl;
     MST(weight, temp_path, grid);
     std::cout<<"End MTS1"<<std::endl;
     std::cout<<temp_path.size()<<std::endl;
     UpdateEdgeWeight(temp_path);
     std::cout<<"End Update weight"<<std::endl;
     //return the shortest path
     Path.push_back(temp_path);

  }

  refreshWeight(grid);


};

void GlobalGraph::UpdateEdgeWeight(std::vector<std::pair<int,int> > temp_path){

   int times = 2;

   for(unsigned int i=0;i<temp_path.size();i++){
        for(unsigned int j=0;j<graph[temp_path[i].first].list.size();j++){
             if(graph[temp_path[i].first].list[j].dest == temp_path[i].second){
                  graph[temp_path[i].first].list[j].weight = graph[temp_path[i].first].list[j].weight*times;
               }
           }

        for(unsigned int j=0;j<graph[temp_path[i].second].list.size();j++){
             if(graph[temp_path[i].second].list[j].dest == temp_path[i].first){
                  graph[temp_path[i].second].list[j].weight = graph[temp_path[i].second].list[j].weight*times;
               }
           }

      }
};

void GlobalGraph::refreshWeight(GlobalGrid &grid){

 for(unsigned int i=0;i<graph.size()-2;i++){
      for(unsigned int j=0;j<graph[i].list.size();j++){
           graph[i].list[j].weight =(double) abs(grid.tiles_total[graph[i].src].x - grid.tiles_total[graph[i].list[j].dest].x)+abs(grid.tiles_total[graph[i].src].y - grid.tiles_total[graph[i].list[j].dest].y);
          }
    }

};

void GlobalGraph::Iterated_Steiner(GlobalGrid &grid, std::vector<int> &Pontential_Stiner_node){


  //std::vector<int> Pontential_Stiner_node = Get_Potential_Steiner_node(grid);

//  std::cout<<"Terminal size "<<terminals.size()<<std::endl;
//  std::cout<<"Potential_Steiner_node size()"<<Pontential_Stiner_node.size()<<std::endl;

  int iterate_number = Pin_terminals.size()-2;

  int LastWireLength = INT_MAX;

  int WireLength = INT_MAX;

  int Flag = 1;

  while(iterate_number>0 and Flag){

        int index = -1;        
 
        GetWireLength(WireLength,index,Pontential_Stiner_node, grid); //based on all pontential stinter node

        int DetailWireLength = LastWireLength - WireLength;

        if(DetailWireLength > 0){

            LastWireLength = WireLength;

            AddStinerNodeToTerminals(Pontential_Stiner_node,index);

           }else{

            Flag = 0;

           }

         iterate_number = iterate_number - 1;

        //find a stiner node
        }
 

};

void GlobalGraph::AddStinerNodeToTerminals(std::vector<int> &Pontential_Stiner_node,int index){

  std::vector<int> Potential_node;

  for(unsigned int i = 0;i<Pontential_Stiner_node.size();i++){
       
    if((int)i==index){
         
         std::vector<int> temp_pin;
         temp_pin.push_back(Pontential_Stiner_node[i]);
         Pin_terminals.push_back(temp_pin);
         
        }else{
         
         Potential_node.push_back(Pontential_Stiner_node[i]);

        }
      
     }

   Pontential_Stiner_node = Potential_node;


};


/*
std::vector<int> GlobalGraph::Get_Potential_Steiner_node(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> Set_tiles){

  std::vector<int> snode;
  //based on terminals get all snode node in some region

  std::set<RouterDB::tile, RouterDB::tileComp> Set_tiles; //it's better to construct this function when terminals are given in grid function

  for(int i=0;i<grid.tiles_total.size();i++){ //is it possible that some tiles are untouchable?
       Set_tiles.insert(grid.tiles_total[i]);
     }

  int min_x = INT_MAX;
  int min_y = INT_MAX;
  int max_x = INT_MIN;
  int max_y = INT_MIN;
    

  for(int i=0;i<terminals.size();i++){
       if(grid.tiles_total[terminals[i]].x<min_x){min_x = grid.tiles_total[terminals[i]].x;}
       if(grid.tiles_total[terminals[i]].y<min_y){min_y = grid.tiles_total[terminals[i]].y;}
       if(grid.tiles_total[terminals[i]].x>max_x){max_x = grid.tiles_total[terminals[i]].x;}
       if(grid.tiles_total[terminals[i]].y>max_y){max_y = grid.tiles_total[terminals[i]].y;}
     }

  RouterDB::tile min_temp_tile = grid.tiles_total[terminals[0]];
  RouterDB::tile max_temp_tile = grid.tiles_total[terminals[0]];
  min_temp_tile.x = min_x;
  min_temp_tile.y = min_y;
  min_temp_tile.index = 0;
  max_temp_tile.x = max_x;
  max_temp_tile.y = max_y;
  max_temp_tile.index = grid.tiles_total.size()-1;

  std::set<RouterDB::tile, RouterDB::tileComp >::iterator itlow, itup, xit;

  itup = Set_tiles.upper_bound(max_temp_tile);
  itlow = Set_tiles.lower_bound(min_temp_tile);

  for(xit=itlow;xit!=itup;++xit){
      
       snode.push_back(xit->index);
  }
  
  //min x, y, max x, y 
  //find all the node in this box but except for the node which is all ready terminals
  

  return snode;


};

*/

void GlobalGraph::GetWireLength(int &WireLength, int &index, std::vector<int> Pontential_Stiner_node, GlobalGrid &grid){

//separete those two teminals
  
//  std::cout<<"Start Get WireLength"<<std::endl;

  int Last_WireLength = INT_MAX; 

  for(unsigned int i=0;i<Pontential_Stiner_node.size();i++){
      
      std::vector<int> temp_pin;
      temp_pin.push_back(Pontential_Stiner_node[i]);
      Pin_terminals.push_back(temp_pin);
      std::vector<pair<int,int> > temp_path;
//      std::cout<<"Start MST"<<std::endl;
      MST(WireLength, temp_path, grid);
//      std::cout<<"End MST"<<std::endl;
      if(WireLength<Last_WireLength){
          Last_WireLength = WireLength;
          index = i;
        }
      Pin_terminals.pop_back();

     }

//  std::cout<<"End Get WireLength"<<std::endl;
  


};



void GlobalGraph::InitialSrcDest(std::vector<int> & temp_src, std::vector<int> & temp_dest, std::vector<int> &pin_access){

  std::set<int> src_set;
  std::set<int> dest_set;

  for(unsigned int i=0;i<Pin_terminals.size();i++){
      //for(int j=0;j<Pin_terminals[i].size();j++){

     if(i==0){
        for(unsigned int j=0;j<Pin_terminals[i].size();j++){
            src_set.insert(Pin_terminals[i][j]);
           }
        pin_access.push_back(1);
        //pin_access.push_back(0);
       }else{
        for(unsigned int j=0;j<Pin_terminals[i].size();j++){
            dest_set.insert(Pin_terminals[i][j]);
           }
        pin_access.push_back(0);
      }    
        
     }

  std::set<int>::iterator itlow, itup, xit;

  itup = src_set.end();
  itlow = src_set.begin();

  for(xit=itlow;xit!=itup;++xit){
      
      temp_src.push_back(*xit);
  }

  itup = dest_set.end();
  itlow = dest_set.begin();

  for(xit=itlow;xit!=itup;++xit){
      
      temp_dest.push_back(*xit);
  }
  

};


void GlobalGraph::ChangeSrcDest(std::vector<int> &temp_src, std::vector<int> &temp_dest, std::vector<int> temp_single_path, std::vector<int> &pin_access){

  std::cout<<"Test1"<<std::endl;
  for(unsigned int i=0;i<temp_single_path.size();i++){
        for(unsigned int j=0;j<Pin_terminals.size();j++){
             for(unsigned int k=0;k<Pin_terminals[j].size();k++){
                  if(temp_single_path[i]==Pin_terminals[j][k]){
                      pin_access[j]=1;
                    }
                }
           }
     }

  std::cout<<"Test2"<<std::endl;
  temp_src.clear();
  temp_dest.clear();

  std::set<int> src_set;
  std::set<int> dest_set; 

  std::cout<<"pin_access size "<<pin_access.size()<<std::endl;
  std::cout<<"Pin_terminals size "<<Pin_terminals.size()<<std::endl;

  for(unsigned int i=0;i<pin_access.size();i++){
      if(pin_access[i]==1){
         for(unsigned int j=0;j<Pin_terminals[i].size();j++){
             src_set.insert(Pin_terminals[i][j]);
            }
        }else{
         for(unsigned int j=0;j<Pin_terminals[i].size();j++){
             dest_set.insert(Pin_terminals[i][j]);
            }
        }
     }
  std::cout<<"Test3"<<std::endl;
  for(unsigned int i=0;i<temp_single_path.size();i++){
     src_set.insert(temp_single_path[i]);
     }


  std::set<int>::iterator itlow, itup, xit;

  itup = src_set.end();
  itlow = src_set.begin();

  for(xit=itlow;xit!=itup;++xit){
      
      temp_src.push_back(*xit);
  }

  itup = dest_set.end();
  itlow = dest_set.begin();

  for(xit=itlow;xit!=itup;++xit){
      
      temp_dest.push_back(*xit);
  }
  std::cout<<"Test4"<<std::endl;
  
};

void GlobalGraph::MST(int & WireLength, std::vector<pair<int,int> > &temp_path, GlobalGrid &grid){

    //std::vector<int> terminals; //Nodes index of terminals in graph
    //std::vector<Node> graph;
    //given any terminals, and graphs find return a path and value
    std::vector<std::vector<int> > MST_path;
    std::vector<int> temp_src;
    std::vector<int> temp_dest;
    std::vector<int> pin_access;
    std::cout<<"Starting initialSrcDest"<<std::endl;
    InitialSrcDest(temp_src, temp_dest, pin_access);
    std::cout<<"pin_access size "<<pin_access.size()<<std::endl;
    std::cout<<"End initialSrcDest"<<std::endl;
    //std::cout<<"temp_dest size "<<temp_dest.size()<<std::endl;


     if(temp_dest.size()==0){
     
        std::vector<int> MST_temp_path;
        MST_temp_path.push_back(temp_src[0]);
        //MST_temp_path.push_back(temp_src[0]); 
        MST_path.push_back(MST_temp_path);

     }


     while(temp_dest.size()>0){
         //std::cout<<"temp_dest size "<<temp_dest.size()<<std::endl;
         std::vector<int> src_set = temp_src;
         std::cout<<"temp_src size "<<temp_src.size()<<std::endl;
         for(unsigned int p=0;p<temp_src.size();p++){std::cout<<temp_src[p];}
         std::cout<<std::endl;
         std::vector<int> dest_set = temp_dest;
         std::cout<<"temp_dest size "<<temp_dest.size()<<std::endl;
         for(unsigned int p=0;p<temp_dest.size();p++){std::cout<<temp_dest[p];}
         std::cout<<std::endl;
         std::cout<<"start setting src and dest"<<std::endl;
         SetSrcDest(src_set, dest_set);
         std::cout<<"End setting src and dest"<<std::endl;
         std::vector<int> temp_single_path = dijkstra(grid);
         std::cout<<"temp_single_path size "<<temp_single_path.size()<<std::endl;
         for(unsigned int p=0;p<temp_single_path.size();p++){std::cout<<temp_single_path[p];}
         std::cout<<std::endl;
         std::cout<<"End dijkstra"<<std::endl;
         MST_path.push_back(temp_single_path);
         RMSrcDest(src_set, dest_set);
         std::cout<<"RMSrcDest"<<std::endl;
         ChangeSrcDest(temp_src, temp_dest, temp_single_path, pin_access);
         std::cout<<"ChangeSrcDest"<<std::endl;
       }
     WireLength = Calculate_Weigt(MST_path);
     temp_path = Get_MST_Edges(MST_path);

     //need a vector<Edges>??? and a map???
     //return Cumulated_weight;

};


int GlobalGraph::Calculate_Weigt(std::vector<std::vector<int> > temp_path){

   int sum = 0;
   for(unsigned int i=0;i<temp_path.size();i++){
       
        for(unsigned int j=0;j<temp_path[i].size()-1;j++){
           
             for(unsigned int k=0;k<graph[temp_path[i][j]].list.size();k++){
                 
                 if(graph[temp_path[i][j]].list[k].dest == temp_path[i][j+1]){
                     sum = sum + graph[temp_path[i][j]].list[k].weight;
                     break;
                   }
                
                }
             
           }
       
      }

  return sum;

};

std::vector<std::pair<int,int> > GlobalGraph::Get_MST_Edges(std::vector<std::vector<int> > temp_path){

   std::vector<std::pair<int,int> > temp_MST_Edges;
   std::pair<int,int> temp_Edge;
   
   for(unsigned int i=0;i<temp_path.size();i++){

        if(temp_path[i].size()==1){
        
             temp_Edge.first = temp_path[i][0];
             temp_Edge.second = temp_path[i][0];
             temp_MST_Edges.push_back(temp_Edge);

        }     
       
        for(int j=0;j<(int)temp_path[i].size()-1;j++){
           
             temp_Edge.first = temp_path[i][j];
             temp_Edge.second = temp_path[i][j+1];
             temp_MST_Edges.push_back(temp_Edge);
             
           }
       
      }

  return temp_MST_Edges;

};


void GlobalGraph::CreateAdjacentList(GlobalGrid& grid){


  for(unsigned int i=0;i<grid.tiles_total.size();i++){
      
        Node tempNode;
        tempNode.src=i;
        Edge tempEdge;

        for(unsigned int j=0;j<grid.tiles_total[i].north.size();j++){

           std::cout<<"Grid capacity north"<<grid.tiles_total[i].north[j].capacity<<std::endl;

            if(grid.tiles_total[i].north[j].capacity>0 and grid.tiles_total[i].north[j].next != -1){

               tempEdge.dest=grid.tiles_total[i].north[j].next;
               tempEdge.weight = (double) abs(grid.tiles_total[i].y-grid.tiles_total[grid.tiles_total[i].north[j].next].y)+abs(grid.tiles_total[i].x-grid.tiles_total[grid.tiles_total[i].north[j].next].x);
               tempEdge.capacity = grid.tiles_total[i].north[j].capacity;
               tempNode.list.push_back(tempEdge);
          
               }           
           }

        for(unsigned int j=0;j<grid.tiles_total[i].south.size();j++){

            std::cout<<"Grid capacity south"<<grid.tiles_total[i].south[j].capacity<<std::endl;

            if(grid.tiles_total[i].south[j].capacity>0 and grid.tiles_total[i].south[j].next != -1){

               tempEdge.dest=grid.tiles_total[i].south[j].next;
               tempEdge.weight = (double) abs(grid.tiles_total[i].y-grid.tiles_total[grid.tiles_total[i].south[j].next].y)+abs(grid.tiles_total[i].x-grid.tiles_total[grid.tiles_total[i].south[j].next].x);
               tempEdge.capacity = grid.tiles_total[i].south[j].capacity;
               tempNode.list.push_back(tempEdge);
          
               }           
           }

        for(unsigned int j=0;j<grid.tiles_total[i].east.size();j++){

            std::cout<<"Grid capacity east"<<grid.tiles_total[i].east[j].capacity<<std::endl;

            if(grid.tiles_total[i].east[j].capacity>0 and grid.tiles_total[i].east[j].next != -1){

               tempEdge.dest=grid.tiles_total[i].east[j].next;
               tempEdge.weight = (double) abs(grid.tiles_total[i].y-grid.tiles_total[grid.tiles_total[i].east[j].next].y)+abs(grid.tiles_total[i].x-grid.tiles_total[grid.tiles_total[i].east[j].next].x);
               tempEdge.capacity = grid.tiles_total[i].east[j].capacity;
               tempNode.list.push_back(tempEdge);
          
               }           
           }

        for(unsigned int j=0;j<grid.tiles_total[i].west.size();j++){

            std::cout<<"Grid capacity west"<<grid.tiles_total[i].west[j].capacity<<std::endl;

            if(grid.tiles_total[i].west[j].capacity>0 and grid.tiles_total[i].west[j].next != -1){

               tempEdge.dest=grid.tiles_total[i].west[j].next;
               tempEdge.weight = (double) abs(grid.tiles_total[i].y-grid.tiles_total[grid.tiles_total[i].west[j].next].y)+abs(grid.tiles_total[i].x-grid.tiles_total[grid.tiles_total[i].west[j].next].x);
               tempEdge.capacity = grid.tiles_total[i].west[j].capacity;
               tempNode.list.push_back(tempEdge);
          
               }           
           }

        for(unsigned int j=0;j<grid.tiles_total[i].up.size();j++){

            std::cout<<"Grid capacity up"<<grid.tiles_total[i].up[j].capacity<<std::endl;

            if(grid.tiles_total[i].up[j].capacity>0 and grid.tiles_total[i].up[j].next != -1){

               tempEdge.dest=grid.tiles_total[i].up[j].next;
               tempEdge.weight = (double) abs(grid.tiles_total[i].y-grid.tiles_total[grid.tiles_total[i].up[j].next].y)+abs(grid.tiles_total[i].x-grid.tiles_total[grid.tiles_total[i].up[j].next].x);
               tempEdge.capacity = grid.tiles_total[i].up[j].capacity;
               tempNode.list.push_back(tempEdge);
          
               }           
           }

        for(unsigned int j=0;j<grid.tiles_total[i].down.size();j++){

            std::cout<<"Grid capacity down"<<grid.tiles_total[i].down[j].capacity<<std::endl;

            if(grid.tiles_total[i].down[j].capacity>0 and grid.tiles_total[i].down[j].next != -1){

               tempEdge.dest=grid.tiles_total[i].down[j].next;
               tempEdge.weight = (double) abs(grid.tiles_total[i].y-grid.tiles_total[grid.tiles_total[i].down[j].next].y)+abs(grid.tiles_total[i].x-grid.tiles_total[grid.tiles_total[i].down[j].next].x);
               tempEdge.capacity = grid.tiles_total[i].down[j].capacity;
               tempNode.list.push_back(tempEdge);
          
               }           
           }
        


        graph.push_back(tempNode);

     }


  source = graph.size();
  dest = source + 1;
     
  Node tempNodeS;
  tempNodeS.src = source;
  graph.push_back(tempNodeS);

  Node tempNodeD;
  tempNodeD.src = dest;
  graph.push_back(tempNodeD);

};

void GlobalGraph::SetSrcDest(std::vector<int> temp_src, std::vector<int> temp_dest){

    std::cout<<"Start Set Src"<<std::endl;
    for(unsigned int i=0;i<temp_src.size();++i)
     {
        //if(temp_src[i]<graph.size()-1){
        Edge tempEdge;
        tempEdge.dest = temp_src[i];
        tempEdge.weight = 0;
        graph[source].list.push_back(tempEdge);
        tempEdge.dest = source;
        graph[temp_src[i]].list.push_back(tempEdge);
        //}
        //std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
     }
    std::cout<<"End Set Src"<<std::endl;

    std::cout<<"Start Set Dest"<<std::endl;
    for(unsigned int i=0;i<temp_dest.size();++i)
     {
        //if(temp_dest[i]<graph.size()-1){
        Edge tempEdge;
        tempEdge.dest = temp_dest[i];
        std::cout<<"temp_dest "<<temp_dest[i]<<std::endl;
        tempEdge.weight = 0;
        std::cout<<"dest 1"<<dest<<std::endl;
        graph[dest].list.push_back(tempEdge);
        std::cout<<"dest 2"<<dest<<std::endl;
        tempEdge.dest = dest;
        std::cout<<"dest 3"<<dest<<std::endl;
        graph[temp_dest[i]].list.push_back(tempEdge);
        std::cout<<"dest 4"<<dest<<std::endl;
        //}
        //std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
     }  
    std::cout<<"End Set Dest"<<std::endl;

};

void GlobalGraph::RMSrcDest(std::vector<int> temp_src, std::vector<int> temp_dest){

    graph[source].list.clear();
    graph[dest].list.clear();

    for(unsigned int i=0;i<temp_src.size();++i)
     {   
        //if(temp_src[i]<graph.size()-1){
        graph[temp_src[i]].list.pop_back();
        //}
        //std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
     }

    for(unsigned int i=0;i<temp_dest.size();++i)
     {
        //if(temp_dest[i]<graph.size()-1){
        graph[temp_dest[i]].list.pop_back();
        //}
        //std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
     }  

};


void GlobalGraph::RemovefromMultMap(std::multimap<double, int>& mmap, double dist, int idx) {
  std::multimap<double, int>::iterator low=mmap.lower_bound(dist);
  std::multimap<double, int>::iterator high=mmap.upper_bound(dist);
  std::multimap<double, int>::iterator tar;
  bool mark=false;
  for(tar=low; tar!=high; ++tar) {
    if(tar->second==idx) {mark=true; break;}
  }
  if(mark) {mmap.erase(tar);}
  else {std::cout<<"Graph-Info: cannot found element in map\n";}
}

void GlobalGraph::UpdateMultMap(std::multimap<double, int>& mmap, double olddist, int idx, double newdist) {
  this->RemovefromMultMap(mmap, olddist, idx);
  mmap.insert(std::pair<double, int>(newdist, idx));
}

std::vector<int> GlobalGraph::minDistancefromMultiMap(std::multimap<double, int> &mmap)
{
  std::vector<int> min_index;
  std::multimap<double, int>::iterator miter=mmap.begin();
  double min = miter->first;
  std::multimap<double, int>::iterator low=mmap.lower_bound(min);
  std::multimap<double, int>::iterator high=mmap.upper_bound(min);
  for(std::multimap<double, int>::iterator it=low; it!=high; ++it) {
    min_index.push_back(it->second);
  }
  return min_index;
};


std::vector<int>  GlobalGraph::dijkstra(GlobalGrid& grid){

  std::vector<int> temp_path;

  std::cout<<"checkpoint 0"<<std::endl;
 
  std::cout<<"graph.size() "<<graph.size()<<std::endl;

  std::vector<double> dist;
  dist.resize(graph.size());
  //double dist[graph.size()];

  std::cout<<"check point 0.1"<<std::endl;
  std::vector<int> parent;
  parent.resize(graph.size());
  //int parent[graph.size()];

  std::cout<<"check point 0.2"<<std::endl;
  std::vector<int> status;
  status.resize(graph.size());
  //int status[graph.size()];

  std::cout<<"check point 0.3"<<std::endl;

  std::multimap<double, int> distMap;
    
  for(unsigned int i = 0; i < graph.size(); ++i)
     {
        parent[i] = -1;
        dist[i] = INT_MAX;
        status[i] = 0;
     }

  std::cout<<"checkpoint 1"<<std::endl;
  dist[source] = 0;
  status[source] = 1;
  distMap.insert ( std::pair<double,int>(dist[source], source) );
  std::cout<<"checkpoint 2"<<std::endl;
  int count=0;
  int v;
  //std::cout<<"graph source "<<source<<" vs graph dest "<<dest<<std::endl;
  while(status[dest]!=2 and count<(int)graph.size()-1)
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
                      else if (status[v]==1 and dist[v]>dist[u]+graph[u].list[j].weight)
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

  std::cout<<"checkpoint 3"<<std::endl;
  printPath(parent, dest, graph.size(), temp_path);
  std::cout<<"checkpoint 4"<<std::endl;
  //std::cout<<"temp path"<<std::endl;
  //for(int i=0;i<temp_path.size();i++) {std::cout<<temp_path[i]<<" "<<std::endl;}
  return temp_path;

};


//std::vector<int>  GlobalGraph::dijkstraRetire(GlobalGrid &grid){
//
//  std::vector<int> temp_path;
//  double dist[graph.size()];
//  int parent[graph.size()];
//  int status[graph.size()];
//    
//  for(int i = 0; i < graph.size(); ++i)
//     {
//        parent[i] = -1;
//        dist[i] = INT_MAX;
//        status[i] = 0;
//     }
//
//  dist[source] = 0;
//  status[source] = 1;
//  int count=0;
//  int v;
//  //std::cout<<"graph source "<<source<<" vs graph dest "<<dest<<std::endl;
//  //std::cout<<grid.tiles_total[source].x<<" "<<grid.tiles_total[source].y<<std::endl;
//  //std::cout<<grid.tiles_total[dest].x<<" "<<grid.tiles_total[dest].y<<std::endl;
//  while(status[dest]!=2 and count<graph.size()-1)
//       {
//          std::vector<int> ulist = minDistance(dist, status, graph.size());
//          //std::cout<<"size of Q: "<<ulist.size()<<std::endl;
//          if(ulist.empty()) {temp_path.clear();std::cout<<"Error No feasible path"<<std::endl; return temp_path;}
//          int u=ulist[0];
//          //std::cout<<"check u: "<<u<<" x: "<<grid.tiles_total[u].x<<" y: "<<grid.tiles_total[u].y <<std::endl;
//          status[u] = 2;
//          
//          for (int j = 0; j < graph[u].list.size(); ++j)
//              {
//                 v=graph[u].list[j].dest;
//                 if(v!=u)
//                   {
//                      if(status[v]==0)
//                        {
//                           parent[v] = u;
//                           dist[v] = dist[u]+graph[u].list[j].weight;
//                           status[v]=1;
//                         }
//                      else if (status[v]==1 and dist[v]>dist[u]+graph[u].list[j].weight)
//                         {
//                            parent[v] = u;
//                            dist[v] = dist[u]+graph[u].list[j].weight;
//                         }
//                    }
//               }
//          count++;
//       }
//
//  //std::cout<<"End dijstra"<<std::endl;
//  //std::cout<<"temp_path size "<<temp_path.size()<<std::endl;
//  //std::cout<<"parent size"<<parent.size()<<std::endl;
//  printPath(parent, dest, graph.size(), temp_path);
//  //std::cout<<"temp path"<<std::endl;
//  //for(int i=0;i<temp_path.size();i++) {std::cout<<temp_path[i]<<" "<<std::endl;}
//  return temp_path;
//
//};

void GlobalGraph::printPath(std::vector<int>& parent, int j, int Vsize, std::vector<int> & temp_path)
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

std::vector<int> GlobalGraph::minDistance(double dist[], int status[], int V)
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

void GlobalGraph::setTerminals(const std::vector<std::vector<int> >& t){

 Pin_terminals = t;

};

void GlobalGraph::setterminals(const std::vector<int>& t){

 terminals = t;

};

std::vector<std::vector<std::pair<int,int> > >GlobalGraph::returnPath(){

  return Path;

};


/*
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
*/
