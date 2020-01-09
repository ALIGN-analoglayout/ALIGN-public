#include "GcellDetailRouter.h"

GcellDetailRouter::GcellDetailRouter(){

};

GcellDetailRouter::GcellDetailRouter(PnRDB::hierNode& HierNode, GcellGlobalRouter& GR, int path_number, int grid_scale){

  std::cout<<"start detail router\n";
  this->Nets = GR.Nets;
  this->Blocks = GR.Blocks;
  this->Terminals = GR.Terminals;
  this->drc_info = GR.drc_info;
  this->terminal_routing = GR.terminal_routing;
  this->lowest_metal = GR.lowest_metal;
  this->highest_metal = GR.highest_metal;
  this->width = GR.width;
  this->height = GR.height;
  this->LL.x = 0;
  this->LL.y = 0;
  this->UR.x = GR.width;
  this->UR.y = GR.height;
  this->LL=GR.LL;
  this->UR=GR.UR;
  this->path_number = path_number;
  this->grid_scale = grid_scale;
  this->layerNo = GR.drc_info.Metal_info.size();
  this->isTop = GR.isTop;
  this->Gcell = GR.Gcell;
  this->temp_report.node_name = HierNode.name;

  printNetsInfo(); 

  create_detailrouter(); 

  std::cout<<"***************physical metal and via"<<std::endl;
  Physical_metal_via(); //this needs modify

  std::cout<<"Start Extend Metal"<<std::endl;
  ExtendMetal(); 
  std::cout<<"End Extend Metal"<<std::endl; 

  std::cout<<"***********start return node in detail router********"<<std::endl;
  ReturnHierNode(HierNode);
  std::cout<<"************end return node in detail router**********"<<std::endl;

};

void GcellDetailRouter::printNetsInfo(){

  for(unsigned int i=0;i<Nets.size();i++){

      std::cout<<"Net name "<<Nets[i].netName<<std::endl;
          
      std::cout<<"Net pins"<<std::endl;

      for(unsigned int j=0;j<Nets[i].connectedTile.size();j++){

            for(unsigned int k=0;k<Nets[i].connectedTile[j].size();k++){

                std::cout<<Nets[i].connectedTile[j][k]<<" ";

               }
                std::cout<<std::endl;

          }

       std::cout<<"Global path"<<std::endl;
     
      int ST_index = Nets[i].STindex;

      for(unsigned int j=0;j<Nets[i].STs[ST_index].path.size();j++){

           std::cout<<" ( "<<Nets[i].STs[ST_index].path[j].first<<" "<<Nets[i].STs[ST_index].path[j].second<<" ) ";

          }
          
       std::cout<<std::endl;

     }

};

std::vector<RouterDB::Metal> GcellDetailRouter::CpSymPath(std::vector<RouterDB::Metal> &temp_path, int H, int center){


  std::vector<RouterDB::Metal> sym_path;

      
     for(unsigned int j=0;j<temp_path.size();j++){

           RouterDB::Metal temp_metal = temp_path[j];

           if(H){

             temp_metal.LinePoint[0].y = 2*center - temp_metal.LinePoint[0].y;
             temp_metal.LinePoint[1].y = 2*center - temp_metal.LinePoint[1].y;   

             }else{

             temp_metal.LinePoint[0].x = 2*center - temp_metal.LinePoint[0].x;
             temp_metal.LinePoint[1].x = 2*center - temp_metal.LinePoint[1].x;
 
             }

           sym_path.push_back(temp_metal);

          }

   return sym_path;

};

std::vector<std::pair<int,int> > GcellDetailRouter::MappingToConnected(RouterDB::R_const &temp_R, RouterDB::Net &temp_net){

  std::vector<std::pair<int,int> > Connected_Map;
  std::pair<int,int> temp_pair;
  for(unsigned int i=0;i<temp_R.start_pin.size();++i){
     for(unsigned int j=0;j<temp_net.connected.size();++j){
        if(temp_R.start_pin[i].first!=-1 and temp_R.start_pin[i].first ==temp_net.connected[j].iter and temp_R.start_pin[i].second ==temp_net.connected[j].iter2){
           temp_pair.first = j;
           break;
        }else if(temp_R.start_pin[i].first == -1 and temp_R.start_pin[i].second ==temp_net.connected[j].iter){
           temp_pair.first = j;
           break;
        }
     }

     for(unsigned int j=0;j<temp_net.connected.size();++j){
        if(temp_R.end_pin[i].first!=-1 and temp_R.end_pin[i].first ==temp_net.connected[j].iter and temp_R.end_pin[i].second ==temp_net.connected[j].iter2){
           temp_pair.second = j;
           break;
        }else if(temp_R.end_pin[i].first == -1 and temp_R.end_pin[i].second ==temp_net.connected[j].iter){
           temp_pair.second = j;
           break;
        }
     }

     Connected_Map.push_back(temp_pair);

  }

  return Connected_Map;

};

void GcellDetailRouter::GatherSourceDest(std::vector<std::pair<int,int> > & global_path, std::vector<int> &temp_src, std::vector<int> &temp_dest, std::vector<int> & Tile_Source, std::vector<int> & Tile_Dest){

  std::set<int> path;
  
  for(unsigned int i=0;i<global_path.size();++i){
    
    path.insert(global_path[i].first);
    path.insert(global_path[i].second);

  }

  for(unsigned int i=0;i<temp_src.size();++i){
   
     if(path.find(temp_src[i])!=path.end()){Tile_Source.push_back(temp_src[i]);}

  }

  for(unsigned int i=0;i<temp_dest.size();++i){
   
     if(path.find(temp_dest[i])!=path.end()){Tile_Dest.push_back(temp_dest[i]);}

  }




};


int GcellDetailRouter::Estimate_multi_connection_number(RouterDB::R_const &temp_R, std::vector<int> &temp_dis){

  std::vector<double> temp_resistance;
  std::vector<int> M_number;

  for(unsigned int i=0;i<temp_R.start_pin.size();++i){

     //double temp_res = (double) temp_dis[i]*drc_info.Metal_info[0].unit_R+2*drc_info.Via_model[0].R;
     double temp_res = (double) temp_dis[i]*drc_info.Metal_info[0].unit_R;
     std::cout<<"temp res "<<temp_res<<std::endl;
     temp_resistance.push_back(temp_res);
     std::cout<<"Required R "<<temp_R.R[i]<<std::endl;
     int m_number = ceil((double)temp_res/temp_R.R[i]);
     std::cout<<"m number "<<m_number<<std::endl;
     m_number = ceil((double) m_number/2);
     std::cout<<"half m number "<<m_number<<std::endl;
     M_number.push_back(m_number);
  }

  int net_m_number = 0;

  for(unsigned int i=0;i<M_number.size();++i){

     if(net_m_number<M_number[i]){

         net_m_number = M_number[i];
         
       }

  }

  std::cout<<"Multi Number "<<net_m_number<<std::endl;
  return net_m_number;

};


std::vector<int> GcellDetailRouter::EstimateDist(RouterDB::R_const &temp_R, RouterDB::Net &temp_net){

  std::cout<<"Start Estimation"<<std::endl;

  std::vector<std::pair<int,int> > Connected_Map = MappingToConnected(temp_R, temp_net);

  //std::cout<<"Connected_Map size "<<Connected_Map.size()<<std::endl;

  std::vector<int> Dist_es;

  std::cout<<"Global Path"<<std::endl;
  for(unsigned int i=0;i<temp_net.global_path.size();++i){

      std::cout<<"temp_net.global_path "<<temp_net.global_path[i].first<<" "<<temp_net.global_path[i].second<<std::endl;

  }

  //std::cout<<"ConnectedTile"<<std::endl;
  for(unsigned int i=0;i<temp_net.connectedTile.size();++i){

      std::cout<<"ConnectedTile"<<std::endl;
      for(unsigned int j=0;j<temp_net.connectedTile[i].size();++j){
         std::cout<<temp_net.connectedTile[i][j]<<" "<<std::endl;
      }

  }

  //std::cout<<"Connected_Map size "<<Connected_Map.size()<<std::endl;

  for(unsigned int i=0;i<Connected_Map.size();++i){

     //std::cout<<"i "<<i<<std::endl;
     //std::cout<<"Connected_Map "<<Connected_Map[i].first<<" "<<Connected_Map[i].second<<std::endl;
     std::vector<int> Tile_Source, Tile_Dest;
     GatherSourceDest(temp_net.global_path, temp_net.connectedTile[Connected_Map[i].first], temp_net.connectedTile[Connected_Map[i].second], Tile_Source, Tile_Dest);
     //std::cout<<"Tile_Source "<<Tile_Source[0]<<std::endl;
     //std::cout<<"Tile_Dest "<<Tile_Dest[0]<<std::endl;
     Graph temp_graph(temp_net.global_path, temp_net.connectedTile, Tile_Source, Tile_Dest);
     std::vector<std::vector<int> > global_path_return = temp_graph.GetShorestPath();

     int dis =0;
 
     for(unsigned int j=0;j<global_path_return.size();++j){

        //std::cout<<"j "<<j<<std::endl;        

        for(unsigned int k =0;k<global_path_return[j].size()-1;++k){

           //std::cout<<"k "<<k<<std::endl;        
   
           int index1 = global_path_return[j][k];
           int index2 = global_path_return[j][k+1];
           //std::cout<<"index1 "<<index1<<" "<<"index2 "<<index2<<std::endl;
           dis = dis + abs( Gcell.tiles_total[index1].x- Gcell.tiles_total[index2].x) + abs( Gcell.tiles_total[index1].y- Gcell.tiles_total[index2].y);

        }
     }


     Dist_es.push_back(dis);
     std::cout<<"Estimate dist "<<dis<<std::endl;     
  }
  
  //drc_info
  return Dist_es;
  
};

void GcellDetailRouter::Copy_tile_metals(){

  for(int i=0;i<Gcell.tiles_total.size();i++){

      Gcell.tiles_total[i].origin_metal = Gcell.tiles_total[i].metal;

    }

};

void GcellDetailRouter::modify_tile_metals(RouterDB::Net& Net, bool set){
  //set=1, set terminal tiles' metals to Lmetal~Hmetal
  //set=0, reset terminal tiles' metals
  std::vector<std::pair<int, int>> path = Net.STs[Net.STindex].path;
  if(set){
    std::vector<int> metal;
    for (int i = lowest_metal; i <= highest_metal;i++)metal.push_back(i);
    for (unsigned int j = 0; j < path.size(); ++j)
    {
      int first_tile = path[j].first, last_tile = path[j].second;
      if (std::find(Net.terminals.begin(), Net.terminals.end(), first_tile) != Net.terminals.end())
      {
        //if the first tile is terminal
        //Gcell.tiles_total[first_tile].origin_metal = Gcell.tiles_total[first_tile].metal;
        Gcell.tiles_total[first_tile].metal = metal;
      }
      if (std::find(Net.terminals.begin(), Net.terminals.end(), last_tile) != Net.terminals.end())
      {
        //if the last tile is terminal
        //Gcell.tiles_total[last_tile].origin_metal = Gcell.tiles_total[last_tile].metal;
        Gcell.tiles_total[last_tile].metal = metal;
      }
    }
  }else{
    for (unsigned int j = 0; j < path.size(); ++j)
    {
      int first_tile = path[j].first, last_tile = path[j].second;
      if (std::find(Net.terminals.begin(), Net.terminals.end(), first_tile) != Net.terminals.end())
      {
        //if the first tile is terminal
        Gcell.tiles_total[first_tile].metal = Gcell.tiles_total[first_tile].origin_metal;
      }
      if (std::find(Net.terminals.begin(), Net.terminals.end(), last_tile) != Net.terminals.end())
      {
        //if the last tile is terminal
        Gcell.tiles_total[last_tile].metal = Gcell.tiles_total[last_tile].origin_metal;
      }
    }
  }
  
}

void GcellDetailRouter::Adding_tiles_for_terminal(int tile_index, std::vector<std::pair<int,int> > &global_path ){

  std::pair<int,int> temp_path;
  temp_path.first = tile_index;
  temp_path.second = tile_index;
  global_path.push_back(temp_path);

  while(Gcell.tiles_total[tile_index].down.size()>0){
    if(Gcell.tiles_total[tile_index].down.size()>1){
        std::cout<<"Tile error"<<std::endl;
        assert(0);
      }
    tile_index = Gcell.tiles_total[tile_index].down[0].next;
    temp_path.first = tile_index;
    temp_path.second = tile_index;
    global_path.push_back(temp_path);
  }

  while(Gcell.tiles_total[tile_index].up.size()>0){
    if(Gcell.tiles_total[tile_index].up.size()>1){
        std::cout<<"Tile error"<<std::endl;
        assert(0);
      }
    tile_index = Gcell.tiles_total[tile_index].up[0].next;
    temp_path.first = tile_index;
    temp_path.second = tile_index;
    global_path.push_back(temp_path);   
  }

  


};

void GcellDetailRouter::Generate_Block_Terminal_Internal_Metal_Set(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x){

  //initial a set for internal metal
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize( this->layerNo );

  //std::cout<<"Gcell Detail Router Check point 1"<<std::endl;
  CreatePlistBlocks(plist, this->Blocks);

  //std::cout<<"Gcell Detail Router Check point 2"<<std::endl;
  CreatePlistTerminals(plist, this->Terminals);

  //std::cout<<"Gcell Detail Router Check point 4"<<std::endl;
  InsertPlistToSet_x(Set_x, plist);

  //std::cout<<"Gcell Detail Router Check point 5"<<std::endl;
  //std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_net;
};

void GcellDetailRouter::Initial_rouer_report_info(PnRDB::routing_net &temp_routing_net, int i){

  temp_routing_net.net_name = Nets[i].netName;

};

int GcellDetailRouter::R_constraint_based_Parallel_routing_number(int i){

  int multi_number = 0;

  if(Nets[i].R_constraints.size()>0){
        std::vector<int> Dist_es= EstimateDist(Nets[i].R_constraints[0], Nets[i]);
        multi_number = Estimate_multi_connection_number(Nets[i].R_constraints[0],Dist_es);
    }

  return multi_number;


};

void GcellDetailRouter::Global_Path_Operation_For_Pins(int i, std::vector<std::pair<int,int> > &global_path){

  for(unsigned int terminal_size=0;terminal_size<Nets[i].terminals.size();terminal_size++){
      Adding_tiles_for_terminal(Nets[i].terminals[terminal_size], global_path);
  }

};

void GcellDetailRouter::Global_Path_Operation_For_Symmetry_Pins(int i, std::vector<std::pair<int,int> > &global_path){

  std::pair<int,int> temp_global_path;
  if(Nets[i].symCounterpart!=-1 and Nets[i].symCounterpart < (int)Nets.size()-1){

     int sym_ST_index = Nets[Nets[i].symCounterpart].STindex;
     for(unsigned int j=0;j<Nets[Nets[i].symCounterpart].STs[sym_ST_index].path.size();j++){
           global_path.push_back(Nets[Nets[i].symCounterpart].STs[sym_ST_index].path[j]);
        }  
     for(unsigned int j=0;j<Nets[Nets[i].symCounterpart].terminals.size();j++){
           temp_global_path.first = Nets[Nets[i].symCounterpart].terminals[j];
           temp_global_path.second = Nets[Nets[i].symCounterpart].terminals[j];
           global_path.push_back(temp_global_path);
        }
    }

};

Grid GcellDetailRouter::Generate_Grid_Net(int i){

  RouterDB::point chip_LL;
  RouterDB::point chip_UR;
  chip_LL.x = 0;
  chip_LL.y = 0;
  chip_UR.x = width;
  chip_UR.y = height;
  int STindex = Nets[i].STindex;

  std::vector<std::pair<int,int> > global_path = Nets[i].STs[STindex].path;
  std::pair<int,int> temp_global_path;

  Global_Path_Operation_For_Pins(i, global_path);
  Global_Path_Operation_For_Symmetry_Pins(i, global_path);
  Grid grid(Gcell, global_path, drc_info, chip_LL, chip_UR, lowest_metal, highest_metal, grid_scale);
  grid.Full_Connected_Vertex();

  return grid;

};

void GcellDetailRouter::Grid_Inactive(Grid &grid, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net, RouterDB::point &gridll, RouterDB::point &gridur){

  gridll=grid.GetGridLL();
  gridur=grid.GetGridUR();
  //std::cout<<"Detail path region ( "<<gridll.x<<" "<<gridll.y<<") ( "<<gridur.x<<" "<<gridur.y<<" ) "<<std::endl;
  //std::cout<<"Gcell Detail Router Check point 8"<<std::endl;
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > plist = FindsetPlist(Set_x, gridll, gridur);
  //std::cout<<"Gcell Detail Router Check point 9"<<std::endl;
  grid.InactivePointlist(plist);//+back
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > temp_netplist = FindsetPlist(Set_net, gridll, gridur);
  //std::cout<<"Detail Router check point 1.3"<<std::endl;
  grid.InactivePointlist(temp_netplist);//+back

};

int GcellDetailRouter::Found_Pins_and_Symmetry_Pins(Grid &grid ,int i, std::vector<std::vector<RouterDB::SinkData> > &temp_pins){

  int sym_flag = 0;
  std::vector<std::vector<RouterDB::SinkData> > sym_temp_pins; //symmetry pins 
  std::vector<std::vector<RouterDB::SinkData> > common_pins; //common part for routing pins and symmetry pins

  if(Nets[i].symCounterpart!=-1 and Nets[i].symCounterpart < (int)Nets.size()-1){       
     sym_flag = findPins_Sym(grid, Nets[i], Nets[Nets[i].symCounterpart], Nets[i].sym_H, Nets[i].center, temp_pins, sym_temp_pins, common_pins);
     if(sym_flag == 1){
        std::cout<<"sym_flag exist"<<std::endl;
        //SortPins(temp_pins);
        //SortPins(sym_temp_pins);
        //SortPins(common_pins);
        temp_pins = common_pins;
       }
    }else{
     std::cout<<"Net index "<<i<<std::endl;
     std::cout<<"temp_ pin size "<<temp_pins.size()<<std::endl;
     temp_pins = findPins_new(grid, Nets[i]);
     std::cout<<"temp_ pin size "<<temp_pins.size()<<std::endl;
     //SortPins(temp_pins);
    }

    return sym_flag;

};


void GcellDetailRouter::Symmetry_metal_Inactive(int i, int sym_flag, Grid &grid, RouterDB::point sym_gridll, RouterDB::point sym_gridur, RouterDB::point &gridll, RouterDB::point &gridur){

       //modify_tile_metals(Nets[i], 1);
    if(sym_flag==1 and Nets[i].global_sym!=-1 and Nets[i].global_sym <(int)Nets.size()-1){

       RouterDB::point global_sym_gridll;
       RouterDB::point global_sym_gridur;
       //FindBoundryofGlobalSymNet(gridll,gridur,global_sym_gridll,global_sym_gridur,Nets[i].sym_H,Nets[i].center, Nets[i].global_sym);
      }

    // void InactivePointlist(std::vector< std::set<RouterDB::point, RouterDB::pointXYComp> > &plist);
    sym_gridll = gridll;
    sym_gridur = gridur;

    if(sym_flag ==1){
        std::cout<<"Starting sym net metal coping"<<std::endl;
        RouterDB::SinkData sym_aear;
        sym_aear.metalIdx = -1;
        sym_aear.coord.push_back(sym_gridll);
        sym_aear.coord.push_back(sym_gridur);
        sym_aear= Sym_contact(sym_aear, Nets[i].sym_H, Nets[i].center);
        sym_gridll = sym_aear.coord[0];
        sym_gridur = sym_aear.coord[1];
        std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > sym_netplist;
        std::cout<<"Starting sym block metal coping flag"<<std::endl;
        CreatePlistSymBlocks(sym_netplist, sym_gridll, sym_gridur, Nets[i].sym_H, Nets[i].center, gridll, gridur);
        std::cout<<"Starting sym block metal coping flag"<<std::endl;
        grid.InactivePointlist(sym_netplist);
        std::cout<<"End sym net metal coping"<<std::endl;
      }

};std::vector<RouterDB::SinkData> GcellDetailRouter::Initial_source_pin(std::vector<std::vector<RouterDB::SinkData> > &temp_pins, int &source_lock){

  std::vector<RouterDB::SinkData> temp_source;
  for(unsigned int j = 0;j<temp_pins[0].size();j++){
      temp_source.push_back(temp_pins[0][j]);
     }
  source_lock = 0;  

  return temp_source;

};

void GcellDetailRouter::Update_rouer_report_info(PnRDB::routing_net &temp_routing_net, int i, int j, int pathMark){

  std::string temp_pin_name;   
  if(Nets[i].connected[j].type==RouterDB::BLOCK){
       int iter2 = Nets[i].connected[j].iter2;
       int iter = Nets[i].connected[j].iter;
       temp_pin_name = Blocks[iter2].blockName + "." + Blocks[iter2].pins[iter].pinName;
    }else{
       int iter = Nets[i].connected[j].iter;
       temp_pin_name = Terminals[iter].name;
    }

   temp_routing_net.pin_name.push_back(temp_pin_name);
   if(j==0){
     temp_routing_net.pin_access.push_back(1);
   }else{
     temp_routing_net.pin_access.push_back(pathMark);
   }

};

void GcellDetailRouter::Detailed_router_set_src_dest(Grid &grid, std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest, int i, RouterDB::point &sym_gridll, RouterDB::point &sym_gridur, RouterDB::point &gridll, RouterDB::point &gridur, std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > &src_dest_plist, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net, int sym_flag){

   std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap; //this map can be removed
   grid.setSrcDest( temp_source, temp_dest, this->width, this->height, Smap);
   //std::cout<<"Detail Router check point 1.1"<<std::endl;
   grid.ActivateSourceDest();
   //std::cout<<"Detail Router check point 1.11"<<std::endl;
   //std::cout<<"Detail Router check point 1.111"<<std::endl;
   CreatePlistSrc_Dest(src_dest_plist,temp_source,temp_dest);
   //std::cout<<"Detail Router check point 1.12"<<std::endl;
   grid.ActivePointlist(src_dest_plist);
   //activate src dest
   //std::cout<<"Detail Router check point 1.2"<<std::endl;
   std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > netplist = FindsetPlist(Set_net, gridll, gridur);
   //std::cout<<"Detail Router check point 1.3"<<std::endl;
   grid.InactivePointlist(netplist);//+back
   //std::cout<<"Detail Router check point 2"<<std::endl;
   std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > sym_net_plist;

   if(sym_flag == 1){
     //inactivate the point in the sym part, then recover those node in the end
     CreatePlistSymNets(sym_net_plist, sym_gridll, sym_gridur, Nets[i].sym_H, Nets[i].center, gridll, gridur);
     grid.InactivePointlist(sym_net_plist);
    }

   grid.setSrcDest_detail( temp_source, temp_dest, this->width, this->height, Smap);

   grid.PrepareGraphVertices(gridll.x, gridll.y, gridur.x, gridur.y); //on longer needed seems

};

void GcellDetailRouter::Update_Grid_Src_Dest(Grid &grid, int source_lock, std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > &src_dest_plist, std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest, std::vector<std::vector<RouterDB::Metal> > &physical_path){

       // void InactivePointlist(std::vector< std::set<RouterDB::point, RouterDB::pointXYComp> > &plist);

    if(source_lock==1){
       temp_source.clear();
       //source_lock = 1;
      }

    std::cout<<"Detail Router check point 9"<<std::endl;
    updateSource(physical_path, temp_source);// wbxu: temp_dest might need be appended into temp_source
    grid.InactivateSourceDest();
    grid.InactivePointlist(src_dest_plist);


    for(unsigned int p=0;p<temp_dest.size();p++){
       temp_source.push_back(temp_dest[p]);
      }

};


void GcellDetailRouter::Symmetry_Routing(int sym_flag, int i, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net){

   if(sym_flag==1){

      std::vector<RouterDB::Metal> sym_path = CpSymPath(Nets[i].path_metal, Nets[i].sym_H, Nets[i].center);
      Nets[Nets[i].symCounterpart].path_metal = sym_path;
      std::vector<std::vector<RouterDB::Metal> > Sym_path;
      std::vector<std::vector<RouterDB::point> > sym_add_plist;
      sym_add_plist.resize(this->layerNo);
      Sym_path.push_back(sym_path);
      UpdatePlistNets(Sym_path, sym_add_plist);
      InsertPlistToSet_x(Set_net,sym_add_plist);          

    }

};

void GcellDetailRouter::create_detailrouter(){

   std::vector<std::vector<RouterDB::point> > plist;
   plist.resize( this->layerNo );

   std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x; //block terminal internal metal set
   Generate_Block_Terminal_Internal_Metal_Set(Set_x);

   std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_net; //Net internal metal set

   std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> Pset_via;
   InsertInternalVia(Pset_via, this->Blocks);
   //end initial set
   //start detail router
   //Copy_tile_metals();
   for(unsigned int i=0;i<Nets.size();i++){

        PnRDB::routing_net temp_routing_net; //router report struct  
        Initial_rouer_report_info(temp_routing_net, i);
        int multi_number = R_constraint_based_Parallel_routing_number(i);

        if(Nets[i].path_metal.size()>0){continue;} //if the net has already been routed, then skip
        if(Nets[i].connected.size()<=1){continue;} //if suspending, then skip 

        std::vector<std::vector<RouterDB::SinkData> > temp_pins; //routing pins
        RouterDB::point gridll;
        RouterDB::point gridur;
        RouterDB::point sym_gridll;
        RouterDB::point sym_gridur;
        Grid grid=Generate_Grid_Net(i);//create grid for this net
        Grid_Inactive(grid, Set_x, Set_net, gridll, gridur);//inactive grid on internal metals
        int sym_flag = Found_Pins_and_Symmetry_Pins(grid, i, temp_pins);
        Symmetry_metal_Inactive(i, sym_flag, grid, sym_gridll, sym_gridur, gridll, gridur);

        int source_lock = 0;
        std::vector<RouterDB::SinkData> temp_source = Initial_source_pin(temp_pins,source_lock);//initial source

        std::vector<std::vector<RouterDB::point> > add_plist;// new feasible grid for routed net
        add_plist.resize(this->layerNo);

        Update_rouer_report_info(temp_routing_net, i, 0, 0);

        for(unsigned int j=1;j<temp_pins.size();j++){
            //create dest
            std::vector<RouterDB::SinkData> temp_dest = temp_pins[j];
            std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > src_dest_plist;
            Detailed_router_set_src_dest(grid, temp_source, temp_dest, i, sym_gridll, sym_gridur,gridll, gridur, src_dest_plist, Set_net, sym_flag);
            AddViaSpacing(Pset_via, grid);
            AddViaEnclosure(Pset_via, grid);
            A_star a_star(grid, Nets[i].shielding);
            bool pathMark= a_star.FindFeasiblePath(grid, this->path_number, multi_number, multi_number);
            std::vector<std::vector<RouterDB::Metal> > physical_path;
            Update_rouer_report_info(temp_routing_net, i, j, pathMark);

            //assert(pathMark);
            if(pathMark) {
              InsertRoutingVia(a_star, grid, Pset_via);
              physical_path = a_star.ConvertPathintoPhysical(grid);
              lastmile_source_new(physical_path, temp_source);
              lastmile_dest_new(physical_path, temp_dest);
              returnPath(physical_path, Nets[i]);
            }else{
            std::cout<<"Router-Warning: feasible path might not be found\n";
            }

            std::cout<<"Detail Router check point 8"<<std::endl;
            //update physical path to 
            Update_Grid_Src_Dest(grid, source_lock, src_dest_plist, temp_source,temp_dest, physical_path);
            UpdatePlistNets(physical_path, add_plist);
           }
       Symmetry_Routing(sym_flag, i, Set_net);
       std::cout<<"Detail Router check point 11"<<std::endl;
       InsertPlistToSet_x(Set_net, add_plist);

       temp_report.routed_net.push_back(temp_routing_net);
       //modify_tile_metals(Nets[i], 0);
   }
 };


void GcellDetailRouter::InsertInternalVia(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, std::vector<RouterDB::Block> &Blocks){
  std::pair<int, RouterDB::point> via_point;
  //insert via point into via set
  for (unsigned int bit = 0; bit < Blocks.size(); bit++)
  {
    for (unsigned int vit = 0; vit < Blocks[bit].InternalVia.size();vit++){
      via_point.first = Blocks[bit].InternalVia[vit].model_index;
      via_point.second.x = Blocks[bit].InternalVia[vit].position.x;
      via_point.second.y = Blocks[bit].InternalVia[vit].position.y;
      Pset_via.insert(via_point);
    }
  }
}

void GcellDetailRouter::InsertRoutingVia(A_star& a_star, Grid& grid, std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via){
  //1.get path from a_star
  std::vector<std::vector<int>> path = a_star.GetPath();
  //2.insert via point into via set
  std::pair<int, RouterDB::point> via_point;
  for (std::vector<std::vector<int>>::const_iterator paths_it = path.begin(); paths_it != path.end(); ++paths_it)
  {
    for (std::vector<int>::const_iterator path_it = paths_it->begin(); path_it != paths_it->end();++path_it){
      if(path_it==paths_it->begin())continue;//start from the second vertice
      int mIdx1 = grid.vertices_total[*(path_it - 1)].metal, mIdx2 = grid.vertices_total[*path_it].metal;
      if (mIdx1==mIdx2)continue; //skip vertices in the same layer
      int x1 = grid.vertices_total[*(path_it - 1)].x, y1 = grid.vertices_total[*(path_it - 1)].y;
      int x2 = grid.vertices_total[*path_it].x, y2 = grid.vertices_total[*path_it].y;
      if(x1!=x2 || y1!=y2)continue;//skip when vertices in different location
      via_point.first = std::min(mIdx1, mIdx2);
      via_point.second.x = x1;
      via_point.second.y = y1;
      Pset_via.insert(via_point);
    }
  }
}

void GcellDetailRouter::AddViaEnclosure(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, Grid& grid){
  RouterDB::box box;
  std::vector<std::vector<RouterDB::point> > plist_via_lower_metal(this->layerNo); //points in this list cannot have an upper via
  std::vector<std::vector<RouterDB::point> > plist_via_upper_metal(this->layerNo); //points in this list cannot have a lower via
  //1.convert via point into via spacing box and 
  for (std::set<std::pair<int, RouterDB::point>>::iterator vit = Pset_via.begin(); vit != Pset_via.end();++vit)
  {
    int vIdx = vit->first;    
    if (drc_info.Metal_info[drc_info.Via_info[vIdx].lower_metal_index].direct == 0) //vertical in lower layer
    {
      int mIdx = drc_info.Via_model[vIdx].LowerIdx;
      box.LL.x = vit->second.x + 2 * drc_info.Via_model[vIdx].LowerRect[0].x;
      box.LL.y = vit->second.y + 2 * drc_info.Via_model[vIdx].LowerRect[0].y - drc_info.Metal_info[mIdx].dist_ss;
      box.UR.x = vit->second.x + 2 * drc_info.Via_model[vIdx].LowerRect[1].x;
      box.UR.y = vit->second.y + 2 * drc_info.Via_model[vIdx].LowerRect[1].y + drc_info.Metal_info[mIdx].dist_ss;
      ConvertRect2GridPoints(plist_via_lower_metal, drc_info.Via_model[vIdx].LowerIdx, box.LL.x, box.LL.y, box.UR.x, box.UR.y);
      mIdx = drc_info.Via_model[vIdx].UpperIdx;
      box.LL.x = vit->second.x + 2 * drc_info.Via_model[vIdx].UpperRect[0].x - drc_info.Metal_info[mIdx].dist_ss;
      box.LL.y = vit->second.y + 2 * drc_info.Via_model[vIdx].UpperRect[0].y;
      box.UR.x = vit->second.x + 2 * drc_info.Via_model[vIdx].UpperRect[1].x + drc_info.Metal_info[mIdx].dist_ss;
      box.UR.y = vit->second.y + 2 * drc_info.Via_model[vIdx].UpperRect[1].y;
      ConvertRect2GridPoints(plist_via_upper_metal, drc_info.Via_model[vIdx].UpperIdx, box.LL.x, box.LL.y, box.UR.x, box.UR.y);
    }else if (drc_info.Metal_info[drc_info.Via_info[vIdx].lower_metal_index].direct == 1){//H in lower layer
      int mIdx = drc_info.Via_model[vIdx].LowerIdx;
      box.LL.x = vit->second.x + 2 * drc_info.Via_model[vIdx].LowerRect[0].x - drc_info.Metal_info[mIdx].dist_ss;
      box.LL.y = vit->second.y + 2 * drc_info.Via_model[vIdx].LowerRect[0].y;
      box.UR.x = vit->second.x + 2 * drc_info.Via_model[vIdx].LowerRect[1].x + drc_info.Metal_info[mIdx].dist_ss;
      box.UR.y = vit->second.y + 2 * drc_info.Via_model[vIdx].LowerRect[1].y;
      ConvertRect2GridPoints(plist_via_lower_metal, drc_info.Via_model[vIdx].LowerIdx, box.LL.x, box.LL.y, box.UR.x, box.UR.y);
      mIdx = drc_info.Via_model[vIdx].UpperIdx;
      box.LL.x = vit->second.x + 2 * drc_info.Via_model[vIdx].UpperRect[0].x;
      box.LL.y = vit->second.y + 2 * drc_info.Via_model[vIdx].UpperRect[0].y - drc_info.Metal_info[mIdx].dist_ss;
      box.UR.x = vit->second.x + 2 * drc_info.Via_model[vIdx].UpperRect[1].x;
      box.UR.y = vit->second.y + 2 * drc_info.Via_model[vIdx].UpperRect[1].y + drc_info.Metal_info[mIdx].dist_ss;
      ConvertRect2GridPoints(plist_via_upper_metal, drc_info.Via_model[vIdx].UpperIdx, box.LL.x, box.LL.y, box.UR.x, box.UR.y);
    }
  }
  
  //convert vector into set
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> Pset_via_lower_metal = Plist2Set(plist_via_lower_metal);
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> Pset_via_upper_metal = Plist2Set(plist_via_upper_metal);
  grid.InactivePointlist_via(Pset_via_lower_metal, true); //inactive metal's upper via
  grid.InactivePointlist_via(Pset_via_upper_metal, false); //inactive metal's lower via
};

void GcellDetailRouter::AddViaSpacing(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, Grid& grid){
  RouterDB::box box;
  std::vector<std::vector<RouterDB::point> > plist_via_lower_metal(this->layerNo); //points in this list cannot have an upper via
  std::vector<std::vector<RouterDB::point> > plist_via_upper_metal(this->layerNo); //points in this list cannot have a lower via
  //1.convert via point into via spacing box and 
  for (std::set<std::pair<int, RouterDB::point>>::iterator vit = Pset_via.begin(); vit != Pset_via.end();++vit)
  {
    int vIdx = vit->first;
    box.LL.x = vit->second.x - drc_info.Via_info[vIdx].dist_ss;
    box.LL.y = vit->second.y - drc_info.Via_info[vIdx].dist_ss_y;
    box.UR.x = vit->second.x + drc_info.Via_info[vIdx].dist_ss;
    box.UR.y = vit->second.y + drc_info.Via_info[vIdx].dist_ss_y;
    //and return point list in via's bounding box
    ConvertRect2GridPoints_Via(plist_via_lower_metal, vIdx, box.LL.x, box.LL.y, box.UR.x, box.UR.y);
    ConvertRect2GridPoints_Via(plist_via_upper_metal, vIdx + 1, box.LL.x, box.LL.y, box.UR.x, box.UR.y);
  }

  //convert vector into set
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> Pset_via_lower_metal = Plist2Set(plist_via_lower_metal);
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> Pset_via_upper_metal = Plist2Set(plist_via_upper_metal);
  grid.InactivePointlist_via(Pset_via_lower_metal, true); //inactive metal's upper via
  grid.InactivePointlist_via(Pset_via_upper_metal, false); //inactive metal's lower via
};

void GcellDetailRouter::SinkData_contact(RouterDB::SinkData &temp_contact, RouterDB::contact & result_contact){

  result_contact.metal = temp_contact.metalIdx;
  result_contact.placedLL =temp_contact.coord[0];
  result_contact.placedUR =temp_contact.coord[1];
  //result_contact.originLL =temp_contact.coord[0];
  //result_contact.originUR =temp_contact.coord[1];

};

int GcellDetailRouter::Cover_Contact(RouterDB::SinkData &temp_contact, RouterDB::SinkData &sym_temp_contact, RouterDB::SinkData &cover_contact){

  if(temp_contact.metalIdx == sym_temp_contact.metalIdx){

     int x1=-1;
     int x2=-1;
     int y1=-1;
     int y2=-1;
     cover_contact.metalIdx = temp_contact.metalIdx ;
    
     if( sym_temp_contact.coord[0].x>temp_contact.coord[0].x and sym_temp_contact.coord[0].x<temp_contact.coord[1].x ){
        
          x1 = sym_temp_contact.coord[0].x;

          if(sym_temp_contact.coord[1].x<temp_contact.coord[1].x){
             x2 = sym_temp_contact.coord[1].x;
            }else{
             x2 = temp_contact.coord[1].x;
            }

       }else if(sym_temp_contact.coord[1].x>temp_contact.coord[0].x and sym_temp_contact.coord[1].x<temp_contact.coord[1].x){

          x2 = sym_temp_contact.coord[1].x;

          if(sym_temp_contact.coord[0].x>temp_contact.coord[0].x){
             x1 = sym_temp_contact.coord[0].x;
            }else{
             x1 = temp_contact.coord[0].x;
            }

       }else if(temp_contact.coord[0].x > sym_temp_contact.coord[0].x and temp_contact.coord[0].x < sym_temp_contact.coord[1].x){

          x1 = temp_contact.coord[0].x;

          if(sym_temp_contact.coord[1].x<temp_contact.coord[1].x){
             x2 = sym_temp_contact.coord[1].x;
            }else{
             x2 = temp_contact.coord[1].x;
            }
          
       }else if(temp_contact.coord[1].x > sym_temp_contact.coord[0].x and temp_contact.coord[1].x < sym_temp_contact.coord[1].x){

          x2 = temp_contact.coord[1].x;

          if(sym_temp_contact.coord[0].x>temp_contact.coord[0].x){
             x1 = sym_temp_contact.coord[0].x;
            }else{
             x1 = temp_contact.coord[0].x;
            }
         
       }else{
        
          return 0;
       
       }

     if( sym_temp_contact.coord[0].y>temp_contact.coord[0].y and sym_temp_contact.coord[0].y<temp_contact.coord[1].y ){
        
          y1 = sym_temp_contact.coord[0].y;

          if(sym_temp_contact.coord[1].y<temp_contact.coord[1].y){
             y2 = sym_temp_contact.coord[1].y;
            }else{
             y2 = temp_contact.coord[1].y;
            }

       }else if(sym_temp_contact.coord[1].y>temp_contact.coord[0].y and sym_temp_contact.coord[1].y<temp_contact.coord[1].y){

          y2 = sym_temp_contact.coord[1].y;

          if(sym_temp_contact.coord[0].y>temp_contact.coord[0].y){
             y1 = sym_temp_contact.coord[0].y;
            }else{
             y1 = temp_contact.coord[0].y;
            }

       }else if(temp_contact.coord[0].y > sym_temp_contact.coord[0].y and temp_contact.coord[0].y < sym_temp_contact.coord[1].y){

          y1 = temp_contact.coord[0].y;

          if(sym_temp_contact.coord[1].y<temp_contact.coord[1].y){
             y2 = sym_temp_contact.coord[1].y;
            }else{
             y2 = temp_contact.coord[1].y;
            }
          
       }else if(temp_contact.coord[1].y > sym_temp_contact.coord[0].y and temp_contact.coord[1].y < sym_temp_contact.coord[1].y){

          y2 = temp_contact.coord[1].y;

          if(sym_temp_contact.coord[0].y>temp_contact.coord[0].y){
             y1 = sym_temp_contact.coord[0].y;
            }else{
             y1 = temp_contact.coord[0].y;
            }
         
       }else{
        
          return 0;
       
       }

      if(x1 == -1 or x2 == -1 or y1 == -1 or y2 == -1){
        
           return 0;
 
         }else{

            RouterDB::point temp_point;
            temp_point.x = x1;
            temp_point.y = y1;
            cover_contact.coord.push_back(temp_point);
            temp_point.x = x2;
            temp_point.y = y2;
            cover_contact.coord.push_back(temp_point);
            return 1;

         }


    }else{
       return 0;
    }

};

void GcellDetailRouter::CheckTile(RouterDB::Net &temp_net, GlobalGrid &Gcell){

  std::cout<<"Start check terminals"<<std::endl;
  std::vector<std::pair<int,int> > tile_index = temp_net.STs[temp_net.STindex].path;

  std::cout<<"Tile info"<<std::endl;

  for(unsigned int i=0;i<tile_index.size();i++){

      std::cout<<"Path ( "<<Gcell.tiles_total[tile_index[i].first].x<<" "<<Gcell.tiles_total[tile_index[i].first].y<<" ) ( "<<Gcell.tiles_total[tile_index[i].second].x<<" "<<Gcell.tiles_total[tile_index[i].second].y<<" ) "<<std::endl;
      std::cout<<"Region ( "<<Gcell.tiles_total[tile_index[i].first].x - Gcell.tiles_total[tile_index[i].first].width/2<<" "<<Gcell.tiles_total[tile_index[i].first].y - Gcell.tiles_total[tile_index[i].first].height/2<<" ) ( "<<Gcell.tiles_total[tile_index[i].first].x + Gcell.tiles_total[tile_index[i].first].width/2<<" "<<Gcell.tiles_total[tile_index[i].first].y + Gcell.tiles_total[tile_index[i].first].height/2<<" ) "<<std::endl;
      std::cout<<"Region ( "<<Gcell.tiles_total[tile_index[i].second].x - Gcell.tiles_total[tile_index[i].second].width/2<<" "<<Gcell.tiles_total[tile_index[i].second].y - Gcell.tiles_total[tile_index[i].second].height/2<<" ) ( "<<Gcell.tiles_total[tile_index[i].second].x + Gcell.tiles_total[tile_index[i].second].width/2<<" "<<Gcell.tiles_total[tile_index[i].second].y + Gcell.tiles_total[tile_index[i].second].height/2<<" ) "<<std::endl;

     }

  std::cout<<"Terminal info"<<std::endl;

  for(unsigned int i=0;i<temp_net.connected.size();i++){

      if(temp_net.connected[i].type == RouterDB::TERMINAL and this->isTop){

          std::cout<<"Terminal name "<<  this->Terminals[temp_net.connected [i].iter].name<<std::endl;
          std::cout<<"Terminal region ("<< this->Terminals[temp_net.connected [i].iter].termContacts[0].placedCenter.x<<" "<<this->Terminals[temp_net.connected [i].iter].termContacts[0].placedCenter.y<<" ) "<<std::endl;

        }

     }

  std::cout<<"End check terminals"<<std::endl;



};

void GcellDetailRouter::JudgeTileCoverage(std::vector<std::pair<int,int> > &tile_index, std::vector<std::vector<RouterDB::SinkData> > &temp_pins, GlobalGrid &Gcell){

  std::set<int> unique_set;
  std::set<int>::iterator it,itlow,itup;
  std::vector<int> tiles;

  std::vector<RouterDB::SinkData> tile_range;

  //RouterDB::SinkData temp_sink;
  std::cout<<"Print Gcell Global Path"<<std::endl;

  for(unsigned int i=0;i<tile_index.size();i++){

      unique_set.insert(tile_index[i].first);
      unique_set.insert(tile_index[i].second);
      std::cout<<"Path ( "<<Gcell.tiles_total[tile_index[i].first].x<<" "<<Gcell.tiles_total[tile_index[i].first].y<<" ) ( "<<Gcell.tiles_total[tile_index[i].second].x<<" "<<Gcell.tiles_total[tile_index[i].second].y<<" ) "<<std::endl;
      std::cout<<"Region ( "<<Gcell.tiles_total[tile_index[i].first].x - Gcell.tiles_total[tile_index[i].first].width/2<<" "<<Gcell.tiles_total[tile_index[i].first].y - Gcell.tiles_total[tile_index[i].first].height/2<<" ) ( "<<Gcell.tiles_total[tile_index[i].first].x + Gcell.tiles_total[tile_index[i].first].width/2<<" "<<Gcell.tiles_total[tile_index[i].first].y + Gcell.tiles_total[tile_index[i].first].height/2<<" ) "<<std::endl;
      std::cout<<"Region ( "<<Gcell.tiles_total[tile_index[i].second].x - Gcell.tiles_total[tile_index[i].second].width/2<<" "<<Gcell.tiles_total[tile_index[i].second].y - Gcell.tiles_total[tile_index[i].second].height/2<<" ) ( "<<Gcell.tiles_total[tile_index[i].second].x + Gcell.tiles_total[tile_index[i].second].width/2<<" "<<Gcell.tiles_total[tile_index[i].second].y + Gcell.tiles_total[tile_index[i].second].height/2<<" ) "<<std::endl;

     }

   std::cout<<"End Gcell Global Path"<<std::endl;
  
  itlow = unique_set.begin();
  itup = unique_set.end();
  
  for(it = itlow;it!=itup;it++){
 
     tiles.push_back(*it);
   
     }

  for(unsigned int i=0;i<tiles.size();i++){

      RouterDB::point temp_point;
      RouterDB::SinkData temp_sink;
      temp_point.x = Gcell.tiles_total[tiles[i]].x - Gcell.tiles_total[tiles[i]].width/2;
      temp_point.y = Gcell.tiles_total[tiles[i]].y - Gcell.tiles_total[tiles[i]].height/2;
      temp_sink.coord.push_back(temp_point);
      temp_point.x = Gcell.tiles_total[tiles[i]].x + Gcell.tiles_total[tiles[i]].width/2;
      temp_point.y = Gcell.tiles_total[tiles[i]].y + Gcell.tiles_total[tiles[i]].height/2;
      temp_sink.coord.push_back(temp_point);
      tile_range.push_back(temp_sink);
      
     }

   for(unsigned int i=0;i<temp_pins.size();i++){
       int found_flag = 0;
       for(unsigned int j=0;j<temp_pins[i].size();j++){
           for(unsigned int k=0;k<tile_range.size();k++){

                int tile_found_flag=Tile_Cover_Contact(temp_pins[i][j], tile_range[k]);
                if(tile_found_flag==1){found_flag=1;}

              }
          }
        if(found_flag==0){std::cout<<"Error tile do not cover pins"<<std::endl;}
      } 
  
  
};


int GcellDetailRouter::Tile_Cover_Contact(RouterDB::SinkData &temp_contact, RouterDB::SinkData &sym_temp_contact){

  if(1){

     int x1=-1;
     int x2=-1;
     int y1=-1;
     int y2=-1;
    
     if( sym_temp_contact.coord[0].x>temp_contact.coord[0].x and sym_temp_contact.coord[0].x<temp_contact.coord[1].x ){
        
          x1 = sym_temp_contact.coord[0].x;

          if(sym_temp_contact.coord[1].x<temp_contact.coord[1].x){
             x2 = sym_temp_contact.coord[1].x;
            }else{
             x2 = temp_contact.coord[1].x;
            }

       }else if(sym_temp_contact.coord[1].x>temp_contact.coord[0].x and sym_temp_contact.coord[1].x<temp_contact.coord[1].x){

          x2 = sym_temp_contact.coord[1].x;

          if(sym_temp_contact.coord[0].x>temp_contact.coord[0].x){
             x1 = sym_temp_contact.coord[0].x;
            }else{
             x1 = temp_contact.coord[0].x;
            }

       }else if(temp_contact.coord[0].x > sym_temp_contact.coord[0].x and temp_contact.coord[0].x < sym_temp_contact.coord[1].x){

          x1 = temp_contact.coord[0].x;

          if(sym_temp_contact.coord[1].x<temp_contact.coord[1].x){
             x2 = sym_temp_contact.coord[1].x;
            }else{
             x2 = temp_contact.coord[1].x;
            }
          
       }else if(temp_contact.coord[1].x > sym_temp_contact.coord[0].x and temp_contact.coord[1].x < sym_temp_contact.coord[1].x){

          x2 = temp_contact.coord[1].x;

          if(sym_temp_contact.coord[0].x>temp_contact.coord[0].x){
             x1 = sym_temp_contact.coord[0].x;
            }else{
             x1 = temp_contact.coord[0].x;
            }
         
       }else{
        
          return 0;
       
       }

     if( sym_temp_contact.coord[0].y>temp_contact.coord[0].y and sym_temp_contact.coord[0].y<temp_contact.coord[1].y ){
        
          y1 = sym_temp_contact.coord[0].y;

          if(sym_temp_contact.coord[1].y<temp_contact.coord[1].y){
             y2 = sym_temp_contact.coord[1].y;
            }else{
             y2 = temp_contact.coord[1].y;
            }

       }else if(sym_temp_contact.coord[1].y>temp_contact.coord[0].y and sym_temp_contact.coord[1].y<temp_contact.coord[1].y){

          y2 = sym_temp_contact.coord[1].y;

          if(sym_temp_contact.coord[0].y>temp_contact.coord[0].y){
             y1 = sym_temp_contact.coord[0].y;
            }else{
             y1 = temp_contact.coord[0].y;
            }

       }else if(temp_contact.coord[0].y > sym_temp_contact.coord[0].y and temp_contact.coord[0].y < sym_temp_contact.coord[1].y){

          y1 = temp_contact.coord[0].y;

          if(sym_temp_contact.coord[1].y<temp_contact.coord[1].y){
             y2 = sym_temp_contact.coord[1].y;
            }else{
             y2 = temp_contact.coord[1].y;
            }
          
       }else if(temp_contact.coord[1].y > sym_temp_contact.coord[0].y and temp_contact.coord[1].y < sym_temp_contact.coord[1].y){

          y2 = temp_contact.coord[1].y;

          if(sym_temp_contact.coord[0].y>temp_contact.coord[0].y){
             y1 = sym_temp_contact.coord[0].y;
            }else{
             y1 = temp_contact.coord[0].y;
            }
         
       }else{
        
          return 0;
       
       }


      if(x1 == -1 or x2 == -1 or y1 == -1 or y2 == -1){
        
           return 0;
 
         }else{

            return 1;

         }


    }else{
       return 0;
    }

};




std::vector<RouterDB::SinkData> GcellDetailRouter::FindCommon_Contact(std::vector<RouterDB::SinkData> &temp_contact, std::vector<RouterDB::SinkData> &sym_temp_contact, bool H, int center){

  std::vector<RouterDB::SinkData> common_contact;

  for(unsigned int i=0;i<temp_contact.size();i++){

       for(unsigned int j=0;j<sym_temp_contact.size();j++){

              RouterDB::SinkData dummy_contact = Sym_contact(sym_temp_contact[j], H, center);

              RouterDB::SinkData cover_contact;

              int coverage_flag = Cover_Contact(temp_contact[i], dummy_contact, cover_contact);

              if(coverage_flag == 1){

                   common_contact.push_back(cover_contact);

                }

           }

     }

  return common_contact;

};

int GcellDetailRouter::findPins_Sym(Grid& grid, RouterDB::Net &temp_net, RouterDB::Net &sym_temp_net, bool H, int center, std::vector<std::vector<RouterDB::SinkData> > &temp_pins, std::vector<std::vector<RouterDB::SinkData> > &sym_temp_pins ,std::vector<std::vector<RouterDB::SinkData> > &Common_contacts){

  // H 1 (y), V 0 (x)
  // this center is absolute center

  std::cout<<"find Pins check point 1"<<std::endl;  

  temp_pins = findPins_new(grid, temp_net);

  std::cout<<"find Pins check point 2"<<std::endl;  

  sym_temp_pins = findPins_new(grid, sym_temp_net);

  std::cout<<"find Pins check point 3"<<std::endl;

  if(temp_pins.size()==sym_temp_pins.size()){  

    for(unsigned int i=0;i<temp_pins.size();i++){

        std::cout<<"check point 4"<<std::endl;

        std::vector<RouterDB::SinkData> common_contact = FindCommon_Contact(temp_pins[i], sym_temp_pins[i], H, center);

        std::cout<<"common_contact size "<<common_contact.size()<<std::endl;

        std::cout<<"check point 5"<<std::endl;

        if(common_contact.size()>0){

            Common_contacts.push_back(common_contact); 

          }else{

            return 0;

          }
   
       }

    }else{

      return 0;
    
    }

    return 1;



};


std::vector<std::vector<RouterDB::SinkData> > GcellDetailRouter::findPins_new_old(Grid& grid, RouterDB::Net &temp_net){


   std::cout<<"Check point 1"<<std::endl;

   std::vector<std::vector<RouterDB::SinkData> > temp_Pin;

   std::cout<<"connected number "<<temp_net.connected.size()<<std::endl;

   int sum = 0;

   for(unsigned int i=0;i<temp_net.connected.size();i++){

      std::vector<RouterDB::SinkData> temp_contacts;

      if(temp_net.connected[i].type == RouterDB::BLOCK){
         
         unsigned int contact_number = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts.size();

         for(unsigned int j=0;j<contact_number;j++){
            RouterDB::SinkData temp_contact;
            RouterDB::point temp_point;
            temp_point.x = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedLL.x;
            temp_point.y = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedLL.y;
            temp_contact.coord.push_back(temp_point);
            temp_point.x = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedUR.x;
            temp_point.y = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedUR.y;
            temp_contact.coord.push_back(temp_point);
            temp_contact.metalIdx = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].metal;
            temp_contacts.push_back(temp_contact);
            }


        }else if(temp_net.connected[i].type == RouterDB::TERMINAL and this->isTop and this->Terminals.at(temp_net.connected[i].iter).termContacts[0].metal==-1){
         //else if(0){ 

            std::cout<<"Terminal name "<<this->Terminals.at(temp_net.connected[i].iter).name<<std::endl;

            RouterDB::SinkData temp_contact;
            RouterDB::point temp_point;
            temp_point.x=this->Terminals.at(temp_net.connected[i].iter).termContacts[0].placedCenter.x;
            temp_point.y=this->Terminals.at(temp_net.connected[i].iter).termContacts[0].placedCenter.y;
            temp_contact.coord.push_back(temp_point);
            temp_contact.metalIdx = this->lowest_metal; // or -1
            //temp_contacts.push_back(temp_contact);

            std::vector<RouterDB::SinkData> temp_terminals;
            std::vector<RouterDB::SinkData> empty_source_dest;
            std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap;
            temp_terminals.push_back(temp_contact);

            temp_contact.coord.push_back(temp_point);

            std::cout<<"terminal contact infor "<<temp_contact.coord[0].x<<" "<<temp_contact.coord[0].y<<" "<<temp_contact.metalIdx<<std::endl;

            std::vector<RouterDB::contact> Terminal_contact=grid.setSrcDest( temp_terminals, empty_source_dest, this->width, this->height, Smap);

            if(Terminal_contact.size()>0){
                Terminals[temp_net.connected[i].iter].termContacts.clear();
                for(unsigned int k=0;k<Terminal_contact.size();k++){
                    Terminals[temp_net.connected[i].iter].termContacts.push_back(Terminal_contact[k]);
                   }
                std::cout<<"Success in terminals map"<<std::endl;

                int contact_number = Terminals[temp_net.connected[i].iter].termContacts.size();

            for(int j=0;j<contact_number;j++){
               RouterDB::SinkData terminals_temp_contact;
               RouterDB::point temp_point;
               temp_point.x = Terminals[temp_net.connected[i].iter].termContacts[j].placedLL.x;
               temp_point.y = Terminals[temp_net.connected[i].iter].termContacts[j].placedLL.y;
               terminals_temp_contact.coord.push_back(temp_point);
               temp_point.x = Terminals[temp_net.connected[i].iter].termContacts[j].placedUR.x;
               temp_point.y = Terminals[temp_net.connected[i].iter].termContacts[j].placedUR.y;
               terminals_temp_contact.coord.push_back(temp_point);
               terminals_temp_contact.metalIdx = Terminals[temp_net.connected[i].iter].termContacts[j].metal;
               temp_contacts.push_back(terminals_temp_contact);
            }

              }else{

/*
                for(int k=0;k<Terminal_contact.size();k++){
                    Terminals[temp_net.connected[i].iter].termContacts[k].metal = 0;
                   }
*/                
                //temp_contacts.push_back(temp_contact);
                std::cout<<"Error: terminals fails to map"<<std::endl;
                

              }   

        }else if(temp_net.connected[i].type == RouterDB::TERMINAL and this->isTop and this->Terminals.at(temp_net.connected[i].iter).termContacts[0].metal!=-1){
              
               RouterDB::SinkData terminals_temp_contact;
               RouterDB::point temp_point;
               temp_point.x = Terminals[temp_net.connected[i].iter].termContacts[0].placedLL.x;
               temp_point.y = Terminals[temp_net.connected[i].iter].termContacts[0].placedLL.y;
               terminals_temp_contact.coord.push_back(temp_point);
               temp_point.x = Terminals[temp_net.connected[i].iter].termContacts[0].placedUR.x;
               temp_point.y = Terminals[temp_net.connected[i].iter].termContacts[0].placedUR.y;
               terminals_temp_contact.coord.push_back(temp_point);
               terminals_temp_contact.metalIdx = Terminals[temp_net.connected[i].iter].termContacts[0].metal;
               temp_contacts.push_back(terminals_temp_contact);         
           
        }

        temp_Pin.push_back(temp_contacts);
        sum++;

      }

  //std::cout<<
  std::cout<<"Check point 2"<<std::endl;

  return temp_Pin;


};


std::vector<std::vector<RouterDB::SinkData> > GcellDetailRouter::findPins_new(Grid& grid, RouterDB::Net &temp_net){


   std::cout<<"Check point 1"<<std::endl;

   std::vector<std::vector<RouterDB::SinkData> > temp_Pin;

   std::cout<<"connected number "<<temp_net.connected.size()<<std::endl;

   int sum = 0;

   for(unsigned int i=0;i<temp_net.connected.size();i++){

      std::vector<RouterDB::SinkData> temp_contacts;

      if(temp_net.connected[i].type == RouterDB::BLOCK){
         
         unsigned int contact_number = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts.size();

         for(unsigned int j=0;j<contact_number;j++){
            RouterDB::SinkData temp_contact;
            RouterDB::point temp_point;
            temp_point.x = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedLL.x;
            temp_point.y = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedLL.y;
            temp_contact.coord.push_back(temp_point);
            temp_point.x = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedUR.x;
            temp_point.y = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].placedUR.y;
            temp_contact.coord.push_back(temp_point);
            temp_contact.metalIdx = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts[j].metal;
            temp_contacts.push_back(temp_contact);
            } 

        }else if(temp_net.connected[i].type == RouterDB::TERMINAL and this->Terminals.at(temp_net.connected[i].iter).termContacts[0].metal!=-1){


         unsigned int contact_number = this->Terminals.at(temp_net.connected[i].iter).termContacts.size();

         for(unsigned int j=0;j<contact_number;j++){
            RouterDB::SinkData temp_contact;
            RouterDB::point temp_point;
            temp_point.x = this->Terminals.at(temp_net.connected[i].iter).termContacts[j].placedLL.x;
            temp_point.y = this->Terminals.at(temp_net.connected[i].iter).termContacts[j].placedLL.y;
            temp_contact.coord.push_back(temp_point);
            temp_point.x = this->Terminals.at(temp_net.connected[i].iter).termContacts[j].placedUR.x;
            temp_point.y = this->Terminals.at(temp_net.connected[i].iter).termContacts[j].placedUR.y;
            temp_contact.coord.push_back(temp_point);
            temp_contact.metalIdx = this->Terminals.at(temp_net.connected[i].iter).termContacts[j].metal;
            temp_contacts.push_back(temp_contact);
            }       
        }

        temp_Pin.push_back(temp_contacts);
        sum++;

      }

  //std::cout<<
  std::cout<<"Check point 2"<<std::endl;

  return temp_Pin;


};

void GcellDetailRouter::SortPins(std::vector<std::vector<RouterDB::SinkData> > & temp_Pin){

  std::cout<<"start sort pins"<<std::endl;

  std::vector<RouterDB::SinkData> temp_label_point;
  std::vector<int> dis;

  std::cout<<"start sort pins 1"<<std::endl;

  if(temp_Pin.size()==0){return;}

  std::cout<<"start sort pins 1.1"<<std::endl;

  std::cout<<"temp_Pin size "<<temp_Pin.size()<<std::endl;

  temp_label_point = temp_Pin[0];

  std::cout<<"start sort pins 1.2"<<std::endl;

  for(unsigned int i=0;i<temp_Pin.size();i++){
      int temp_dis=INT_MAX;
       for(unsigned int j=0;j<temp_Pin[i].size();j++){
            std::cout<<"temp_Pin coord size "<<temp_Pin[i][j].coord.size()<<std::endl;
            for(unsigned int k=0;k<temp_label_point.size();k++){
               if(abs(temp_Pin[i][j].coord[0].x-temp_label_point[k].coord[0].x)+abs(temp_Pin[i][j].coord[0].y-temp_label_point[k].coord[0].y)<temp_dis){
                   temp_dis = abs(temp_Pin[i][j].coord[0].x-temp_label_point[k].coord[0].x)+abs(temp_Pin[i][j].coord[0].y-temp_label_point[k].coord[0].y);
                 }
               if(abs(temp_Pin[i][j].coord[0].x-temp_label_point[k].coord[1].x)+abs(temp_Pin[i][j].coord[0].y-temp_label_point[k].coord[1].y)<temp_dis){
                   temp_dis = abs(temp_Pin[i][j].coord[0].x-temp_label_point[k].coord[1].x)+abs(temp_Pin[i][j].coord[0].y-temp_label_point[k].coord[1].y);
                 }
               if(abs(temp_Pin[i][j].coord[1].x-temp_label_point[k].coord[1].x)+abs(temp_Pin[i][j].coord[1].y-temp_label_point[k].coord[1].y)<temp_dis){
                   temp_dis = abs(temp_Pin[i][j].coord[1].x-temp_label_point[k].coord[1].x)+abs(temp_Pin[i][j].coord[1].y-temp_label_point[k].coord[1].y);
                 }
               if(abs(temp_Pin[i][j].coord[1].x-temp_label_point[k].coord[0].x)+abs(temp_Pin[i][j].coord[1].y-temp_label_point[k].coord[0].y)<temp_dis){
                   temp_dis = abs(temp_Pin[i][j].coord[1].x-temp_label_point[k].coord[0].x)+abs(temp_Pin[i][j].coord[1].y-temp_label_point[k].coord[0].y);
                 }
               }
          }
       dis.push_back(temp_dis);
     }

   std::cout<<"start sort pins 2"<<std::endl;

   vector<int> index;
   for(unsigned int i=0;i<dis.size();i++){
       index.push_back(i);
      }

   int temp_dist;
   int temp_index;

   std::cout<<"start sort pins 3"<<std::endl;

   for(unsigned int i=0;i<dis.size();i++){
       for(unsigned int j=i+1;j<dis.size();j++){
            if(dis[i]>dis[j]){
               temp_dist=dis[i];
               dis[i] = dis[j];
               dis[j] = temp_dist;
               temp_index = index[i];
               index[i] = index[j];
               index[j] = temp_index;
              }
          }
      }

   std::cout<<"start sort pins 4"<<std::endl;

   std::vector<std::vector<RouterDB::SinkData> > Pin;
   for(unsigned int i=0;i<dis.size();i++){
         Pin.push_back(temp_Pin[index[i]]);
      }

  temp_Pin = Pin;

  std::cout<<"End sort pins"<<std::endl;

};



std::vector<RouterDB::Metal> GcellDetailRouter::findGlobalPath(RouterDB::Net &temp_net){

  std::vector<RouterDB::Metal> temp_metal;
  
  for(unsigned int i=0;i<temp_net.seg.size();i++){

     int chosenCand = temp_net.seg[i].chosenCand;
     if(chosenCand==-1) {continue;}
     for(unsigned int j=0;j<temp_net.seg[i].candis[chosenCand].metals.size();j++){

          temp_metal.push_back(temp_net.seg[i].candis[chosenCand].metals[j]);

        }
     
     }
  
  return temp_metal;

};

void GcellDetailRouter::splitPath(std::vector<std::vector<RouterDB::Metal> > &temp_path, RouterDB::Net& temp_net){

  RouterDB::point temp_point = temp_path[0][0].LinePoint[0];
  int temp_metalIdx = temp_path[0][0].MetalIdx;
  int found_index = -1;

  RouterDB::point Lpoint;
  RouterDB::point Upoint;

  for(unsigned int i = 0;i<temp_net.path_metal.size();i++){


      if(temp_net.path_metal[i].LinePoint[0].x ==temp_net.path_metal[i].LinePoint[1].x){
         
         if(temp_net.path_metal[i].LinePoint[0].y<=temp_net.path_metal[i].LinePoint[1].y){
             Lpoint = temp_net.path_metal[i].LinePoint[0];
             Upoint = temp_net.path_metal[i].LinePoint[1];
           }else{
             Lpoint = temp_net.path_metal[i].LinePoint[1];
             Upoint = temp_net.path_metal[i].LinePoint[0];
           }
        
         }else{

         if(temp_net.path_metal[i].LinePoint[0].x<=temp_net.path_metal[i].LinePoint[1].x){
             Lpoint = temp_net.path_metal[i].LinePoint[0];
             Upoint = temp_net.path_metal[i].LinePoint[1];
           }else{
             Lpoint = temp_net.path_metal[i].LinePoint[1];
             Upoint = temp_net.path_metal[i].LinePoint[0];
           }

         }


      if(temp_metalIdx ==temp_net.path_metal[i].MetalIdx and temp_point.x>Lpoint.x and temp_point.x<Upoint.x and temp_point.y==Lpoint.y and temp_point.y==Upoint.y){
          
          found_index = i;
          break;
        
         }

      if(temp_metalIdx ==temp_net.path_metal[i].MetalIdx and temp_point.x==Lpoint.x and temp_point.x==Upoint.x and temp_point.y>Lpoint.y and temp_point.y<Upoint.y){
          found_index = i;
          break;
         }
     
     }

  if(found_index!=-1){
       
         RouterDB::point End_point = temp_net.path_metal[found_index].LinePoint[1];         
         temp_net.path_metal[found_index].LinePoint[1] = temp_point;
         RouterDB::Metal temp_metal;
         temp_metal.MetalIdx = temp_net.path_metal[found_index].MetalIdx;
         temp_metal.LinePoint.push_back(temp_point);
         temp_metal.LinePoint.push_back(End_point);
         temp_metal.width = drc_info.Metal_info[temp_metalIdx].width;
         temp_net.path_metal.insert(temp_net.path_metal.begin()+found_index+1,temp_metal);
     
     }

};


void GcellDetailRouter::lastmile_source_new(std::vector<std::vector<RouterDB::Metal> > &temp_path, std::vector<RouterDB::SinkData> &temp_source){

  RouterDB::point temp_point = temp_path[0][0].LinePoint[0];
  int temp_metal_metalidx = temp_path[0][0].MetalIdx;
  //int temp_metal_metalidx = 5;
  int point_flag = 0; // 0 is ll, 1 is ur

  RouterDB::point source_point;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for(unsigned int i =0;i<temp_source.size();i++){
     
     if(temp_source[i].coord[0].x<=temp_source[i].coord[1].x and temp_source[i].coord[0].y<=temp_source[i].coord[1].y){}else{std::cout<<"EEroor"<<std::endl;} 
       
     if(temp_point.x>=temp_source[i].coord[0].x and temp_point.y>=temp_source[i].coord[0].y and temp_point.x<=temp_source[i].coord[1].x and temp_point.y<=temp_source[i].coord[1].y and temp_source[i].metalIdx == temp_metal_metalidx){connected = 1;}

     if(abs(temp_source[i].coord[0].x - temp_point.x)+abs(temp_source[i].coord[0].y - temp_point.y)<dis and temp_source[i].metalIdx == temp_metal_metalidx){
         dis = abs(temp_source[i].coord[0].x - temp_point.x)+abs(temp_source[i].coord[0].y - temp_point.y);
         source_point = temp_source[i].coord[0];
         point_flag = 0;
         }



     if(abs(temp_source[i].coord[1].x - temp_point.x)+abs(temp_source[i].coord[1].y - temp_point.y)<dis and temp_source[i].metalIdx == temp_metal_metalidx){
         dis = abs(temp_source[i].coord[1].x - temp_point.x)+abs(temp_source[i].coord[1].y - temp_point.y);
         source_point = temp_source[i].coord[1];
         point_flag = 1;
         }

     }

  if(point_flag == 1){
      source_point.x = source_point.x - drc_info.Metal_info[temp_metal_metalidx].width/2;
      source_point.y = source_point.y - drc_info.Metal_info[temp_metal_metalidx].width/2;
    }else{
      source_point.x = source_point.x + drc_info.Metal_info[temp_metal_metalidx].width/2;
      source_point.y = source_point.y + drc_info.Metal_info[temp_metal_metalidx].width/2;
    }


  if(connected == 0){

      std::cout<<"source unconnected"<<std::endl;
      std::cout<<"Source point ("<<source_point.x<<" "<<source_point.y<<")"<<std::endl;
      std::cout<<"Dest point ("<<temp_point.x<<" "<<temp_point.y<<")"<<std::endl;      
    
      RouterDB::Metal temp_metal;
      temp_metal.MetalIdx = temp_metal_metalidx;
      //temp_metal.MetalIdx = 5;
      temp_metal.width = drc_info.Metal_info[temp_metal_metalidx].width;

      if(drc_info.Metal_info[temp_metal_metalidx].direct == 0){//v
          if(temp_point.x == source_point.x){
           temp_metal.LinePoint.push_back(source_point); 
           temp_metal.LinePoint.push_back(temp_point);
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].begin(),temp_metal);
           std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl;
            }else{

           temp_metal.LinePoint.push_back(source_point); 
           if(source_point.x>temp_point.x){source_point.x = temp_point.x-drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.x = temp_point.x+drc_info.Metal_info[temp_metal_metalidx].width/2;}
           temp_metal.LinePoint.push_back(source_point);
    
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].begin(),temp_metal);
           std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl;

           temp_metal.LinePoint.clear();
           source_point.x = temp_point.x;
           temp_metal.LinePoint.push_back(source_point);
           temp_metal.LinePoint.push_back(temp_point);
           temp_path[0].insert(temp_path[0].begin()+1,temp_metal); 
           
            }
        }else{

          if(temp_point.y == source_point.y){
           temp_metal.LinePoint.push_back(source_point); 
           temp_metal.LinePoint.push_back(temp_point);
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].begin(),temp_metal);
           std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl;
            }else{

           temp_metal.LinePoint.push_back(source_point); 
           if(source_point.y>temp_point.y){source_point.y = temp_point.y-drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.y = temp_point.y+drc_info.Metal_info[temp_metal_metalidx].width/2;}
           temp_metal.LinePoint.push_back(source_point);
    
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].begin(),temp_metal);
           std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl;

           temp_metal.LinePoint.clear();
           source_point.y = temp_point.y;
           temp_metal.LinePoint.push_back(source_point);
           temp_metal.LinePoint.push_back(temp_point);
           temp_path[0].insert(temp_path[0].begin()+1,temp_metal); 
           
            }

        }
     
    }

};


void GcellDetailRouter::lastmile_dest_new(std::vector<std::vector<RouterDB::Metal> > &temp_path, std::vector<RouterDB::SinkData> &temp_source){

  int last_index = temp_path[0].size()-1;
  RouterDB::point temp_point = temp_path[0][last_index].LinePoint[1];
  int temp_metal_metalidx = temp_path[0][last_index].MetalIdx;
  //int temp_metal_metalidx = 6;

  RouterDB::point source_point;
  int point_flag = 0;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for(unsigned int i =0;i<temp_source.size();i++){
     
     if(temp_source[i].coord[0].x<=temp_source[i].coord[1].x and temp_source[i].coord[0].y<=temp_source[i].coord[1].y){}else{std::cout<<"EEroor"<<std::endl;}  
       
     if(temp_point.x>=temp_source[i].coord[0].x and temp_point.y>=temp_source[i].coord[0].y and temp_point.x<=temp_source[i].coord[1].x and temp_point.y<=temp_source[i].coord[1].y and temp_source[i].metalIdx == temp_metal_metalidx){connected = 1;}

     if(abs(temp_source[i].coord[0].x - temp_point.x)+abs(temp_source[i].coord[0].y - temp_point.y)<dis and temp_source[i].metalIdx == temp_metal_metalidx){
         dis = abs(temp_source[i].coord[0].x - temp_point.x)+abs(temp_source[i].coord[0].y - temp_point.y);
         source_point = temp_source[i].coord[0];
         point_flag = 0;
         }

     if(abs(temp_source[i].coord[1].x - temp_point.x)+abs(temp_source[i].coord[1].y - temp_point.y)<dis and temp_source[i].metalIdx == temp_metal_metalidx){
         dis = abs(temp_source[i].coord[1].x - temp_point.x)+abs(temp_source[i].coord[1].y - temp_point.y);
         source_point = temp_source[i].coord[1];
         point_flag = 1;
         }

     }

  if(point_flag == 1){
      source_point.x = source_point.x - drc_info.Metal_info[temp_metal_metalidx].width/2;
      source_point.y = source_point.y - drc_info.Metal_info[temp_metal_metalidx].width/2;
    }else{
      source_point.x = source_point.x + drc_info.Metal_info[temp_metal_metalidx].width/2;
      source_point.y = source_point.y + drc_info.Metal_info[temp_metal_metalidx].width/2;
    }

  RouterDB::point exch_point = source_point;
  source_point = temp_point;
  temp_point = exch_point;


  if(connected == 0){
      
      //std::cout<<"Dest unconnected"<<std::endl;

      std::cout<<"Dest unconnected"<<std::endl;
      std::cout<<"Source point ("<<source_point.x<<" "<<source_point.y<<")"<<std::endl;
      std::cout<<"Dest point ("<<temp_point.x<<" "<<temp_point.y<<")"<<std::endl;

      RouterDB::Metal temp_metal;
      temp_metal.MetalIdx = temp_metal_metalidx;
      //temp_metal.MetalIdx = 6;
      temp_metal.width = drc_info.Metal_info[temp_metal_metalidx].width;
      //temp_metal.LinePoint.push_back(source_point);

      if(drc_info.Metal_info[temp_metal_metalidx].direct == 0){//v

          if(source_point.x==temp_point.x){
           temp_metal.LinePoint.push_back(source_point); 
           temp_metal.LinePoint.push_back(temp_point);
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].end(),temp_metal);
           int last_end_index = temp_path[0].size()-1;
        std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
            }else{
           temp_metal.LinePoint.push_back(source_point); 
           if(source_point.y>temp_point.y){source_point.y = temp_point.y-drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.y = temp_point.y+drc_info.Metal_info[temp_metal_metalidx].width/2;}
           temp_metal.LinePoint.push_back(source_point);
    
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].end(),temp_metal);
           temp_metal.LinePoint.clear();
           source_point.y = temp_point.y;
           temp_metal.LinePoint.push_back(source_point);
           temp_metal.LinePoint.push_back(temp_point);
           temp_path[0].insert(temp_path[0].end(),temp_metal);
           int last_end_index = temp_path[0].size()-1;
        std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
           


            }          

        }else{

          if(source_point.y==temp_point.y){
           temp_metal.LinePoint.push_back(source_point); 
           temp_metal.LinePoint.push_back(temp_point);
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].end(),temp_metal);
           int last_end_index = temp_path[0].size()-1;
        std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
            }else{
           temp_metal.LinePoint.push_back(source_point); 
           if(source_point.x>temp_point.x){source_point.x = temp_point.x-drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.x = temp_point.x+drc_info.Metal_info[temp_metal_metalidx].width/2;}
           temp_metal.LinePoint.push_back(source_point);
    
           std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
           temp_path[0].insert(temp_path[0].end(),temp_metal);
           temp_metal.LinePoint.clear();
           source_point.x = temp_point.x;
           temp_metal.LinePoint.push_back(source_point);
           temp_metal.LinePoint.push_back(temp_point);
           temp_path[0].insert(temp_path[0].end(),temp_metal);
           int last_end_index = temp_path[0].size()-1;
        std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
           


            }   

        }


    }

};


void GcellDetailRouter::UpdateVia(RouterDB::Via &temp_via){

  //ViaRect
  temp_via.ViaRect.metal = temp_via.model_index;
  temp_via.ViaRect.placedCenter = temp_via.position;
  temp_via.ViaRect.placedLL.x = drc_info.Via_model[temp_via.model_index].ViaRect[0].x + temp_via.position.x;
  temp_via.ViaRect.placedLL.y = drc_info.Via_model[temp_via.model_index].ViaRect[0].y + temp_via.position.y;
  temp_via.ViaRect.placedUR.x = drc_info.Via_model[temp_via.model_index].ViaRect[1].x + temp_via.position.x;
  temp_via.ViaRect.placedUR.y = drc_info.Via_model[temp_via.model_index].ViaRect[1].y + temp_via.position.y;
  //LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Via_model[temp_via.model_index].LowerIdx;
  temp_via.LowerMetalRect.placedCenter = temp_via.position;
  temp_via.LowerMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].LowerRect[0].x + temp_via.position.x;
  temp_via.LowerMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].LowerRect[0].y + temp_via.position.y;
  temp_via.LowerMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].LowerRect[1].x + temp_via.position.x;
  temp_via.LowerMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].LowerRect[1].y + temp_via.position.y;
  //UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Via_model[temp_via.model_index].UpperIdx;
  temp_via.UpperMetalRect.placedCenter = temp_via.position;
  temp_via.UpperMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].UpperRect[0].x + temp_via.position.x;
  temp_via.UpperMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].UpperRect[0].y + temp_via.position.y;
  temp_via.UpperMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].UpperRect[1].x + temp_via.position.x;
  temp_via.UpperMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].UpperRect[1].y + temp_via.position.y;
  

};

void GcellDetailRouter::updateSource(std::vector<std::vector<RouterDB::Metal> > &temp_path, std::vector<RouterDB::SinkData>& temp_source){

  RouterDB::SinkData temp_sink;
  int width = 1;

  unsigned int prime_path;
  if((int)temp_path.size()>0){
      prime_path = 1;
     }else{
      prime_path = 0;
     }

  for(unsigned int i=0;i<prime_path;i++){

     for(unsigned int j=0;j<temp_path[i].size();j++){
           temp_sink.coord.clear();
           temp_sink.metalIdx = temp_path[i][j].MetalIdx;
           RouterDB::point Lpoint;
           RouterDB::point Upoint;
           
           RouterDB::point spoint;
           RouterDB::point epoint;
           spoint = temp_path[i][j].LinePoint[0];
           epoint = temp_path[i][j].LinePoint[1];
           
           if(spoint.x == epoint.x){
             
              if(spoint.y<=epoint.y){
                 Lpoint.x = spoint.x - width;
                 Lpoint.y = spoint.y;
                 Upoint.x = epoint.x + width;
                 Upoint.y = epoint.y;
                }else{
                 Lpoint.x = epoint.x - width;
                 Lpoint.y = epoint.y;
                 Upoint.x = spoint.x + width;
                 Upoint.y = spoint.y;                 
                }
             
             }else{

              if(spoint.x<=epoint.x){
                 Lpoint.x = spoint.x;
                 Lpoint.y = spoint.y - width;
                 Upoint.x = epoint.x;
                 Upoint.y = epoint.y + width;
                }else{
                 Lpoint.x = epoint.x;
                 Lpoint.y = epoint.y - width;
                 Upoint.x = spoint.x;
                 Upoint.y = spoint.y + width;                
                }
             
             }

           temp_sink.coord.push_back(Lpoint);
           temp_sink.coord.push_back(Upoint);
           temp_source.push_back(temp_sink);          

        }
     
     }

};

void GcellDetailRouter::returnPath(std::vector<std::vector<RouterDB::Metal> > &temp_path, RouterDB::Net& temp_net){

  for(unsigned int i=0;i<temp_path.size();i++){
       
     for(unsigned int j=0;j<temp_path[i].size();j++){
         if(j==0 or j==temp_path[i].size()-1){
           temp_net.extend_label.push_back(0);
         }else{
           temp_net.extend_label.push_back(1);
         }
         temp_net.path_metal.push_back(temp_path[i][j]);
     
        }
     }

};



void GcellDetailRouter::Physical_metal_via(){
  
   for(unsigned int i=0;i<Nets.size();i++){
             
           GetPhsical_Metal_Via(i);
     
      }

};

void GcellDetailRouter::UpdateMetalContact(RouterDB::Metal &temp_metal){

  temp_metal.MetalRect.metal = temp_metal.MetalIdx;
  temp_metal.MetalRect.placedCenter.x = (temp_metal.LinePoint[0].x+temp_metal.LinePoint[1].x)/2;
  temp_metal.MetalRect.placedCenter.y = (temp_metal.LinePoint[0].y+temp_metal.LinePoint[1].y)/2;

  if(temp_metal.LinePoint[0].y==temp_metal.LinePoint[1].y){

     if(temp_metal.LinePoint[0].x<temp_metal.LinePoint[1].x){
        temp_metal.MetalRect.placedLL.x =  temp_metal.LinePoint[0].x;
        temp_metal.MetalRect.placedLL.y =  temp_metal.LinePoint[0].y-temp_metal.width/2;
        temp_metal.MetalRect.placedUR.x =  temp_metal.LinePoint[1].x;
        temp_metal.MetalRect.placedUR.y =  temp_metal.LinePoint[1].y+temp_metal.width/2;
     }else{
        temp_metal.MetalRect.placedLL.x =  temp_metal.LinePoint[1].x;
        temp_metal.MetalRect.placedLL.y =  temp_metal.LinePoint[1].y-temp_metal.width/2;
        temp_metal.MetalRect.placedUR.x =  temp_metal.LinePoint[0].x;
        temp_metal.MetalRect.placedUR.y =  temp_metal.LinePoint[0].y+temp_metal.width/2;
     }

  }else{

     if(temp_metal.LinePoint[0].y<temp_metal.LinePoint[1].y){               
        temp_metal.MetalRect.placedLL.x =  temp_metal.LinePoint[0].x-temp_metal.width/2;;
        temp_metal.MetalRect.placedLL.y =  temp_metal.LinePoint[0].y;
        temp_metal.MetalRect.placedUR.x =  temp_metal.LinePoint[1].x+temp_metal.width/2;;
        temp_metal.MetalRect.placedUR.y =  temp_metal.LinePoint[1].y;  
       }else{
        temp_metal.MetalRect.placedLL.x =  temp_metal.LinePoint[1].x-temp_metal.width/2;;
        temp_metal.MetalRect.placedLL.y =  temp_metal.LinePoint[1].y;
        temp_metal.MetalRect.placedUR.x =  temp_metal.LinePoint[0].x+temp_metal.width/2;;
        temp_metal.MetalRect.placedUR.y =  temp_metal.LinePoint[0].y;
       }
  }

};

void GcellDetailRouter::ExtendX(RouterDB::Metal &temp_metal, int extend_dis){

  //extend
  if(temp_metal.LinePoint[0].x<temp_metal.LinePoint[1].x){

     temp_metal.LinePoint[0].x = temp_metal.LinePoint[0].x - extend_dis;
     temp_metal.LinePoint[1].x = temp_metal.LinePoint[1].x + extend_dis;
     //rewrite contact

    }else{

     temp_metal.LinePoint[0].x = temp_metal.LinePoint[0].x + extend_dis;
     temp_metal.LinePoint[1].x = temp_metal.LinePoint[1].x - extend_dis;

    }

    UpdateMetalContact(temp_metal);
  
};

void GcellDetailRouter::ExtendY(RouterDB::Metal &temp_metal, int extend_dis){

  //extend
  if(temp_metal.LinePoint[0].y<temp_metal.LinePoint[1].y){

     temp_metal.LinePoint[0].y = temp_metal.LinePoint[0].y - extend_dis;
     temp_metal.LinePoint[1].y = temp_metal.LinePoint[1].y + extend_dis;
     //rewrite contact

    }else{

     temp_metal.LinePoint[0].y = temp_metal.LinePoint[0].y + extend_dis;
     temp_metal.LinePoint[1].y = temp_metal.LinePoint[1].y - extend_dis;

    }

    UpdateMetalContact(temp_metal);
  
};

void GcellDetailRouter::ExtendMetal(){


  for(unsigned int i=0;i<Nets.size();i++){

     if(Nets[i].path_metal.size()!=Nets[i].extend_label.size()){assert(0);}

     for(unsigned int j=0;j<Nets[i].path_metal.size();j++){

         if(Nets[i].extend_label[j]==0){continue;}

         int current_metal = Nets[i].path_metal[j].MetalIdx;

         int direction = drc_info.Metal_info[current_metal].direct;

         int minL = drc_info.Metal_info[current_metal].minL;
         
         int current_length = abs( Nets[i].path_metal[j].LinePoint[0].x - Nets[i].path_metal[j].LinePoint[1].x) + abs( Nets[i].path_metal[j].LinePoint[0].y - Nets[i].path_metal[j].LinePoint[1].y);

         if(current_length<minL){

            int extend_dis = ceil(minL - current_length)/2;
   
            if(direction==1){//h
             
               ExtendX(Nets[i].path_metal[j], extend_dis);
               
            }else{//v
              
               ExtendY(Nets[i].path_metal[j], extend_dis);
              
            }


         }
     }
  }


};


void GcellDetailRouter::GetPhsical_Metal_Via(int i){
  
  for(unsigned int h=0;h<Nets[i].path_metal.size();h++){

      Nets[i].path_metal[h].MetalRect.metal =  Nets[i].path_metal[h].MetalIdx;
      Nets[i].path_metal[h].MetalRect.placedCenter.x =( Nets[i].path_metal[h].LinePoint[0].x+Nets[i].path_metal[h].LinePoint[1].x)/2;
      Nets[i].path_metal[h].MetalRect.placedCenter.y =( Nets[i].path_metal[h].LinePoint[0].y+Nets[i].path_metal[h].LinePoint[1].y)/2; 

         if(Nets[i].path_metal[h].LinePoint[0].y==Nets[i].path_metal[h].LinePoint[1].y){          
            if(Nets[i].path_metal[h].LinePoint[0].x<Nets[i].path_metal[h].LinePoint[1].x){
              Nets[i].path_metal[h].MetalRect.placedLL.x =  Nets[i].path_metal[h].LinePoint[0].x;
              Nets[i].path_metal[h].MetalRect.placedLL.y =  Nets[i].path_metal[h].LinePoint[0].y-Nets[i].path_metal[h].width/2;
              Nets[i].path_metal[h].MetalRect.placedUR.x =  Nets[i].path_metal[h].LinePoint[1].x;
              Nets[i].path_metal[h].MetalRect.placedUR.y =  Nets[i].path_metal[h].LinePoint[1].y+Nets[i].path_metal[h].width/2;
              }else{
              Nets[i].path_metal[h].MetalRect.placedLL.x =  Nets[i].path_metal[h].LinePoint[1].x;
              Nets[i].path_metal[h].MetalRect.placedLL.y =  Nets[i].path_metal[h].LinePoint[1].y-Nets[i].path_metal[h].width/2;
              Nets[i].path_metal[h].MetalRect.placedUR.x =  Nets[i].path_metal[h].LinePoint[0].x;
              Nets[i].path_metal[h].MetalRect.placedUR.y =  Nets[i].path_metal[h].LinePoint[0].y+Nets[i].path_metal[h].width/2;
              }
            }else{
              if(Nets[i].path_metal[h].LinePoint[0].y<Nets[i].path_metal[h].LinePoint[1].y){               
              Nets[i].path_metal[h].MetalRect.placedLL.x =  Nets[i].path_metal[h].LinePoint[0].x-Nets[i].path_metal[h].width/2;;
              Nets[i].path_metal[h].MetalRect.placedLL.y =  Nets[i].path_metal[h].LinePoint[0].y;
              Nets[i].path_metal[h].MetalRect.placedUR.x =  Nets[i].path_metal[h].LinePoint[1].x+Nets[i].path_metal[h].width/2;;
              Nets[i].path_metal[h].MetalRect.placedUR.y =  Nets[i].path_metal[h].LinePoint[1].y;  
                }else{
              Nets[i].path_metal[h].MetalRect.placedLL.x =  Nets[i].path_metal[h].LinePoint[1].x-Nets[i].path_metal[h].width/2;;
              Nets[i].path_metal[h].MetalRect.placedLL.y =  Nets[i].path_metal[h].LinePoint[1].y;
              Nets[i].path_metal[h].MetalRect.placedUR.x =  Nets[i].path_metal[h].LinePoint[0].x+Nets[i].path_metal[h].width/2;;
              Nets[i].path_metal[h].MetalRect.placedUR.y =  Nets[i].path_metal[h].LinePoint[0].y;
                }
            }

         if(Nets[i].path_metal[h].LinePoint[0].y==Nets[i].path_metal[h].LinePoint[1].y and Nets[i].path_metal[h].LinePoint[0].x==Nets[i].path_metal[h].LinePoint[1].x){          
           
              Nets[i].path_metal[h].MetalRect.placedLL.x =  Nets[i].path_metal[h].LinePoint[0].x-Nets[i].path_metal[h].width/2;
              Nets[i].path_metal[h].MetalRect.placedLL.y =  Nets[i].path_metal[h].LinePoint[0].y-Nets[i].path_metal[h].width/2;
              Nets[i].path_metal[h].MetalRect.placedUR.x =  Nets[i].path_metal[h].LinePoint[1].x+Nets[i].path_metal[h].width/2;
              Nets[i].path_metal[h].MetalRect.placedUR.y =  Nets[i].path_metal[h].LinePoint[1].y+Nets[i].path_metal[h].width/2;
            
            }

          
     }

  
  std::vector<RouterDB::Via> Vias;
  RouterDB::Via temp_via;
  std::set<RouterDB::Via, RouterDB::ViaComp> set_via;

  for(unsigned int h=0;h<Nets[i].path_metal.size();h++){
       int temp_metal_index = Nets[i].path_metal[h].MetalIdx;
       for(unsigned int l=0;l<Nets[i].path_metal.size();l++){

            int next_metal_index = Nets[i].path_metal[l].MetalIdx;

            if(l==h){continue;}

            if(temp_metal_index == next_metal_index -1){
                
                if(Nets[i].path_metal[h].LinePoint[0].x==Nets[i].path_metal[l].LinePoint[0].x and Nets[i].path_metal[h].LinePoint[0].y==Nets[i].path_metal[l].LinePoint[0].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[0];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(Nets[i].path_metal[h].LinePoint[0].x==Nets[i].path_metal[l].LinePoint[1].x and Nets[i].path_metal[h].LinePoint[0].y==Nets[i].path_metal[l].LinePoint[1].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[0];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(Nets[i].path_metal[h].LinePoint[1].x==Nets[i].path_metal[l].LinePoint[0].x and Nets[i].path_metal[h].LinePoint[1].y==Nets[i].path_metal[l].LinePoint[0].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[1];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(Nets[i].path_metal[h].LinePoint[1].x==Nets[i].path_metal[l].LinePoint[1].x and Nets[i].path_metal[h].LinePoint[1].y==Nets[i].path_metal[l].LinePoint[1].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[1];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }
                
              }
           
          }         

     }

  std::set<RouterDB::Via, RouterDB::ViaComp>::iterator via_begin, via_end, via_it;
  via_begin = set_via.begin();
  via_end = set_via.end();

  for(via_it=via_begin;via_it!=via_end;++via_it){
      Nets[i].path_via.push_back(*via_it);
     }

};


void GcellDetailRouter::CreatePlistSymBlocks(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > &set_plist, RouterDB::point gridll, RouterDB::point gridur, int H, int center, RouterDB::point symgridll, RouterDB::point symgridur){

  //RouterDB::point tmpP;
  std::vector<RouterDB::contact> Contacts;
  std::vector<RouterDB::contact> Sym_Contacts;
  std::vector<std::vector<RouterDB::point> > plist;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x;
  //std::vector<RouterDB::point>
  int LLx, LLy, URx, URy;

  auto push_contact = [&](auto & temp_contact){

       LLx=temp_contact.placedLL.x;
       LLy=temp_contact.placedLL.y;
       URx=temp_contact.placedUR.x;
       URy=temp_contact.placedUR.y;
        
       if(!(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y)){
           Contacts.push_back(temp_contact);
         }

  };

  for(std::vector<RouterDB::Block>::iterator bit=Blocks.begin(); bit!=Blocks.end(); ++bit) {
    // 1. collect pin contacts on grids
    for(std::vector<RouterDB::Pin>::iterator pit=bit->pins.begin(); pit!=bit->pins.end(); ++pit) {
      for(std::vector<RouterDB::contact>::iterator cit=pit->pinContacts.begin(); cit!=pit->pinContacts.end(); ++cit) {
         push_contact(*cit);
      }
      for(std::vector<RouterDB::Via>::iterator cit=pit->pinVias.begin(); cit!=pit->pinVias.end(); ++cit) {
         push_contact(cit->UpperMetalRect);
         push_contact(cit->LowerMetalRect);
      }
    }
    // 2. collect internal metals on grids
    for(std::vector<RouterDB::contact>::iterator pit=bit->InternalMetal.begin(); pit!=bit->InternalMetal.end(); ++pit) {
        //std::cout<<"check point createplistBlocks 4.0 "<<std::endl;
        push_contact(*pit);
        //std::cout<<"check point createplistBlocks 4.5 "<<std::endl;
    }
    for(std::vector<RouterDB::Via>::iterator pit=bit->InternalVia.begin(); pit!=bit->InternalVia.end(); ++pit) {
        push_contact(pit->UpperMetalRect);
        push_contact(pit->LowerMetalRect);

    }

  }

  for(unsigned int i=0;i<Contacts.size();i++){

        RouterDB::contact temp_sym_contact = SymContact(Contacts[i], H, center);

        Sym_Contacts.push_back(temp_sym_contact);

     }    

   CreatePlistContact(plist, Sym_Contacts);
   InsertPlistToSet_x(Set_x, plist);
   set_plist = FindsetPlist(Set_x, symgridll, symgridur);

};

RouterDB::contact GcellDetailRouter::SymContact(RouterDB::contact &temp_contact, bool H, int center){

  RouterDB::contact sym_contact;
  sym_contact.metal = temp_contact.metal;
  RouterDB::point LL_point;
  RouterDB::point UR_point;
  RouterDB::point temp_point;
  RouterDB::point temp_point1;
  RouterDB::point temp_point2;

  if(H==0){

     temp_point1 = temp_contact.placedLL;
     temp_point1.x = 2*center - temp_point1.x;
     temp_point2 = temp_contact.placedUR;
     temp_point2.x = 2*center - temp_point2.x;
     temp_point.y = temp_point1.y;
     temp_point1.y = temp_point2.y;
     temp_point2.y = temp_point.y;
     sym_contact.placedLL=temp_point2;
     sym_contact.placedUR=temp_point1;

    }else{

     temp_point1 = temp_contact.placedLL;
     temp_point1.y = 2*center - temp_point1.y;
     temp_point2 = temp_contact.placedUR;
     temp_point2.y = 2*center - temp_point2.y;
     temp_point.x = temp_point1.x;
     temp_point1.x = temp_point2.x;
     temp_point2.x = temp_point.x;
     sym_contact.placedLL = temp_point2;
     sym_contact.placedUR = temp_point1;


    }

  return sym_contact;

};

RouterDB::SinkData GcellDetailRouter::Sym_contact(RouterDB::SinkData &temp_contact, bool H, int center){

  RouterDB::SinkData sym_contact;
  sym_contact.metalIdx = temp_contact.metalIdx;
  RouterDB::point LL_point;
  RouterDB::point UR_point;
  RouterDB::point temp_point;
  RouterDB::point temp_point1;
  RouterDB::point temp_point2;

  if(H==0){

     temp_point1 = temp_contact.coord[0];
     temp_point1.x = 2*center - temp_point1.x;
     temp_point2 = temp_contact.coord[1];
     temp_point2.x = 2*center - temp_point2.x;
     temp_point.y = temp_point1.y;
     temp_point1.y = temp_point2.y;
     temp_point2.y = temp_point.y;
     sym_contact.coord.push_back(temp_point2);
     sym_contact.coord.push_back(temp_point1);

    }else{

     temp_point1 = temp_contact.coord[0];
     temp_point1.y = 2*center - temp_point1.y;
     temp_point2 = temp_contact.coord[1];
     temp_point2.y = 2*center - temp_point2.y;
     temp_point.x = temp_point1.x;
     temp_point1.x = temp_point2.x;
     temp_point2.x = temp_point.x;
     sym_contact.coord.push_back(temp_point2);
     sym_contact.coord.push_back(temp_point1);


    }

  return sym_contact;

};


void GcellDetailRouter::CreatePlistContact(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::contact>& Contacts){
  
  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;

  for(std::vector<RouterDB::contact>::iterator cit = Contacts.begin();cit!=Contacts.end(); ++cit){
     
        mIdx=cit->metal;
        LLx=cit->placedLL.x;
        LLy=cit->placedLL.y;
        URx=cit->placedUR.x;
        URy=cit->placedUR.y;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);

     }

};

void GcellDetailRouter::CreatePlistSingleContact(std::vector<std::vector<RouterDB::point> >& plist, RouterDB::contact& Contacts){
  
  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;

  {
     mIdx=Contacts.metal;
     LLx=Contacts.placedLL.x;
     LLy=Contacts.placedLL.y;
     URx=Contacts.placedUR.x;
     URy=Contacts.placedUR.y;
     ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);

   }

};



void GcellDetailRouter::CreatePlistBlocks(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Block>& Blocks){
  
  //RouterDB::point tmpP;
  //int mIdx, LLx, LLy, URx, URy;
  for(std::vector<RouterDB::Block>::iterator bit=Blocks.begin(); bit!=Blocks.end(); ++bit) {
    // 1. collect pin contacts on grids
    for(std::vector<RouterDB::Pin>::iterator pit=bit->pins.begin(); pit!=bit->pins.end(); ++pit) {
      for(std::vector<RouterDB::contact>::iterator cit=pit->pinContacts.begin(); cit!=pit->pinContacts.end(); ++cit) {
        CreatePlistSingleContact(plist,*cit);
      }
      for(std::vector<RouterDB::Via>::iterator cit=pit->pinVias.begin(); cit!=pit->pinVias.end(); ++cit) {
        CreatePlistSingleContact(plist,cit->UpperMetalRect);
        CreatePlistSingleContact(plist,cit->LowerMetalRect);
      }
    }
    // 2. collect internal metals on grids
    for(std::vector<RouterDB::contact>::iterator pit=bit->InternalMetal.begin(); pit!=bit->InternalMetal.end(); ++pit) {
        //std::cout<<"check point createplistBlocks 4.0 "<<std::endl;
        CreatePlistSingleContact(plist,*pit);
    }
    for(std::vector<RouterDB::Via>::iterator pit=bit->InternalVia.begin(); pit!=bit->InternalVia.end(); ++pit) {
        CreatePlistSingleContact(plist,pit->UpperMetalRect);
        CreatePlistSingleContact(plist,pit->LowerMetalRect);
    }
  }  

};



void GcellDetailRouter::CreatePlistTerminals(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::terminal> &Terminals){
  
  //RouterDB::point tmpP;
  //int mIdx, LLx, LLy, URx, URy;
  int mIdx;
  for(unsigned int i=0;i<Terminals.size();i++){
      for(unsigned int j=0;j<Terminals[i].termContacts.size();j++){
          mIdx = Terminals[i].termContacts[j].metal;
          if(mIdx>=0){
             CreatePlistSingleContact(plist, Terminals[i].termContacts[j]);
           }
         }
     }

};


void GcellDetailRouter::UpdatePlistNets(std::vector<std::vector<RouterDB::Metal> > &physical_path, std::vector<std::vector<RouterDB::point> > &plist){


  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;
  
  GetPhsical_Metal(physical_path);
  
  //here intervia is not included
  for(unsigned int i=0;i<physical_path.size();i++){
      for(unsigned int j=0;j<physical_path[i].size();j++){
          mIdx = physical_path[i][j].MetalIdx;
          LLx = physical_path[i][j].MetalRect.placedLL.x;
          LLy = physical_path[i][j].MetalRect.placedLL.y;
          URx = physical_path[i][j].MetalRect.placedUR.x;
          URy = physical_path[i][j].MetalRect.placedUR.y;

          int direction = drc_info.Metal_info[mIdx].direct;
          int minL = drc_info.Metal_info[mIdx].minL;

          if(direction==1){ //h

          if( (URx-LLx)<minL ){

              int extend_dis = ceil(minL- (URx-LLx))/2;
              LLx = LLx - extend_dis;
              URx = URx + extend_dis;
            }

            }else{//v

            if( (URy-LLy)<minL ){

              int extend_dis = ceil(minL- (URy-LLy))/2;
              LLy = LLy - extend_dis;
              URy = URy + extend_dis;
           }

  }


          ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
         }
     }

  std::vector<RouterDB::contact> temp_via_contact;
  GetPhsical_Via_contacts(physical_path, temp_via_contact);

  for(unsigned int i=0;i<temp_via_contact.size();i++){
        CreatePlistSingleContact(plist, temp_via_contact[i]);
     }


  

};

void GcellDetailRouter::GetPhsical_Via_contacts(std::vector<std::vector<RouterDB::Metal> >&physical_path, std::vector<RouterDB::contact> &temp_via_contact){


  RouterDB::Via temp_via;
  std::set<RouterDB::Via, RouterDB::ViaComp> set_via;

  for(unsigned int i=0;i<physical_path.size();i++){
       
      std::vector<RouterDB::Metal> temp_path = physical_path[i];

      for(unsigned int j=0;j<temp_path.size();j++){

           int temp_metal_index = temp_path[j].MetalIdx;
           
           for(unsigned int h=0;h<temp_path.size();h++){

               int next_metal_index = temp_path[h].MetalIdx;

               if(j==h){continue;}

               if(temp_metal_index == next_metal_index -1){
                
                if(temp_path[j].LinePoint[0].x==temp_path[h].LinePoint[0].x and temp_path[j].LinePoint[0].y==temp_path[h].LinePoint[0].y){
                  temp_via.position = temp_path[j].LinePoint[0];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(temp_path[j].LinePoint[0].x==temp_path[h].LinePoint[1].x and temp_path[j].LinePoint[0].y==temp_path[h].LinePoint[1].y){
                  temp_via.position = temp_path[j].LinePoint[0];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(temp_path[j].LinePoint[1].x==temp_path[h].LinePoint[0].x and temp_path[j].LinePoint[1].y==temp_path[h].LinePoint[0].y){
                  temp_via.position = temp_path[j].LinePoint[1];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(temp_path[j].LinePoint[1].x==temp_path[h].LinePoint[1].x and temp_path[j].LinePoint[1].y==temp_path[h].LinePoint[1].y){
                  temp_via.position = temp_path[j].LinePoint[1];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }                

                }
              }
         }

     }


  std::set<RouterDB::Via, RouterDB::ViaComp>::iterator via_begin, via_end, via_it;
  via_begin = set_via.begin();
  via_end = set_via.end();

  for(via_it=via_begin;via_it!=via_end;++via_it){
      
      temp_via_contact.push_back(via_it->UpperMetalRect);
      temp_via_contact.push_back(via_it->LowerMetalRect);

     }

};


void GcellDetailRouter::CreatePlistSrc_Dest(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > &src_dest_plist, std::vector<RouterDB::SinkData > &temp_src, std::vector<RouterDB::SinkData > &temp_dest){


  //RouterDB::point tmpP;
  int LLx, LLy, URx, URy;

  std::vector<RouterDB::contact> Contacts;
  RouterDB::contact temp_contact;
  //RouterDB::point tmpP;
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize( this->layerNo );
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x; 
  RouterDB::point ll;
  RouterDB::point ur;
  //RouterDB::contact temp_contact;
  ll.x = INT_MAX;
  ll.y = INT_MAX;

  ur.x = INT_MIN;
  ur.y = INT_MIN;

  std::cout<<"check point new function 1 "<<std::endl;

  //change sinkdata to contact
  std::cout<<"src contact "<<temp_src.size()<<std::endl;
  for(int i=0;i<temp_src.size();i++){
    SinkData_contact(temp_src[i], temp_contact);
    Contacts.push_back(temp_contact);
    if(temp_contact.placedLL.x<ll.x){ll.x=temp_contact.placedLL.x;}
    if(temp_contact.placedLL.y<ll.y){ll.y=temp_contact.placedLL.y;}
    if(temp_contact.placedUR.x>ur.x){ur.x=temp_contact.placedUR.x;}
    if(temp_contact.placedUR.y>ur.y){ur.y=temp_contact.placedUR.y;}
  }
  std::cout<<"check point new function 2 "<<std::endl;
 std::cout<<"dest contact "<<temp_dest.size()<<std::endl;
  for(int i=0;i<temp_dest.size();i++){
    SinkData_contact(temp_dest[i], temp_contact);
    Contacts.push_back(temp_contact);
    if(temp_contact.placedLL.x<ll.x){ll.x=temp_contact.placedLL.x;}
    if(temp_contact.placedLL.y<ll.y){ll.y=temp_contact.placedLL.y;}
    if(temp_contact.placedUR.x>ur.x){ur.x=temp_contact.placedUR.x;}
    if(temp_contact.placedUR.y>ur.y){ur.y=temp_contact.placedUR.y;}

  }  
  std::cout<<"check point new function 3 "<<std::endl;

  std::cout<<"Contacts size "<<Contacts.size()<<std::endl;
   CreatePlistContact(plist, Contacts);
  //here intervia is not included
  std::cout<<"check point new function 4 "<<std::endl;
   InsertPlistToSet_x(Set_x, plist);
  std::cout<<"check point new function 5 "<<std::endl;
   src_dest_plist = FindsetPlist(Set_x, ll, ur);
  std::cout<<"check point new function 6 "<<std::endl;
};


void GcellDetailRouter::CreatePlistSymNets(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > &set_plist, RouterDB::point gridll, RouterDB::point gridur, bool H, int center, RouterDB::point symgridll, RouterDB::point symgridur){


  //RouterDB::point tmpP;
  int LLx, LLy, URx, URy;

  std::vector<RouterDB::contact> Contacts;
  std::vector<RouterDB::contact> Sym_Contacts; 
  //RouterDB::point tmpP;
  std::vector<std::vector<RouterDB::point> > plist;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x; 

  auto push_contact = [&](auto & temp_contact){

       LLx=temp_contact.placedLL.x;
       LLy=temp_contact.placedLL.y;
       URx=temp_contact.placedUR.x;
       URy=temp_contact.placedUR.y;
        
       if(!(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y)){
           Contacts.push_back(temp_contact);
         }

  };

  for(unsigned int k=0;k<Nets.size();k++){  
    
      std::vector<std::vector<RouterDB::Metal> > physical_path;
      physical_path.push_back(Nets[k].path_metal); 
      GetPhsical_Metal(physical_path);
      
      for(unsigned int i=0;i<physical_path.size();i++){
         for(unsigned int j=0;j<physical_path[i].size();j++){
             push_contact(physical_path[i][j].MetalRect);
            }
        }

      std::vector<RouterDB::contact> temp_via_contact;
      GetPhsical_Via_contacts(physical_path, temp_via_contact);
      
      for(unsigned int i=0;i<temp_via_contact.size();i++){
           push_contact(temp_via_contact[i]);
         }
      

     }
    
  for(unsigned int i=0;i<Contacts.size();i++){

        RouterDB::contact temp_sym_contact = SymContact(Contacts[i], H, center);

        Sym_Contacts.push_back(temp_sym_contact);

     }    

   CreatePlistContact(plist, Sym_Contacts);
  //here intervia is not included

   InsertPlistToSet_x(Set_x, plist);
   set_plist = FindsetPlist(Set_x, symgridll, symgridur);

  

};

void GcellDetailRouter::GetPhsical_Metal(std::vector<std::vector<RouterDB::Metal> > &physical_path){

  //via is not included here
  for(unsigned int i=0;i<physical_path.size();i++){
       for(unsigned int j=0;j<physical_path[i].size();j++){
            if(drc_info.Metal_info[physical_path[i][j].MetalIdx].direct == 1){
              if(physical_path[i][j].LinePoint[0].x<=physical_path[i][j].LinePoint[1].x){
                physical_path[i][j].MetalRect.placedLL.x =  physical_path[i][j].LinePoint[0].x;
                physical_path[i][j].MetalRect.placedLL.y =  physical_path[i][j].LinePoint[0].y-physical_path[i][j].width/2;
                physical_path[i][j].MetalRect.placedUR.x =  physical_path[i][j].LinePoint[1].x;
                physical_path[i][j].MetalRect.placedUR.y =  physical_path[i][j].LinePoint[1].y+physical_path[i][j].width/2;
                }else{
                physical_path[i][j].MetalRect.placedLL.x =  physical_path[i][j].LinePoint[1].x;
                physical_path[i][j].MetalRect.placedLL.y =  physical_path[i][j].LinePoint[1].y-physical_path[i][j].width/2;
                physical_path[i][j].MetalRect.placedUR.x =  physical_path[i][j].LinePoint[0].x;
                physical_path[i][j].MetalRect.placedUR.y =  physical_path[i][j].LinePoint[0].y+physical_path[i][j].width/2;
                }
             }else{
              if(physical_path[i][j].LinePoint[0].y<=physical_path[i][j].LinePoint[1].y){
                physical_path[i][j].MetalRect.placedLL.x =  physical_path[i][j].LinePoint[0].x-physical_path[i][j].width/2;
                physical_path[i][j].MetalRect.placedLL.y =  physical_path[i][j].LinePoint[0].y;
                physical_path[i][j].MetalRect.placedUR.x =  physical_path[i][j].LinePoint[1].x+physical_path[i][j].width/2;
                physical_path[i][j].MetalRect.placedUR.y =  physical_path[i][j].LinePoint[1].y;
                }else{
                physical_path[i][j].MetalRect.placedLL.x =  physical_path[i][j].LinePoint[1].x-physical_path[i][j].width/2;
                physical_path[i][j].MetalRect.placedLL.y =  physical_path[i][j].LinePoint[1].y;
                physical_path[i][j].MetalRect.placedUR.x =  physical_path[i][j].LinePoint[0].x+physical_path[i][j].width/2;
                physical_path[i][j].MetalRect.placedUR.y =  physical_path[i][j].LinePoint[0].y;
                }
             }
          }
     }

};


void GcellDetailRouter::ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  RouterDB::point tmpP;
  int obs_l=0;
  int obs_h=this->layerNo-1;
  std::cout<<"Enter converter"<<std::endl;

  if(drc_info.Metal_info[mIdx].direct==0) { // vertical metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_x;
    int newLLx=LLx-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    int newURx=URx+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundX=(newLLx%curlayer_unit==0) ? (newLLx+curlayer_unit) : ( (newLLx/curlayer_unit)*curlayer_unit<newLLx ? (newLLx/curlayer_unit+1)*curlayer_unit : (newLLx/curlayer_unit)*curlayer_unit  );
    for(int x=boundX; x<newURx; x+=curlayer_unit) {
      if(mIdx!=obs_l) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_y;

        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );

        int newLLy=LLy-drc_info.Metal_info.at(mIdx).dist_ee;
        int newURy=URy+drc_info.Metal_info.at(mIdx).dist_ee;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        int boundY=floor((double)newLLy/nexlayer_unit)*nexlayer_unit;
        //int boundY=ceil((double)newLLy/nexlayer_unit)*nexlayer_unit;
        newURy=ceil((double)newURy/nexlayer_unit)*nexlayer_unit;
        std::cout<<"converter check point 1"<<std::endl;
        for(int y=boundY; y<=newURy; y+=nexlayer_unit) {
          if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             std::cout<<"Plist problem"<<std::endl;
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_y;

        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );

        int newLLy=LLy-drc_info.Metal_info.at(mIdx).dist_ee;
        int newURy=URy+drc_info.Metal_info.at(mIdx).dist_ee;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        int boundY=floor((double)newLLy/nexlayer_unit)*nexlayer_unit;
        //int boundY=ceil((double)newLLy/nexlayer_unit)*nexlayer_unit;
        newURy=ceil((double)newURy/nexlayer_unit)*nexlayer_unit;
        std::cout<<"converter check point 2"<<std::endl;
        for(int y=boundY; y<=newURy; y+=nexlayer_unit) {
          if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else if(drc_info.Metal_info[mIdx].direct==1) { // horizontal metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_y;
    int newLLy=LLy-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    int newURy=URy+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundY=(newLLy%curlayer_unit==0) ? (newLLy+curlayer_unit) : ( (newLLy/curlayer_unit)*curlayer_unit<newLLy ? (newLLy/curlayer_unit+1)*curlayer_unit : (newLLy/curlayer_unit)*curlayer_unit  );
    for(int y=boundY; y<newURy; y+=curlayer_unit) {
      if(mIdx!=obs_l) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_x;

        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );

        int newLLx=LLx-drc_info.Metal_info.at(mIdx).dist_ee;
        int newURx=URx+drc_info.Metal_info.at(mIdx).dist_ee;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        int boundX=floor((double)newLLx/nexlayer_unit)*nexlayer_unit;
        //int boundX=ceil((double)newLLx/nexlayer_unit)*nexlayer_unit;
        newURx=ceil((double)newURx/nexlayer_unit)*nexlayer_unit;
         std::cout<<"converter check point 3"<<std::endl;
        for(int x=boundX; x<=newURx; x+=nexlayer_unit) {
           if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
           //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_x;

        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );

        int newLLx=LLx-drc_info.Metal_info.at(mIdx).dist_ee;
        int newURx=URx+drc_info.Metal_info.at(mIdx).dist_ee;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        int boundX=floor((double)newLLx/nexlayer_unit)*nexlayer_unit;
        //int boundX=ceil((double)newLLx/nexlayer_unit)*nexlayer_unit;
        newURx=ceil((double)newURx/nexlayer_unit)*nexlayer_unit;
        std::cout<<"converter check point 4"<<std::endl;
        for(int x=boundX; x<=newURx; x+=nexlayer_unit) {
          if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else {
    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
  }

};

void GcellDetailRouter::ConvertRect2GridPoints_Via(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  RouterDB::point tmpP;
  int obs_l=0;
  int obs_h=this->layerNo-1;
  std::cout<<"Enter converter"<<std::endl;
  //int direction = drc_info.Metal_info[mIdx].direct;

  if(drc_info.Metal_info[mIdx].direct==0) { // vertical metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_x;
    int newLLx=LLx;
    int newURx=URx;
    int boundX=ceil((double)newLLx/curlayer_unit)*curlayer_unit;
    for(int x=boundX; x<newURx; x+=curlayer_unit) {
      if(mIdx!=obs_l) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_y;

        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );

        int newLLy=LLy;
        int newURy=URy;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        //int boundY=floor((double)newLLy/nexlayer_unit)*nexlayer_unit;
        int boundY=ceil((double)newLLy/nexlayer_unit)*nexlayer_unit;
        //newURy=ceil((double)newURy/nexlayer_unit)*nexlayer_unit;
        std::cout<<"converter check point 1"<<std::endl;
        for(int y=boundY; y<=newURy; y+=nexlayer_unit) {
          if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             std::cout<<"Plist problem"<<std::endl;
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_y;

        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );

        int newLLy=LLy;
        int newURy=URy;
        //int boundY=(newLLy%nexlayer_unit==0) ? (newLLy) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        //int boundY=floor((double)newLLy/nexlayer_unit)*nexlayer_unit;
        int boundY=ceil((double)newLLy/nexlayer_unit)*nexlayer_unit;
        //newURy=ceil((double)newURy/nexlayer_unit)*nexlayer_unit;
        std::cout<<"converter check point 2"<<std::endl;
        for(int y=boundY; y<=newURy; y+=nexlayer_unit) {
          if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else if(drc_info.Metal_info[mIdx].direct==1) { // horizontal metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_y;
    int newLLy=LLy;
    int newURy=URy;
    int boundY=ceil((double)newLLy/curlayer_unit)*curlayer_unit;
    for(int y=boundY; y<newURy; y+=curlayer_unit) {
      if(mIdx!=obs_l) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_x;

        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );

        int newLLx=LLx;
        int newURx=URx;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        //int boundX=floor((double)newLLx/nexlayer_unit)*nexlayer_unit;
        int boundX=ceil((double)newLLx/nexlayer_unit)*nexlayer_unit;
        //newURx=ceil((double)newURx/nexlayer_unit)*nexlayer_unit;
         std::cout<<"converter check point 3"<<std::endl;
        for(int x=boundX; x<=newURx; x+=nexlayer_unit) {
           if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
           //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_x;

        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );

        int newLLx=LLx;
        int newURx=URx;
        //int boundX=(newLLx%nexlayer_unit==0) ? (newLLx) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        //int boundX=floor((double)newLLx/nexlayer_unit)*nexlayer_unit;
        int boundX=ceil((double)newLLx/nexlayer_unit)*nexlayer_unit;
        //newURx=ceil((double)newURx/nexlayer_unit)*nexlayer_unit;
        std::cout<<"converter check point 4"<<std::endl;
        for(int x=boundX; x<=newURx; x+=nexlayer_unit) {
          if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else {
    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
  }

};

void GcellDetailRouter::NetToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index){
  PnRDB::point tpoint;  

  //including via
  //std::cout<<"Start NetToNodeNet"<<std::endl;
  
  for(unsigned int i=0;i<net.path_metal.size();i++){

             PnRDB::Metal temp_metal;
             temp_metal.MetalIdx = net.path_metal[i].MetalIdx;
             temp_metal.width = net.path_metal[i].width;
             //std::cout<<"checkpoint 1"<<std::endl;
             tpoint.x = net.path_metal[i].LinePoint[0].x;
             tpoint.y = net.path_metal[i].LinePoint[0].y;
             temp_metal.LinePoint.push_back(tpoint);
             tpoint.x = net.path_metal[i].LinePoint[1].x;
             tpoint.y = net.path_metal[i].LinePoint[1].y;
             temp_metal.LinePoint.push_back(tpoint);
             temp_metal.MetalRect.metal = drc_info.Metal_info[net.path_metal[i].MetalRect.metal].name;
             //std::cout<<"checkpoint 2"<<std::endl;
             temp_metal.MetalRect.placedBox.LL.x = net.path_metal[i].MetalRect.placedLL.x;
             temp_metal.MetalRect.placedBox.LL.y = net.path_metal[i].MetalRect.placedLL.y;
             temp_metal.MetalRect.placedBox.UR.x = net.path_metal[i].MetalRect.placedUR.x;
             temp_metal.MetalRect.placedBox.UR.y = net.path_metal[i].MetalRect.placedUR.y;
             temp_metal.MetalRect.placedCenter.x = net.path_metal[i].MetalRect.placedCenter.x;
             temp_metal.MetalRect.placedCenter.y = net.path_metal[i].MetalRect.placedCenter.y;
             //std::cout<<"checkpoint 3"<<std::endl;
             HierNode.Nets[net_index].path_metal.push_back(temp_metal);

     }

  for(unsigned int i=0;i<net.path_via.size();i++){
       PnRDB::Via temp_via;
       ConvertToViaPnRDB_Placed_Placed(temp_via,net.path_via[i]);
       HierNode.Nets[net_index].path_via.push_back(temp_via);
     }

};



void GcellDetailRouter::NetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::Net& net){
  //std::cout<<"Start NetToNodeInterMetal"<<std::endl;
  //blockspin to intermetal
  for(unsigned int i=0;i<net.connected.size();i++){
      if(net.connected[i].type == RouterDB::BLOCK){
          
          for(unsigned int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size();j++){

             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
             HierNode.interMetals.push_back(temp_contact);

             }
          for(unsigned int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size();j++){
             
             PnRDB::Via temp_via;
ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
             HierNode.interVias.push_back(temp_via);
             }
        } 
     }

  //std::cout<<"Via"<<std::endl;
  //including via
  for(unsigned int i=0;i<net.path_metal.size();i++){
      //std::cout<<"seg "<<i<<std::endl;
        PnRDB::contact temp_contact;
        ConvertToContactPnRDB_Placed_Origin(temp_contact, net.path_metal[i].MetalRect);
        HierNode.interMetals.push_back(temp_contact);
      }
  for(unsigned int i=0;i<net.path_via.size();i++){
             //std::cout<<"vias "<<j<<std::endl;

       PnRDB::Via temp_via;
       ConvertToViaPnRDB_Placed_Origin(temp_via, net.path_via[i]);
       HierNode.interVias.push_back(temp_via);

      }
          
  //std::cout<<"END par"<<std::endl;
       
};




void GcellDetailRouter::NetToNodeBlockPins(PnRDB::hierNode& HierNode, RouterDB::Net& net){
  std::cout<<"Start NetToNodeBlockPins"<<std::endl;
  // wbxu: when update hierNode data, all the coordinates should be stored into
  // origin fields, NOT placed fields. Because the hierNode data will be checkin back to higher nodes [fixed]
  PnRDB::pin temp_pin;
  //PnRDB::point temp_point;
  // wbxu: the name should be the name of terminal, not the net name! [fixed]
  if(net.terminal_idx==-1) {std::cout<<"Router-Warning: cannot found terminal conntecting to net"<<std::endl; return;}
  temp_pin.name = Terminals.at(net.terminal_idx).name;

  //if(this->isTop)
  if(terminal_routing){

             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Origin(temp_contact,Terminals.at(net.terminal_idx).termContacts[0]);
             temp_pin.pinContacts.push_back(temp_contact);

    }else{

  //blockspin to intermetal
  for(unsigned int i=0;i<net.connected.size();i++){
      if(net.connected[i].type == RouterDB::BLOCK){
          
          for(unsigned int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size();j++){

             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
             temp_pin.pinContacts.push_back(temp_contact);

             }
          for(unsigned int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size();j++){
             
             PnRDB::Via temp_via;
ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
             temp_pin.pinVias.push_back(temp_via);
             }
        } 
     }

  for(unsigned int i=0;i<net.path_metal.size();i++){

             // wbxu: placed field -> origin field [fixed]
      PnRDB::contact temp_contact;
      ConvertToContactPnRDB_Placed_Origin(temp_contact,net.path_metal[i].MetalRect);
      temp_pin.pinContacts.push_back(temp_contact);
     }
  for(unsigned int i=0;i<net.path_via.size();i++){

             // wbxu: placed field -> origin field [fixed]
      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Origin(temp_via, net.path_via[i]);  
      temp_pin.pinVias.push_back(temp_via);
     }
  }         

  HierNode.blockPins.push_back(temp_pin);    
  std::cout<<"END NetToNodeBlockPins"<<std::endl;
};


void GcellDetailRouter::ReturnHierNode(PnRDB::hierNode& HierNode)
{
  HierNode.blockPins.clear();
  HierNode.interMetals.clear();
  HierNode.interVias.clear();

  for(unsigned int i=0;i<HierNode.Terminals.size();i++){
      HierNode.Terminals[i].termContacts.clear();
     }

  for(unsigned int i=0;i<HierNode.Nets.size();i++){
        HierNode.Nets[i].path_metal.clear();
        HierNode.Nets[i].path_via.clear();
     }

  //distinguish those two net
  //std::cout<<"Start ReturnHierNode"<<std::endl;
  for(unsigned int i=0;i<Nets.size();i++){
      std::cout<<i<<" ter? "<<Nets[i].isTerminal<<std::endl;
      if(Nets[i].isTerminal){
  // wbxu: not only nets should be put into NodeBlockPins, but also those pins connected to nets
  // should be put into NodeBlockPins
         //return blockpins
         std::cout<<"test net to block pin: start"<<std::endl;
         NetToNodeBlockPins(HierNode, Nets[i]);
         std::cout<<"test net to block pin: end"<<std::endl;
        
        }else{
  // wbxu: not only nets should be put into NodeInterMetal, but also those pins connected to nets
  // should be put into NodeInterMetal
         //HierNode.interMetals
         std::cout<<"test net to InterMetal: start"<<std::endl;
         NetToNodeInterMetal(HierNode, Nets[i]);
         std::cout<<"test net to InterMetal: end"<<std::endl;
        }
       
       for(unsigned int j=0;j<HierNode.Nets.size();j++){
          if(HierNode.Nets[j].name == Nets[i].netName){
              HierNode.Nets.at(j).path_metal.clear();
              HierNode.Nets.at(j).path_via.clear();
              std::cout<<"test net to net: start"<<std::endl;
              NetToNodeNet(HierNode, Nets[i], j);
              std::cout<<"test net to net: end"<<std::endl;
              break;
            }
          }
     }
  
  //if(isTop==1)
  if(terminal_routing){
    //return terminal to node terminal
    std::cout<<"test terminal to termina: start"<<std::endl;
    TerminalToNodeTerminal(HierNode);
    std::cout<<"test terminal to termina: end"<<std::endl;
    }
  std::cout<<"test blockintermetal to node intermetal: start"<<std::endl;
  BlockInterMetalToNodeInterMetal(HierNode);
  std::cout<<"test blockintermetal to node intermetal: end"<<std::endl;

  HierNode.router_report.push_back(temp_report);
  //std::cout<<"End ReturnHierNode"<<std::endl;
};

void GcellDetailRouter::ConvertToViaPnRDB_Placed_Placed(PnRDB::Via& temp_via, RouterDB::Via& router_via){
  // wbxu: placed field -> origin field [fixed]
  PnRDB::point temp_point;
  temp_via.model_index = router_via.model_index;
  temp_via.placedpos.x = router_via.position.x;
  temp_via.placedpos.y = router_via.position.y;
  //viarect
  temp_via.ViaRect.metal = drc_info.Via_info[router_via.ViaRect.metal].name;
  temp_via.ViaRect.placedBox.LL.x = router_via.ViaRect.placedLL.x;
  temp_via.ViaRect.placedBox.LL.y = router_via.ViaRect.placedLL.y;
  temp_via.ViaRect.placedBox.UR.x = router_via.ViaRect.placedUR.x;
  temp_via.ViaRect.placedBox.UR.y = router_via.ViaRect.placedUR.y;
  temp_via.ViaRect.placedCenter.x = router_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.placedCenter.y = router_via.ViaRect.placedCenter.y; 

  //LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Metal_info[router_via.LowerMetalRect.metal].name;
  temp_via.LowerMetalRect.placedBox.LL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.placedBox.LL.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.placedBox.UR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.placedBox.UR.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.placedCenter.x = router_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.placedCenter.y = router_via.LowerMetalRect.placedCenter.y;

  //UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Metal_info[router_via.UpperMetalRect.metal].name;
  temp_via.UpperMetalRect.placedBox.LL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.placedBox.LL.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.placedBox.UR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.placedBox.UR.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.placedCenter.x = router_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.placedCenter.y = router_via.UpperMetalRect.placedCenter.y;

};

void GcellDetailRouter::ConvertToContactPnRDB_Placed_Origin(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact){

  PnRDB::point temp_point;
  pnr_contact.metal = drc_info.Metal_info[router_contact.metal].name;
  pnr_contact.originBox.LL.x = router_contact.placedLL.x;
  pnr_contact.originBox.LL.y = router_contact.placedLL.y;
  pnr_contact.originBox.UR.x = router_contact.placedUR.x;
  pnr_contact.originBox.UR.y = router_contact.placedUR.y;
  pnr_contact.originCenter.x = router_contact.placedCenter.x;
  pnr_contact.originCenter.y = router_contact.placedCenter.y; 

};

void GcellDetailRouter::ConvertToViaPnRDB_Placed_Origin(PnRDB::Via& temp_via, RouterDB::Via& router_via){
  // wbxu: placed field -> origin field [fixed]
  PnRDB::point temp_point;
  temp_via.model_index = router_via.model_index;
  temp_via.originpos.x = router_via.position.x;
  temp_via.originpos.y = router_via.position.y;
  //viarect
  temp_via.ViaRect.metal = drc_info.Via_info[router_via.ViaRect.metal].name;
  temp_via.ViaRect.originBox.LL.x = router_via.ViaRect.placedLL.x;
  temp_via.ViaRect.originBox.LL.y = router_via.ViaRect.placedLL.y;
  temp_via.ViaRect.originBox.UR.x = router_via.ViaRect.placedUR.x;
  temp_via.ViaRect.originBox.UR.y = router_via.ViaRect.placedUR.y;
  temp_via.ViaRect.originCenter.x = router_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.originCenter.y = router_via.ViaRect.placedCenter.y; 

  //LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Metal_info[router_via.LowerMetalRect.metal].name;
  temp_via.LowerMetalRect.originBox.LL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.originBox.LL.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.originBox.UR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.originBox.UR.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.originCenter.x = router_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.originCenter.y = router_via.LowerMetalRect.placedCenter.y;

  //UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Metal_info[router_via.UpperMetalRect.metal].name;
  temp_via.UpperMetalRect.originBox.LL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.originBox.LL.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.originBox.UR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.originBox.UR.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.originCenter.x = router_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.originCenter.y = router_via.UpperMetalRect.placedCenter.y;

};

void GcellDetailRouter::TerminalToNodeTerminal(PnRDB::hierNode& HierNode){

   //including via
   //includeing blockpin also

  for(unsigned int i=0;i<this->Terminals.size();i++){
       //pins
       for(unsigned int j=0;j<this->Terminals[i].termContacts.size();j++){
             
             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Placed(temp_contact,this->Terminals[i].termContacts[j]);

             HierNode.Terminals[i].termContacts.push_back(temp_contact);
                

          }
      }

       
};

void GcellDetailRouter::BlockInterMetalToNodeInterMetal(PnRDB::hierNode& HierNode){

   //including via
   //includeing blockpin also

  for(unsigned int i=0;i<Blocks.size();i++){

       //InternalMetal
       for(unsigned int j=0;j<Blocks[i].InternalMetal.size();j++){
            //to internal metal
             PnRDB::contact temp_contact;
             ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[i].InternalMetal[j]);
             HierNode.interMetals.push_back(temp_contact);
          }
       //via
       for(unsigned int j=0;j<Blocks[i].InternalVia.size();j++){
            //to interal via
             PnRDB::Via temp_via;
             ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[i].InternalVia[j]);   
             HierNode.interVias.push_back(temp_via); 

          }

     }
   //block pin also becomes internal metal
       
};

void GcellDetailRouter::ConvertToContactPnRDB_Placed_Placed(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact){

  PnRDB::point temp_point;
  if(router_contact.metal<0){router_contact.metal=0;}
  //std::cout<<"terminal check point 1"<<std::endl;
  pnr_contact.metal = drc_info.Metal_info[router_contact.metal].name;
  //std::cout<<"terminal check point 2"<<std::endl;
  pnr_contact.placedBox.LL.x = router_contact.placedLL.x;
  //std::cout<<"terminal check point 3"<<std::endl;
  pnr_contact.placedBox.LL.y = router_contact.placedLL.y;
  pnr_contact.placedBox.UR.x = router_contact.placedUR.x;
  pnr_contact.placedBox.UR.y = router_contact.placedUR.y;
  pnr_contact.placedCenter.x = router_contact.placedCenter.x;
  pnr_contact.placedCenter.y = router_contact.placedCenter.y; 

};

