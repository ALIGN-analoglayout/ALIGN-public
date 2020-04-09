#include "PowerRouter.h"
#include <cmath>

//one : creation of power gird
//create power grid (creation: drc-info; return to node: based on node grid, create source and dest) create once or separately?
  //1. separately, LL, UR and drc_info for different blocks (creation)
  //2. return to power grid data structure in PnRDB, return metal-path with width.
  //3. if locally created, then find it
  //     globally created, need a function to find metal-path in some region for each net
  // ad/disad: globally is sample, but need a function to find it. But can not adjust the grid
  //           locally is not ez, but need to make each power grid consistant with others


//assign source and dest, based on power grid and vdd pin/gnd pin

//detail router for the rest

PowerRouter::PowerRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, int power_grid, int h_skip_factor, int v_skip_factor){
  
  //power_grid 1 create power_grid, 0 power net routing

  if(power_grid == 1){
     std::cout<<"CheckPoint 1"<<std::endl;
     CreatePowerGrid(node, drc_info, Lmetal, Hmetal, h_skip_factor, v_skip_factor);
     std::cout<<"CheckPoint 2"<<std::endl;
     Physical_metal_via_power_grid(Vdd_grid);

     Vdd_grid.name = "vdd";
     for (unsigned int idx = 0; idx < node.PowerNets.size(); ++idx) {
       if ( node.PowerNets[idx].power == 1) {
	 Vdd_grid.name = node.PowerNets[idx].name;
	 break;
       }
     }

     std::cout<<"CheckPoint 3"<<std::endl;
     Physical_metal_via_power_grid(Gnd_grid);

     Gnd_grid.name = "vss";
     for (unsigned int idx = 0; idx < node.PowerNets.size(); ++idx) {
       if ( node.PowerNets[idx].power == 0) {
	 Gnd_grid.name = node.PowerNets[idx].name;
	 break;
       }
     }

     std::cout<<"CheckPoint 4"<<std::endl;
     ReturnPowerGridData(node);   
     std::cout<<"CheckPoint 5"<<std::endl;  
    }else{
     std::cout<<"CheckPoint 6"<<std::endl;
     PowerNetRouter(node, drc_info, Lmetal, Hmetal);
     std::cout<<"CheckPoint 7"<<std::endl;
     Physical_metal_via(); 
     std::cout<<"CheckPoint 8"<<std::endl;
     ExtendMetal();  // need to change this part
     std::cout<<"CheckPoint 8.5"<<std::endl;
     ReturnPowerNetData(node);
     std::cout<<"CheckPoint 9"<<std::endl;
    }
  
};

void PowerRouter::InsertRoutingContact(A_star &a_star, Grid &grid, std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via,
                                             std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &contacts, int net_num){
  //1.Set physical rect
  GetPhsical_Metal_Via(net_num);
  ExtendMetals(net_num);
  //2.insert routing contact
  for (std::vector<RouterDB::Metal>::const_iterator pit = PowerNets[net_num].path_metal.begin(); pit != PowerNets[net_num].path_metal.end(); ++pit)
  {
    RouterDB::SinkData contact;
    RouterDB::point LL, UR;
    LL = pit->MetalRect.placedLL;
    UR = pit->MetalRect.placedUR;
    contact.metalIdx = pit->MetalIdx;
    contact.coord.push_back(LL);
    contact.coord.push_back(UR);
    contacts.insert(contact);
  }
  for (std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp>::const_iterator vit = Pset_via.begin(); vit != Pset_via.end();++vit){
    //do lower contact
    RouterDB::SinkData contact;
    contact.metalIdx = vit->first;
    RouterDB::point LL, UR;
    LL.x = vit->second.x + drc_info.Via_model[vit->first].LowerRect[0].x;
    LL.y = vit->second.y + drc_info.Via_model[vit->first].LowerRect[0].y;
    UR.x = vit->second.x + drc_info.Via_model[vit->first].LowerRect[1].x;
    UR.y = vit->second.y + drc_info.Via_model[vit->first].LowerRect[1].y;
    contact.coord.push_back(LL);
    contact.coord.push_back(UR);
    contacts.insert(contact);
    //do upper contact
    contact.metalIdx = vit->first + 1;
    LL.x = vit->second.x + drc_info.Via_model[vit->first].UpperRect[0].x;
    LL.y = vit->second.y + drc_info.Via_model[vit->first].UpperRect[0].y;
    UR.x = vit->second.x + drc_info.Via_model[vit->first].UpperRect[1].x;
    UR.y = vit->second.y + drc_info.Via_model[vit->first].UpperRect[1].y;
    contact.coord.clear();
    contact.coord.push_back(LL);
    contact.coord.push_back(UR);
    contacts.insert(contact);
  }
};


void PowerRouter::ExtendMetals(int i){


     if(PowerNets[i].path_metal.size()!=PowerNets[i].extend_label.size()){assert(0);}

     for(unsigned int j=0;j<PowerNets[i].path_metal.size();j++){

         if(PowerNets[i].extend_label[j]==0){continue;}

         int current_metal = PowerNets[i].path_metal[j].MetalIdx;

         int direction = drc_info.Metal_info[current_metal].direct;

         int minL = drc_info.Metal_info[current_metal].minL;
         
         int current_length = abs( PowerNets[i].path_metal[j].LinePoint[0].x - PowerNets[i].path_metal[j].LinePoint[1].x) + abs( PowerNets[i].path_metal[j].LinePoint[0].y - PowerNets[i].path_metal[j].LinePoint[1].y);

         if(current_length<minL){

            int extend_dis = ceil(minL - current_length)/2;
   
            if(direction==1){//h
             
               ExtendX(PowerNets[i].path_metal[j], extend_dis);
               
            }else{//v
              
               ExtendY(PowerNets[i].path_metal[j], extend_dis);
              
            }


         }
     }


};

void PowerRouter::ExtendMetal(){


  for(unsigned int i=0;i<PowerNets.size();i++){

     if(PowerNets[i].path_metal.size()!=PowerNets[i].extend_label.size()){assert(0);}

     for(unsigned int j=0;j<PowerNets[i].path_metal.size();j++){

         if(PowerNets[i].extend_label[j]==0){continue;}

         int current_metal = PowerNets[i].path_metal[j].MetalIdx;

         int direction = drc_info.Metal_info[current_metal].direct;

         int minL = drc_info.Metal_info[current_metal].minL;
         
         int current_length = abs( PowerNets[i].path_metal[j].LinePoint[0].x - PowerNets[i].path_metal[j].LinePoint[1].x) + abs( PowerNets[i].path_metal[j].LinePoint[0].y - PowerNets[i].path_metal[j].LinePoint[1].y);

         if(current_length<minL){

            int extend_dis = ceil(minL - current_length)/2;
   
            if(direction==1){//h
             
               ExtendX(PowerNets[i].path_metal[j], extend_dis);
               
            }else{//v
              
               ExtendY(PowerNets[i].path_metal[j], extend_dis);
              
            }


         }
     }
  }


};

void PowerRouter::ExtendX(RouterDB::Metal &temp_metal, int extend_dis){

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

void PowerRouter::ExtendY(RouterDB::Metal &temp_metal, int extend_dis){

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

void PowerRouter::UpdateMetalContact(RouterDB::Metal &temp_metal){

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

//write PowerGrid in top level
//write PowerNet in each level or top level???

void PowerRouter::ReturnInternalMetalContact(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x_contact, int net_num){
  Set_x_contact.clear();
  for (std::vector<RouterDB::Block>::iterator bit = Blocks.begin(); bit != Blocks.end(); ++bit)
  {
    // 1. collect internal metals on grids
    for(std::vector<RouterDB::contact>::iterator pit=bit->InternalMetal.begin(); pit!=bit->InternalMetal.end(); ++pit) {
      Set_x_contact.insert(Contact2Sinkdata(*pit));
    }
    for(std::vector<RouterDB::Via>::iterator pit=bit->InternalVia.begin(); pit!=bit->InternalVia.end(); ++pit) {
      Set_x_contact.insert(Contact2Sinkdata(pit->UpperMetalRect));
      Set_x_contact.insert(Contact2Sinkdata(pit->LowerMetalRect));
    }
    // 2. remove pin contacts from internal metal
    for(std::vector<RouterDB::Pin>::iterator pit=bit->pins.begin(); pit!=bit->pins.end(); ++pit) {
      if (0)
        continue;
      for (std::vector<RouterDB::contact>::iterator cit = pit->pinContacts.begin(); cit != pit->pinContacts.end(); ++cit)
      {
        Set_x_contact.erase(Contact2Sinkdata(*cit));
      }
      for(std::vector<RouterDB::Via>::iterator cit=pit->pinVias.begin(); cit!=pit->pinVias.end(); ++cit) {
        Set_x_contact.erase(Contact2Sinkdata(cit->UpperMetalRect));
        Set_x_contact.erase(Contact2Sinkdata(cit->LowerMetalRect));
      }
    }
  }
};


void PowerRouter::PowerNetRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal){
  GetData(node, drc_info, Lmetal, Hmetal);
  
  // bug missing via space check?
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize( this->layerNo );

  CreatePlistBlocks(plist, this->Blocks);
  CreatePlistTerminals(plist, this->Terminals);
  CreatePlistPowerGrid(plist, this->Vdd_grid);
  CreatePlistPowerGrid(plist, this->Gnd_grid);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x_contact; //Net metal contact set
  InsertPlistToSet_x(Set_x, plist);

  std::vector<std::vector<RouterDB::point> > netplist;
  netplist.resize( this->layerNo );

  CreatePlistPowerNets(netplist, this->PowerNets);
  CreatePlistNets(netplist, this->Nets);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_net;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_net_contact; //Net metal contact set
  InsertPlistToSet_x(Set_net, netplist);

  std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> Pset_via; //via conter and layer info
  InsertInternalVia(Pset_via, this->Blocks);
  //QQQ Vdd_grid Gnd_grid Terminals PowerNets Nets

  for(unsigned int i=0;i<PowerNets.size();i++){

      std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> Pset_current_net_via; //current net via conter and layer info
      std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_current_net_contact; //current Net metal contact set
      ReturnInternalMetalContact(Set_x_contact,i); //get internal metals' contact,first LL, second UR, exclude current net

      for(unsigned int j=0;j<PowerNets[i].pins.size();j++){

           std::vector<std::vector<RouterDB::point> > add_plist;
           add_plist.resize(this->layerNo);

           RouterDB::Pin temp_pin = PowerNets[i].pins[j];
           std::vector<RouterDB::SinkData> temp_source, temp_dest;

           if(Vdd_grid.metals.size()==0 or Gnd_grid.metals.size()==0){
             std::cout<<"Placement Area is too small, no space to create power grid"<<std::endl;
             assert(0);
             //continue;
           }

           if(PowerNets[i].power ==1){
               //Q1
               SetSrcDest(temp_pin, Vdd_grid, temp_source, temp_dest);
              }else{
               SetSrcDest(temp_pin, Gnd_grid, temp_source, temp_dest);
              }

            Grid grid(this->drc_info, this->LL, this->UR, lowest_metal, highest_metal, this->grid_scale);
            grid.Full_Connected_Vertex();
            std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > pinplist = FindsetPlist(Set_x, LL, UR);
            std::cout<<"start inactive plist"<<std::endl;
            grid.InactivePointlist_Power(pinplist);
            std::cout<<"End inactive plist"<<std::endl;
            std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap;
            
            grid.setSrcDest( temp_source, temp_dest, this->width, this->height, Smap);
            grid.ActivateSourceDest();
            std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > netplist = FindsetPlist(Set_net, LL, UR);
            grid.InactivePointlist_Power(netplist);
       
            grid.setSrcDest_detail( temp_source, temp_dest, this->width, this->height, Smap);
            A_star a_star(grid, 0); // no sheilding
            int multi_number = 0;

            AddViaEnclosure(Pset_via, grid, Set_x_contact, Set_net_contact);
            AddViaSpacing(Pset_via, grid);

            bool pathMark = a_star.FindFeasiblePath(grid, this->path_number, multi_number, multi_number);
            std::vector<std::vector<RouterDB::Metal>> physical_path;
            std::cout<<"power routing pathMark "<<pathMark<<std::endl;
            if(pathMark) {

                physical_path=a_star.ConvertPathintoPhysical(grid);
                lastmile_source_new(physical_path,temp_source);
                lastmile_dest_new(physical_path,temp_dest);
                returnPath(physical_path, PowerNets[i]);

                InsertRoutingVia(a_star, grid, Pset_current_net_via);
                InsertRoutingVia(a_star, grid, Pset_via);
                //add path metal to set_current_net_contact
                //add via conatct to set_current_net_contact
                InsertRoutingContact(a_star, grid, Pset_current_net_via, Set_current_net_contact, i);

               }else{
                 std::cout<<"Router-Warning: feasible path might not be found\n";
                 std::cout<<PowerNets[i].netName<<std::endl;
               }
             UpdatePlistNets(physical_path, add_plist);
             InsertPlistToSet_x(Set_net, add_plist);           
             InsertContact2Contact(Set_current_net_contact, Set_net_contact);
         }
     }

};



void PowerRouter::CreatePowerGrid(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, int h_skip_factor, int v_skip_factor){

  std::cout<<"checkpoint1.1"<<std::endl;
  GetData(node, drc_info, Lmetal, Hmetal);
  CreatePowerGridDrc_info( h_skip_factor, v_skip_factor);
  this->drc_info=this->PowerGrid_Drc_info;
  std::cout<<"checkpoint1.2"<<std::endl;
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize( this->layerNo );
  std::cout<<"checkpoint1.2.1"<<std::endl;
  CreatePlistBlocks(plist, this->Blocks);
  std::cout<<"checkpoint1.2.2"<<std::endl;
  CreatePlistNets(plist, this->Nets);
  std::cout<<"checkpoint1.2.3"<<std::endl;
  CreatePlistTerminals(plist, this->Terminals);
  std::cout<<"checkpoint1.2.4"<<std::endl;
  CreatePlistPowerNets(plist, this->PowerNets);
  std::cout<<"checkpoint1.2.5"<<std::endl;
  CreatePlistPowerGrid(plist, this->Vdd_grid);
  std::cout<<"checkpoint1.2.6"<<std::endl;
  CreatePlistPowerGrid(plist, this->Gnd_grid);
  std::cout<<"checkpoint1.2.7"<<std::endl;
  

  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x;
  InsertPlistToSet_x(Set_x, plist);
  std::cout<<"checkpoint1.2.8"<<std::endl;
  
  //how to crate PowerGrid here????
  Grid grid(this->PowerGrid_Drc_info, this->LL, this->UR, lowest_metal, highest_metal, this->grid_scale);//1.pg needs other LL, UR 2. here what is the lowest_metal, highest_metal

  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > netplist = FindsetPlist(Set_x, LL, UR);
  for(int i=0;i<netplist.size();i++){
     std::cout<<"Power inactive node "<<netplist[i].size()<<std::endl;
     if(i==5){
       for(auto it=netplist[i].begin();it!=netplist[i].end();it++){
         std::cout<<"point "<<it->x<<" "<<it->y<<std::endl;
       }
     }
  }

  grid.InactivePointlist_Power(netplist);
  //std::vector<std::vector<RouterDB::point> > new_plist = FindPlist(Set_x, this->LL, this->UR);
  //grid.InactivePointlist(new_plist);
  grid.PrepareGraphVertices(LL.x, LL.y, UR.x, UR.y);

  std::cout<<"Power Grid Info "<<grid.vertices_total.size()<<" "<<grid.vertices_graph.size()<<std::endl;
  //here return a power grid metal information
  bool power_grid = 1;
  std::cout<<"checkpoint1.3"<<std::endl;
  Graph graph(grid, power_grid);
  std::cout<<"checkpoint1.4"<<std::endl;
  Vdd_grid = graph.GetVdd_grid();
  std::cout<<"checkpoint1.5"<<std::endl;
  Gnd_grid = graph.GetGnd_grid();
  std::cout<<"checkpoint1.6"<<std::endl;
  //use this create a vdd_grid & gnd_grid;
 

};

void PowerRouter::returnPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::PowerNet& temp_net){

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

void PowerRouter::SetSrcDest(RouterDB::Pin temp_pin, RouterDB::PowerGrid Vdd_grid, std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest){

  int expand_scale = 4;
  RouterDB::SinkData temp_sink;
  RouterDB::point temp_point;

  for(unsigned int i=0;i<temp_pin.pinContacts.size();i++){

      temp_sink.coord.clear();
      temp_sink.metalIdx = temp_pin.pinContacts[i].metal;

      temp_point.x = temp_pin.pinContacts[i].placedLL.x;
      temp_point.y = temp_pin.pinContacts[i].placedLL.y;
      temp_sink.coord.push_back(temp_point);
      temp_point.x = temp_pin.pinContacts[i].placedUR.x;
      temp_point.y = temp_pin.pinContacts[i].placedUR.y;
      temp_sink.coord.push_back(temp_point);
      temp_source.push_back(temp_sink);

     }

  int dis = INT_MAX;
  int index = -1;
  int lowest_metal_index = INT_MAX;
  for(unsigned int j=0;j<Vdd_grid.metals.size();j++){

        if(Vdd_grid.metals[j].MetalIdx < lowest_metal_index){
              lowest_metal_index = Vdd_grid.metals[j].MetalIdx;
          }

     }
  


  RouterDB::point source_point;
  RouterDB::point dest_point;
  std::map<int, int> dist_pair;
  //here we can use a set to find all the vdd in some region
  for(unsigned int i=0;i<temp_source.size();i++){
      source_point.x = (temp_source[i].coord[0].x + temp_source[i].coord[1].x)/2;
      source_point.y = (temp_source[i].coord[0].y + temp_source[i].coord[1].y)/2;
      for(unsigned int j=0;j<Vdd_grid.metals.size();j++){
          dest_point.x = (Vdd_grid.metals[j].LinePoint[0].x + Vdd_grid.metals[j].LinePoint[1].x)/2;
          dest_point.y = (Vdd_grid.metals[j].LinePoint[0].y + Vdd_grid.metals[j].LinePoint[1].y)/2;
          if(Vdd_grid.metals[j].MetalIdx == lowest_metal_index){
              dis = abs(source_point.x-dest_point.x)+abs(source_point.y-dest_point.y);
              std::pair<int,int> value(dis,j);
              dist_pair.insert(value);
            }

         }
     }
  
  int src_index_number = 7;
  int count = 0;
  for(auto it = dist_pair.begin();it!=dist_pair.end();++it){
      if(count < src_index_number){
        index = it->second;
        temp_sink.coord.clear();
        temp_sink.metalIdx = Vdd_grid.metals.at(index).MetalIdx;
        temp_point.x = Vdd_grid.metals.at(index).MetalRect.placedLL.x;
        temp_point.y = Vdd_grid.metals.at(index).MetalRect.placedLL.y;
        temp_sink.coord.push_back(temp_point);
        temp_point.x = Vdd_grid.metals.at(index).MetalRect.placedUR.x;
        temp_point.y = Vdd_grid.metals.at(index).MetalRect.placedUR.y;
        temp_sink.coord.push_back(temp_point);
        temp_dest.push_back(temp_sink);
        }
        count = count + 1;
  
     }

  RouterDB::point temp_ll,temp_ur;
  temp_ll.x = INT_MAX;
  temp_ll.y = INT_MAX;
  temp_ur.x = INT_MIN;
  temp_ur.y = INT_MIN;

  for(unsigned int i=0;i<temp_dest.size();i++){
     for(unsigned int j=0;j<temp_dest[i].coord.size();j++){
         if(temp_dest[i].coord[j].x<temp_ll.x){temp_ll.x = temp_dest[i].coord[j].x;}
         if(temp_dest[i].coord[j].y<temp_ll.y){temp_ll.y = temp_dest[i].coord[j].y;}
         if(temp_dest[i].coord[j].x>temp_ur.x){temp_ur.x = temp_dest[i].coord[j].x;}
         if(temp_dest[i].coord[j].y>temp_ur.y){temp_ur.y = temp_dest[i].coord[j].y;}
        }
     }

  for(unsigned int i=0;i<temp_source.size();i++){
     for(unsigned int j=0;j<temp_source[i].coord.size();j++){
         if(temp_source[i].coord[j].x<temp_ll.x){temp_ll.x = temp_source[i].coord[j].x;}
         if(temp_source[i].coord[j].y<temp_ll.y){temp_ll.y = temp_source[i].coord[j].y;}
         if(temp_source[i].coord[j].x>temp_ur.x){temp_ur.x = temp_source[i].coord[j].x;}
         if(temp_source[i].coord[j].y>temp_ur.y){temp_ur.y = temp_source[i].coord[j].y;}
        }
     }

  //LL, UR

   int xMar, yMar;
  if(this->drc_info.Metal_info.at(this->highest_metal).direct==0) { // vertical
    xMar=this->drc_info.Metal_info.at(this->highest_metal).grid_unit_x*this->grid_scale;
    yMar=this->drc_info.Metal_info.at(this->highest_metal-1).grid_unit_y*this->grid_scale;
  } else { // horizontal
    yMar=this->drc_info.Metal_info.at(this->highest_metal).grid_unit_y*this->grid_scale;
    xMar=this->drc_info.Metal_info.at(this->highest_metal-1).grid_unit_x*this->grid_scale;
  }
  
  if(temp_ll.x - expand_scale*xMar<0){LL.x = 0;}else{LL.x = temp_ll.x - expand_scale*xMar;}
  if(temp_ll.y - expand_scale*yMar<0){LL.y = 0;}else{LL.y = temp_ll.y - expand_scale*yMar;}
  if(temp_ur.x + expand_scale*xMar>width){UR.x = width;}else{UR.x = temp_ur.x + expand_scale*xMar;}
  if(temp_ur.y + expand_scale*yMar>height){UR.y = height;}else{UR.y = temp_ur.y + expand_scale*yMar;}

};


void PowerRouter::UpdateVia(RouterDB::Via &temp_via){

  //ViaRect
  std::cout<<"Test 1"<<std::endl;
  temp_via.ViaRect.metal = temp_via.model_index;
  temp_via.ViaRect.placedCenter = temp_via.position;
  temp_via.ViaRect.placedLL.x = drc_info.Via_model[temp_via.model_index].ViaRect[0].x + temp_via.position.x;
  temp_via.ViaRect.placedLL.y = drc_info.Via_model[temp_via.model_index].ViaRect[0].y + temp_via.position.y;
  temp_via.ViaRect.placedUR.x = drc_info.Via_model[temp_via.model_index].ViaRect[1].x + temp_via.position.x;
  temp_via.ViaRect.placedUR.y = drc_info.Via_model[temp_via.model_index].ViaRect[1].y + temp_via.position.y;
  //LowerMetalRect
  std::cout<<"Test 2"<<std::endl;
  temp_via.LowerMetalRect.metal = drc_info.Via_model[temp_via.model_index].LowerIdx;
  temp_via.LowerMetalRect.placedCenter = temp_via.position;
  temp_via.LowerMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].LowerRect[0].x + temp_via.position.x;
  temp_via.LowerMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].LowerRect[0].y + temp_via.position.y;
  temp_via.LowerMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].LowerRect[1].x + temp_via.position.x;
  temp_via.LowerMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].LowerRect[1].y + temp_via.position.y;
  //UpperMetalRect
  std::cout<<"Test 3"<<std::endl;
  temp_via.UpperMetalRect.metal = drc_info.Via_model[temp_via.model_index].UpperIdx;
  temp_via.UpperMetalRect.placedCenter = temp_via.position;
  temp_via.UpperMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].UpperRect[0].x + temp_via.position.x;
  temp_via.UpperMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].UpperRect[0].y + temp_via.position.y;
  temp_via.UpperMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].UpperRect[1].x + temp_via.position.x;
  temp_via.UpperMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].UpperRect[1].y + temp_via.position.y;
  

};

void PowerRouter::Physical_metal_via(){
  
   for(unsigned int i=0;i<PowerNets.size();i++){
             
           GetPhsical_Metal_Via(i);
     
      }

};



void PowerRouter::Physical_metal_via_power_grid(RouterDB::PowerGrid &temp_grid){
  
  //metals
  for(unsigned int i=0;i<temp_grid.metals.size();i++){

      temp_grid.metals[i].MetalRect.metal =  temp_grid.metals[i].MetalIdx;
      temp_grid.metals[i].MetalRect.placedCenter.x =( temp_grid.metals[i].LinePoint[0].x+temp_grid.metals[i].LinePoint[1].x)/2;
      temp_grid.metals[i].MetalRect.placedCenter.y =( temp_grid.metals[i].LinePoint[0].y+temp_grid.metals[i].LinePoint[1].y)/2; 

         if(temp_grid.metals[i].LinePoint[0].y==temp_grid.metals[i].LinePoint[1].y){          
            if(temp_grid.metals[i].LinePoint[0].x<temp_grid.metals[i].LinePoint[1].x){
              temp_grid.metals[i].MetalRect.placedLL.x =  temp_grid.metals[i].LinePoint[0].x-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedLL.y =  temp_grid.metals[i].LinePoint[0].y-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.x =  temp_grid.metals[i].LinePoint[1].x+temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.y =  temp_grid.metals[i].LinePoint[1].y+temp_grid.metals[i].width/2;
              }else{
              temp_grid.metals[i].MetalRect.placedLL.x =  temp_grid.metals[i].LinePoint[1].x-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedLL.y =  temp_grid.metals[i].LinePoint[1].y-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.x =  temp_grid.metals[i].LinePoint[0].x+temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.y =  temp_grid.metals[i].LinePoint[0].y+temp_grid.metals[i].width/2;
              }
            }else{
              if(temp_grid.metals[i].LinePoint[0].y<temp_grid.metals[i].LinePoint[1].y){               
              temp_grid.metals[i].MetalRect.placedLL.x =  temp_grid.metals[i].LinePoint[0].x-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedLL.y =  temp_grid.metals[i].LinePoint[0].y-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.x =  temp_grid.metals[i].LinePoint[1].x+temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.y =  temp_grid.metals[i].LinePoint[1].y+temp_grid.metals[i].width/2;  
                }else{
              temp_grid.metals[i].MetalRect.placedLL.x =  temp_grid.metals[i].LinePoint[1].x-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedLL.y =  temp_grid.metals[i].LinePoint[1].y-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.x =  temp_grid.metals[i].LinePoint[0].x+temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.y =  temp_grid.metals[i].LinePoint[0].y+temp_grid.metals[i].width/2;
                }
            }

         if(temp_grid.metals[i].LinePoint[0].y==temp_grid.metals[i].LinePoint[1].y and temp_grid.metals[i].LinePoint[0].x==temp_grid.metals[i].LinePoint[1].x){          
           
              temp_grid.metals[i].MetalRect.placedLL.x =  temp_grid.metals[i].LinePoint[0].x-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedLL.y =  temp_grid.metals[i].LinePoint[0].y-temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.x =  temp_grid.metals[i].LinePoint[1].x+temp_grid.metals[i].width/2;
              temp_grid.metals[i].MetalRect.placedUR.y =  temp_grid.metals[i].LinePoint[1].y+temp_grid.metals[i].width/2;
            
            }

     

     }

  //vias
  for(unsigned int i=0;i<temp_grid.vias.size();i++){

       //temp_via.position = PowerNets[i].path_metal[h].LinePoint[1];
       //temp_via.model_index = temp_metal_index;
       RouterDB::Via temp_via;
       temp_via = temp_grid.vias[i];
       std::cout<<"before update via"<<std::endl;
       std::cout<<"temp via "<<temp_via.model_index<<std::endl;
       UpdateVia(temp_via);
       std::cout<<"after update via"<<std::endl;
       temp_grid.vias[i]=temp_via;
     
     }

};

void PowerRouter::GetPhsical_Metal_Via(int i){
  
  for(unsigned int h=0;h<PowerNets[i].path_metal.size();h++){

      PowerNets[i].path_metal[h].MetalRect.metal =  PowerNets[i].path_metal[h].MetalIdx;
      PowerNets[i].path_metal[h].MetalRect.placedCenter.x =( PowerNets[i].path_metal[h].LinePoint[0].x+PowerNets[i].path_metal[h].LinePoint[1].x)/2;
      PowerNets[i].path_metal[h].MetalRect.placedCenter.y =( PowerNets[i].path_metal[h].LinePoint[0].y+PowerNets[i].path_metal[h].LinePoint[1].y)/2; 

         if(PowerNets[i].path_metal[h].LinePoint[0].y==PowerNets[i].path_metal[h].LinePoint[1].y){          
            if(PowerNets[i].path_metal[h].LinePoint[0].x<PowerNets[i].path_metal[h].LinePoint[1].x){
              PowerNets[i].path_metal[h].MetalRect.placedLL.x =  PowerNets[i].path_metal[h].LinePoint[0].x;
              PowerNets[i].path_metal[h].MetalRect.placedLL.y =  PowerNets[i].path_metal[h].LinePoint[0].y-PowerNets[i].path_metal[h].width/2;
              PowerNets[i].path_metal[h].MetalRect.placedUR.x =  PowerNets[i].path_metal[h].LinePoint[1].x;
              PowerNets[i].path_metal[h].MetalRect.placedUR.y =  PowerNets[i].path_metal[h].LinePoint[1].y+PowerNets[i].path_metal[h].width/2;
              }else{
              PowerNets[i].path_metal[h].MetalRect.placedLL.x =  PowerNets[i].path_metal[h].LinePoint[1].x;
              PowerNets[i].path_metal[h].MetalRect.placedLL.y =  PowerNets[i].path_metal[h].LinePoint[1].y-PowerNets[i].path_metal[h].width/2;
              PowerNets[i].path_metal[h].MetalRect.placedUR.x =  PowerNets[i].path_metal[h].LinePoint[0].x;
              PowerNets[i].path_metal[h].MetalRect.placedUR.y =  PowerNets[i].path_metal[h].LinePoint[0].y+PowerNets[i].path_metal[h].width/2;
              }
            }else{
              if(PowerNets[i].path_metal[h].LinePoint[0].y<PowerNets[i].path_metal[h].LinePoint[1].y){               
              PowerNets[i].path_metal[h].MetalRect.placedLL.x =  PowerNets[i].path_metal[h].LinePoint[0].x-PowerNets[i].path_metal[h].width/2;;
              PowerNets[i].path_metal[h].MetalRect.placedLL.y =  PowerNets[i].path_metal[h].LinePoint[0].y;
              PowerNets[i].path_metal[h].MetalRect.placedUR.x =  PowerNets[i].path_metal[h].LinePoint[1].x+PowerNets[i].path_metal[h].width/2;;
              PowerNets[i].path_metal[h].MetalRect.placedUR.y =  PowerNets[i].path_metal[h].LinePoint[1].y;  
                }else{
              PowerNets[i].path_metal[h].MetalRect.placedLL.x =  PowerNets[i].path_metal[h].LinePoint[1].x-PowerNets[i].path_metal[h].width/2;;
              PowerNets[i].path_metal[h].MetalRect.placedLL.y =  PowerNets[i].path_metal[h].LinePoint[1].y;
              PowerNets[i].path_metal[h].MetalRect.placedUR.x =  PowerNets[i].path_metal[h].LinePoint[0].x+PowerNets[i].path_metal[h].width/2;;
              PowerNets[i].path_metal[h].MetalRect.placedUR.y =  PowerNets[i].path_metal[h].LinePoint[0].y;
                }
            }

         if(PowerNets[i].path_metal[h].LinePoint[0].y==PowerNets[i].path_metal[h].LinePoint[1].y and PowerNets[i].path_metal[h].LinePoint[0].x==PowerNets[i].path_metal[h].LinePoint[1].x){          
           
              PowerNets[i].path_metal[h].MetalRect.placedLL.x =  PowerNets[i].path_metal[h].LinePoint[0].x-PowerNets[i].path_metal[h].width/2;
              PowerNets[i].path_metal[h].MetalRect.placedLL.y =  PowerNets[i].path_metal[h].LinePoint[0].y-PowerNets[i].path_metal[h].width/2;
              PowerNets[i].path_metal[h].MetalRect.placedUR.x =  PowerNets[i].path_metal[h].LinePoint[1].x+PowerNets[i].path_metal[h].width/2;
              PowerNets[i].path_metal[h].MetalRect.placedUR.y =  PowerNets[i].path_metal[h].LinePoint[1].y+PowerNets[i].path_metal[h].width/2;
            
            }

          
     }

  
  std::vector<RouterDB::Via> Vias;
  RouterDB::Via temp_via;
  std::set<RouterDB::Via, RouterDB::ViaComp> set_via;

  for(unsigned int h=0;h<PowerNets[i].path_metal.size();h++){
       int temp_metal_index = PowerNets[i].path_metal[h].MetalIdx;
       for(unsigned int l=0;l<PowerNets[i].path_metal.size();l++){

            int next_metal_index = PowerNets[i].path_metal[l].MetalIdx;

            if(l==h){continue;}

            if(temp_metal_index == next_metal_index -1){
                
                if(PowerNets[i].path_metal[h].LinePoint[0].x==PowerNets[i].path_metal[l].LinePoint[0].x and PowerNets[i].path_metal[h].LinePoint[0].y==PowerNets[i].path_metal[l].LinePoint[0].y){
                  temp_via.position = PowerNets[i].path_metal[h].LinePoint[0];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(PowerNets[i].path_metal[h].LinePoint[0].x==PowerNets[i].path_metal[l].LinePoint[1].x and PowerNets[i].path_metal[h].LinePoint[0].y==PowerNets[i].path_metal[l].LinePoint[1].y){
                  temp_via.position = PowerNets[i].path_metal[h].LinePoint[0];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(PowerNets[i].path_metal[h].LinePoint[1].x==PowerNets[i].path_metal[l].LinePoint[0].x and PowerNets[i].path_metal[h].LinePoint[1].y==PowerNets[i].path_metal[l].LinePoint[0].y){
                  temp_via.position = PowerNets[i].path_metal[h].LinePoint[1];
                  temp_via.model_index = temp_metal_index;
                  UpdateVia(temp_via);
                  set_via.insert(temp_via);
                  }

                if(PowerNets[i].path_metal[h].LinePoint[1].x==PowerNets[i].path_metal[l].LinePoint[1].x and PowerNets[i].path_metal[h].LinePoint[1].y==PowerNets[i].path_metal[l].LinePoint[1].y){
                  temp_via.position = PowerNets[i].path_metal[h].LinePoint[1];
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
      PowerNets[i].path_via.push_back(*via_it);
     }

};


void PowerRouter::CreatePowerGridDrc_info( int h_skip_factor, int v_skip_factor){

  PowerGrid_Drc_info = drc_info;
  
  int Power_width = 1; 

  for(unsigned int i=0;i<PowerGrid_Drc_info.Metal_info.size();i++){
      
    auto& mi = PowerGrid_Drc_info.Metal_info[i];

    int factor;

    if        (mi.direct == 1) { // horizontal
      factor = h_skip_factor;
    } else if (mi.direct == 0) { // vertical
      factor = v_skip_factor;
    } else {
      assert( 0);
    }

    // This is weird changing them both, but the code did this before
    // Probably only need to expand the x for vertical wires and the y for horizontal wires
    mi.grid_unit_x *= factor;
    mi.grid_unit_y *= factor;
    mi.width *= Power_width;

  }

};

void PowerRouter::GetData(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal){
  std::cout<<"Checkpoint get Data 1"<<std::endl;
  getDRCdata(drc_info);
  std::cout<<"Checkpoint get Data 2"<<std::endl;
  getBlockData(node, Lmetal, Hmetal);
  std::cout<<"Checkpoint get Data 3"<<std::endl;
  getNetData(node);
  std::cout<<"Checkpoint get Data 4"<<std::endl;
  getTerminalData(node);
  std::cout<<"Checkpoint get Data 5"<<std::endl;
  getPowerGridData(node);
  std::cout<<"Checkpoint get Data 6"<<std::endl;
  getPowerNetData(node);//Power net 
  std::cout<<"Checkpoint get Data 7"<<std::endl;

};

void PowerRouter::getBlockData(PnRDB::hierNode& node, int Lmetal, int Hmetal){

  std::cout<<"Router-Info: begin to import data"<<std::endl;
  this->isTop = node.isTop;
  this->topName=node.name;
  this->width=node.width;
  this->height=node.height;
  this->LL.x=0; this->LL.y=0;
  this->UR.x=node.width;
  this->UR.y=node.height;
  this->path_number=1; // number of candidates
  //int max_width = node.width;
  //int max_height = node.height;
  lowest_metal = Lmetal;
  highest_metal = Hmetal;
  this->layerNo = drc_info.Metal_info.size();

  //grid_alpha should be adjusted according to the size of node
  //more adjust is necessry for detail router?
  grid_scale = 1;
	
  //For blocks	
  for(unsigned int i=0;i<node.Blocks.size();i++){
      RouterDB::Block temp_block;
      int slcNumber = node.Blocks[i].selectedInstance;
      temp_block.blockName=node.Blocks[i].instance[slcNumber].name;
      temp_block.blockMaster=node.Blocks[i].instance[slcNumber].master;
      temp_block.gdsfile=node.Blocks[i].instance[slcNumber].gdsFile;
      temp_block.numTerminals=node.Blocks[i].instance[slcNumber].blockPins.size();
      temp_block.orient=RouterDB::Omark(node.Blocks[i].instance[slcNumber].orient);
      temp_block.isLeaf=node.Blocks[i].instance[slcNumber].isLeaf;
      temp_block.width=node.Blocks[i].instance[slcNumber].width;
      temp_block.height=node.Blocks[i].instance[slcNumber].height;
      temp_block.area=temp_block.width*temp_block.height;
      temp_block.placedLL.x=node.Blocks[i].instance[slcNumber].placedBox.LL.x;
      temp_block.placedLL.y=node.Blocks[i].instance[slcNumber].placedBox.LL.y;
      temp_block.placedUR.x=node.Blocks[i].instance[slcNumber].placedBox.UR.x;
      temp_block.placedUR.y=node.Blocks[i].instance[slcNumber].placedBox.UR.y;
      //temp_block.originLL.x=node.Blocks[i].instance.originBox.LL.x;
      //temp_block.originLL.y=node.Blocks[i].instance.originBox.LL.y;
      //temp_block.originUR.x=node.Blocks[i].instance.originBox.UR.x;
      //temp_block.originUR.y=node.Blocks[i].instance.originBox.UR.y;

      for(unsigned int j=0;j<node.Blocks[i].instance[slcNumber].blockPins.size();j++){
          RouterDB::Pin temp_pin;
          ConvertPin(temp_pin,node.Blocks[i].instance[slcNumber].blockPins[j]);
          temp_block.pins.push_back(temp_pin);
      }

   for(unsigned int j=0;j<node.Blocks[i].instance[slcNumber].interMetals.size();j++){
       RouterDB::contact temp_metal;
       ConvertContact(temp_metal,node.Blocks[i].instance[slcNumber].interMetals[j]);
       temp_block.InternalMetal.push_back(temp_metal);
      }
	
   for(unsigned int j=0;j<node.Blocks[i].instance[slcNumber].interVias.size();j++){
       RouterDB::Via temp_via;
       ConvertVia(temp_via,node.Blocks[i].instance[slcNumber].interVias[j]);
       temp_block.InternalVia.push_back(temp_via);
      }
   Blocks.push_back(temp_block);
  }
  std::cout<<"Router-Info: complete importing data"<<std::endl;
};

void PowerRouter::getNetData(PnRDB::hierNode& node){
	
  //For net

  for(unsigned int i=0;i<node.Nets.size();i++){
      RouterDB::Net temp_net;
      temp_net.netName = node.Nets[i].name;
      //temp_net.shielding = node.Nets[i].
      //path_metal
      for(unsigned int j=0;j<node.Nets[i].path_metal.size();j++){
          RouterDB::Metal temp_metal;
          std::cout<<"getNetData check point 1"<<std::endl;
          ConvertMetal(temp_metal,node.Nets[i].path_metal[j]);
          std::cout<<"getNetData check point 2"<<std::endl;
          temp_net.path_metal.push_back(temp_metal);          
         }
      
      //path via
      for(unsigned int j=0;j<node.Nets[i].path_via.size();j++){
          RouterDB::Via temp_via;
          std::cout<<"getNetData check point 3"<<std::endl;
          ConvertVia(temp_via,node.Nets[i].path_via[j]); 
          std::cout<<"getNetData check point 4"<<std::endl;   
          temp_net.path_via.push_back(temp_via);          
         }

      Nets.push_back(temp_net);
     
     }
  	

  std::cout<<"Router-Info: complete importing data"<<std::endl;
};

void PowerRouter::getPowerGridData(PnRDB::hierNode & node){


  //Vdd_grid
  Vdd_grid.power = 1;

  for(unsigned int i =0;i<node.Vdd.metals.size();i++){
       RouterDB::Metal temp_metal;
       ConvertMetal(temp_metal, node.Vdd.metals[i]);
       Vdd_grid.metals.push_back(temp_metal);
     }

  for(unsigned int i =0;i<node.Vdd.vias.size();i++){
       RouterDB::Via temp_via;
       ConvertVia(temp_via, node.Vdd.vias[i]);
       Vdd_grid.vias.push_back(temp_via);
     }

  //Gnd_grid
  // Gnd_grid.power = 0; // SMB: should be this
  Gnd_grid.power = 1;

  for(unsigned int i =0;i<node.Gnd.metals.size();i++){
       RouterDB::Metal temp_metal;
       ConvertMetal(temp_metal, node.Gnd.metals[i]);
       Gnd_grid.metals.push_back(temp_metal);
     }

  for(unsigned int i =0;i<node.Gnd.vias.size();i++){
       RouterDB::Via temp_via;
       ConvertVia(temp_via, node.Gnd.vias[i]);
       Gnd_grid.vias.push_back(temp_via);
     }

};

void PowerRouter::getTerminalData(PnRDB::hierNode& node){

  for(unsigned int i=0;i<node.Terminals.size();i++){
      RouterDB::terminal temp_terminal;
      ConvertTerminal(temp_terminal, node.Terminals[i]);
      Terminals.push_back(temp_terminal);
     }

};

void PowerRouter::getPowerNetData(PnRDB::hierNode& node){
	
  //For power net

  for(unsigned int i=0;i<node.PowerNets.size();i++){
      RouterDB::PowerNet temp_net;
      temp_net.netName = node.PowerNets[i].name;
      //temp_net.shielding = node.Nets[i].shielding;
      temp_net.power = node.PowerNets[i].power;
      //path_metal
      for(unsigned int j=0;j<node.PowerNets[i].path_metal.size();j++){
          RouterDB::Metal temp_metal;
          ConvertMetal(temp_metal, node.PowerNets[i].path_metal[j]);
          temp_net.path_metal.push_back(temp_metal);          
         }
      
      //path via
      for(unsigned int j=0;j<node.PowerNets[i].path_via.size();j++){
          RouterDB::Via temp_via;
          ConvertVia(temp_via,node.PowerNets[i].path_via[j]);
          temp_net.path_via.push_back(temp_via);          

         }

      //pins

      for(unsigned int j=0;j<node.PowerNets[i].Pins.size();j++){
          RouterDB::Pin temp_pin;
          ConvertPin(temp_pin, node.PowerNets[i].Pins[j]);
          temp_net.pins.push_back(temp_pin);
      }
      

      PowerNets.push_back(temp_net);
     
     }
};

void PowerRouter::ConvertTerminal(RouterDB::terminal& temp_terminal, PnRDB::terminal pnr_terminal){
  
  temp_terminal.name = pnr_terminal.name;
  temp_terminal.type = pnr_terminal.type;
  temp_terminal.netIter = pnr_terminal.netIter;
  for(unsigned int i=0; i<pnr_terminal.termContacts.size();i++){
       RouterDB::contact temp_contact;
       ConvertContact(temp_contact, pnr_terminal.termContacts[i]);
       temp_terminal.termContacts.push_back(temp_contact);
     }

};

void PowerRouter::ConvertContact(RouterDB::contact& temp_metal, PnRDB::contact& pnr_metal){

  //RouterDB::contact temp_metal;
  if(drc_info.Metalmap.find(pnr_metal.metal)!=drc_info.Metalmap.end()){
      temp_metal.metal=drc_info.Metalmap[pnr_metal.metal];
      //temp_metal.width=drc_info.Metal_info[temp_metal.MetalIdx].width;
    }else{
      std::cout<<"Router-Error: interMetal info missing metal"<<std::endl;
    }
   RouterDB::point temp_point;
   temp_metal.placedLL.x = pnr_metal.placedBox.LL.x;     
   temp_metal.placedLL.y = pnr_metal.placedBox.LL.y;
   temp_metal.placedUR.x = pnr_metal.placedBox.UR.x;      
   temp_metal.placedUR.y = pnr_metal.placedBox.UR.y;  
   temp_metal.placedCenter.x = (temp_metal.placedLL.x + temp_metal.placedUR.x)/2;
   temp_metal.placedCenter.y = (temp_metal.placedLL.y + temp_metal.placedUR.y)/2;
   //temp_block.InternalMetal.push_back(temp_metal);

};

void PowerRouter::ConvertMetal(RouterDB::Metal& temp_metal,PnRDB::Metal& pnr_metal){

  std::cout<<"ConvertMetal check point 1"<<std::endl;
  //RouterDB::Metal temp_metal;
  temp_metal.MetalIdx = pnr_metal.MetalIdx;
  RouterDB::point temp_point;
  temp_point.x = pnr_metal.LinePoint[0].x;
  temp_point.y = pnr_metal.LinePoint[0].y;
  temp_metal.LinePoint.push_back(temp_point);

  temp_point.x = pnr_metal.LinePoint[1].x;
  temp_point.y = pnr_metal.LinePoint[1].y;
  temp_metal.LinePoint.push_back(temp_point);
/*
  temp_metal.LinePoint[0].x = pnr_metal.LinePoint[0].x;
  temp_metal.LinePoint[0].y = pnr_metal.LinePoint[0].y;
  temp_metal.LinePoint[1].x = pnr_metal.LinePoint[1].x;
  temp_metal.LinePoint[1].y = pnr_metal.LinePoint[1].y;
*/
  temp_metal.width = pnr_metal.width;
  //contact
  RouterDB::contact temp_contact;
  std::cout<<"ConvertMetal check point 2"<<std::endl;
  if(drc_info.Metalmap.find(pnr_metal.MetalRect.metal)!=drc_info.Metalmap.end()){
    temp_contact.metal=drc_info.Metalmap[pnr_metal.MetalRect.metal];
  }else{
    std::cout<<"Router-Error: the metal pin contact of block is not found"<<std::endl;
  }

  //temp_contact.metal = drc_info.Metalmap[node.Nets[i].path_metal[j].MetalRect.metal];
  std::cout<<"ConvertMetal check point 3"<<std::endl;
  temp_contact.placedLL.x = pnr_metal.MetalRect.placedBox.LL.x;
  temp_contact.placedLL.y = pnr_metal.MetalRect.placedBox.LL.y;
  temp_contact.placedUR.x = pnr_metal.MetalRect.placedBox.UR.x;
  temp_contact.placedUR.y = pnr_metal.MetalRect.placedBox.UR.y;
  temp_contact.placedCenter.x = pnr_metal.MetalRect.placedCenter.x;
  temp_contact.placedCenter.y = pnr_metal.MetalRect.placedCenter.y;
  temp_metal.MetalRect = temp_contact;
  std::cout<<"ConvertMetal check point 4"<<std::endl;
};

void PowerRouter::ConvertVia(RouterDB::Via &temp_via,PnRDB::Via& pnr_via){

  //RouterDB::Via temp_via;

  temp_via.model_index = pnr_via.model_index;
  temp_via.position.x = pnr_via.placedpos.x;
  temp_via.position.y = pnr_via.placedpos.y;
  //ViaRect

  if(drc_info.Viamap.find(pnr_via.ViaRect.metal)!=drc_info.Viamap.end()){
      temp_via.ViaRect.metal = drc_info.Viamap[pnr_via.ViaRect.metal];
     }else{
      std::cout<<"Router-Error: - Viamap Error"<<std::endl;
     }

  temp_via.ViaRect.placedLL.x = pnr_via.ViaRect.placedBox.LL.x;
  temp_via.ViaRect.placedLL.y = pnr_via.ViaRect.placedBox.LL.y;
  temp_via.ViaRect.placedUR.x = pnr_via.ViaRect.placedBox.UR.x;
  temp_via.ViaRect.placedUR.y = pnr_via.ViaRect.placedBox.UR.y;
  temp_via.ViaRect.placedCenter.x= pnr_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.placedCenter.y= pnr_via.ViaRect.placedCenter.y;
  //LowerRect //LowerMetalRect
  if(drc_info.Metalmap.find(pnr_via.LowerMetalRect.metal)!=drc_info.Metalmap.end()){
      temp_via.LowerMetalRect.metal = drc_info.Metalmap[pnr_via.LowerMetalRect.metal];
     }else{
      std::cout<<"Router-Error: Metal map error"<<std::endl;
     }
  temp_via.LowerMetalRect.placedLL.x = pnr_via.LowerMetalRect.placedBox.LL.x;
  temp_via.LowerMetalRect.placedLL.y = pnr_via.LowerMetalRect.placedBox.LL.y;
  temp_via.LowerMetalRect.placedUR.x = pnr_via.LowerMetalRect.placedBox.UR.x;
  temp_via.LowerMetalRect.placedUR.y = pnr_via.LowerMetalRect.placedBox.UR.y;
  temp_via.LowerMetalRect.placedCenter.x= pnr_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.placedCenter.y= pnr_via.LowerMetalRect.placedCenter.y;
  //UpperRect //UpperMetalRect
  if(drc_info.Metalmap.find(pnr_via.UpperMetalRect.metal)!=drc_info.Metalmap.end()){
       temp_via.UpperMetalRect.metal = drc_info.Metalmap[pnr_via.UpperMetalRect.metal];
     }else{
       std::cout<<"Router-Error: Metal map error"<<std::endl;
     }
  temp_via.UpperMetalRect.placedLL.x = pnr_via.UpperMetalRect.placedBox.LL.x;
  temp_via.UpperMetalRect.placedLL.y = pnr_via.UpperMetalRect.placedBox.LL.y;
  temp_via.UpperMetalRect.placedUR.x = pnr_via.UpperMetalRect.placedBox.UR.x;
  temp_via.UpperMetalRect.placedUR.y = pnr_via.UpperMetalRect.placedBox.UR.y;
  temp_via.UpperMetalRect.placedCenter.x = pnr_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.placedCenter.y = pnr_via.UpperMetalRect.placedCenter.y;

};

void PowerRouter::ConvertPin(RouterDB::Pin& temp_pin,PnRDB::pin& pnr_pin){

  //RouterDB::Pin temp_pin;
  temp_pin.pinName=pnr_pin.name;
  temp_pin.netIter=pnr_pin.netIter;
  for(unsigned int k=0;k<pnr_pin.pinContacts.size();k++){
       RouterDB::contact temp_contact;
       if(drc_info.Metalmap.find(pnr_pin.pinContacts[k].metal)!=drc_info.Metalmap.end()){
           temp_contact.metal=drc_info.Metalmap[pnr_pin.pinContacts[k].metal];
        }else{
           std::cout<<"Router-Error: the metal pin contact of block is not found"<<std::endl;
        }
       temp_contact.placedLL.x=pnr_pin.pinContacts[k].placedBox.LL.x;
       temp_contact.placedLL.y=pnr_pin.pinContacts[k].placedBox.LL.y;
       temp_contact.placedUR.x=pnr_pin.pinContacts[k].placedBox.UR.x;
       temp_contact.placedUR.y=pnr_pin.pinContacts[k].placedBox.UR.y;
       temp_contact.placedCenter.x=pnr_pin.pinContacts[k].placedCenter.x;
       temp_contact.placedCenter.y=pnr_pin.pinContacts[k].placedCenter.y;
       temp_pin.pinContacts.push_back(temp_contact);
      }
          

  for(unsigned int k=0;k<pnr_pin.pinVias.size();k++){
        RouterDB::Via temp_via;
        temp_via.model_index = pnr_pin.pinVias[k].model_index;
        temp_via.position.x = pnr_pin.pinVias[k].placedpos.x;
        temp_via.position.y = pnr_pin.pinVias[k].placedpos.y;
        //ViaRect

        if(drc_info.Viamap.find(pnr_pin.pinVias[k].ViaRect.metal)!=drc_info.Viamap.end()){
             temp_via.ViaRect.metal = drc_info.Viamap[pnr_pin.pinVias[k].ViaRect.metal];
          }else{
             std::cout<<"Router-Error: - Viamap Error"<<std::endl;
          }
        temp_via.ViaRect.placedLL.x = pnr_pin.pinVias[k].ViaRect.placedBox.LL.x;
        temp_via.ViaRect.placedLL.y = pnr_pin.pinVias[k].ViaRect.placedBox.LL.y;
        temp_via.ViaRect.placedUR.x = pnr_pin.pinVias[k].ViaRect.placedBox.UR.x;
        temp_via.ViaRect.placedUR.y = pnr_pin.pinVias[k].ViaRect.placedBox.UR.y;
        temp_via.ViaRect.placedCenter.x= pnr_pin.pinVias[k].ViaRect.placedCenter.x;
        temp_via.ViaRect.placedCenter.y= pnr_pin.pinVias[k].ViaRect.placedCenter.y;
        //LowerRect //LowerMetalRect
        if(drc_info.Metalmap.find(pnr_pin.pinVias[k].LowerMetalRect.metal)!=drc_info.Metalmap.end()){
             temp_via.LowerMetalRect.metal = drc_info.Metalmap[pnr_pin.pinVias[k].LowerMetalRect.metal];
           }else{
             std::cout<<"Router-Error: Metal map error"<<std::endl;
           }
         temp_via.LowerMetalRect.placedLL.x = pnr_pin.pinVias[k].LowerMetalRect.placedBox.LL.x;
         temp_via.LowerMetalRect.placedLL.y = pnr_pin.pinVias[k].LowerMetalRect.placedBox.LL.y;
         temp_via.LowerMetalRect.placedUR.x = pnr_pin.pinVias[k].LowerMetalRect.placedBox.UR.x;
         temp_via.LowerMetalRect.placedUR.y = pnr_pin.pinVias[k].LowerMetalRect.placedBox.UR.y;
         temp_via.LowerMetalRect.placedCenter.x= pnr_pin.pinVias[k].LowerMetalRect.placedCenter.x;
         temp_via.LowerMetalRect.placedCenter.y= pnr_pin.pinVias[k].LowerMetalRect.placedCenter.y;
         //UpperRect //UpperMetalRect
         if(drc_info.Metalmap.find(pnr_pin.pinVias[k].UpperMetalRect.metal)!=drc_info.Metalmap.end()){
              temp_via.UpperMetalRect.metal = drc_info.Metalmap[pnr_pin.pinVias[k].UpperMetalRect.metal];
            }else{
              std::cout<<"Router-Error: Metal map error"<<std::endl;
            }
         temp_via.UpperMetalRect.placedLL.x = pnr_pin.pinVias[k].UpperMetalRect.placedBox.LL.x;
         temp_via.UpperMetalRect.placedLL.y = pnr_pin.pinVias[k].UpperMetalRect.placedBox.LL.y;
         temp_via.UpperMetalRect.placedUR.x = pnr_pin.pinVias[k].UpperMetalRect.placedBox.UR.x;
         temp_via.UpperMetalRect.placedUR.y = pnr_pin.pinVias[k].UpperMetalRect.placedBox.UR.y;
         temp_via.UpperMetalRect.placedCenter.x = pnr_pin.pinVias[k].UpperMetalRect.placedCenter.x;
         temp_via.UpperMetalRect.placedCenter.y = pnr_pin.pinVias[k].UpperMetalRect.placedCenter.y;

         temp_pin.pinVias.push_back(temp_via);
      }


};

void PowerRouter::CreatePlistNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Net>& Nets){
  
  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;
  //here via is not included
  for(unsigned int i=0;i<Nets.size();i++){
      for(unsigned int j=0;j<Nets[i].path_metal.size();j++){

           mIdx = Nets[i].path_metal[j].MetalIdx;
           LLx = Nets[i].path_metal[j].MetalRect.placedLL.x;
           LLy = Nets[i].path_metal[j].MetalRect.placedLL.y;
           URx = Nets[i].path_metal[j].MetalRect.placedUR.x;
           URy = Nets[i].path_metal[j].MetalRect.placedUR.y;
           ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);

         }
     }

};

void PowerRouter::CreatePlistPowerNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::PowerNet>& Nets){
  
  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;
  //here via is not included
  for(unsigned int i=0;i<Nets.size();i++){
      for(unsigned int j=0;j<Nets[i].path_metal.size();j++){

           mIdx = Nets[i].path_metal[j].MetalIdx;
           LLx = Nets[i].path_metal[j].MetalRect.placedLL.x;
           LLy = Nets[i].path_metal[j].MetalRect.placedLL.y;
           URx = Nets[i].path_metal[j].MetalRect.placedUR.x;
           URy = Nets[i].path_metal[j].MetalRect.placedUR.y;
           ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);

         }
     }

};

void PowerRouter::CreatePlistPowerGrid(std::vector<std::vector<RouterDB::point> >& plist, RouterDB::PowerGrid Nets){
  
  //RouterDB::point tmpP;
  //int mIdx, LLx, LLy, URx, URy;
  //here via is not included
  //for(unsigned int i=0;i<Nets.size();i++){
      for(unsigned int j=0;j<Nets.metals.size();j++){

           int mIdx = Nets.metals[j].MetalIdx;
           int LLx = Nets.metals[j].MetalRect.placedLL.x;
           int LLy = Nets.metals[j].MetalRect.placedLL.y;
           int URx = Nets.metals[j].MetalRect.placedUR.x;
           int URy = Nets.metals[j].MetalRect.placedUR.y;
           ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);

         }
     //}

};


void PowerRouter::ConvertToMetalPnRDB_Placed_Placed(PnRDB::Metal &temp_metal,RouterDB::Metal router_metal){

  //to placed or origin, it's problem QQQQ
  temp_metal.MetalIdx = router_metal.MetalIdx;
  temp_metal.width = router_metal.width;
  for(unsigned int i=0;i<router_metal.LinePoint.size();i++){
      PnRDB::point temp_point;
      temp_point.x = router_metal.LinePoint[i].x;
      temp_point.y = router_metal.LinePoint[i].y;
      temp_metal.LinePoint.push_back(temp_point);
     }
   PnRDB::contact temp_contact;
   ConvertToContactPnRDB_Placed_Placed(temp_contact,router_metal.MetalRect);
   temp_metal.MetalRect = temp_contact;

};

void PowerRouter::ReturnPowerGridData(PnRDB::hierNode& node){

//vdd
  for(unsigned int i=0;i<Vdd_grid.metals.size();i++){
      PnRDB::Metal temp_metal;
      ConvertToMetalPnRDB_Placed_Placed(temp_metal,Vdd_grid.metals[i]);
      node.Vdd.metals.push_back(temp_metal);
     }

  for(unsigned int i=0;i<Vdd_grid.vias.size();i++){
      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Placed(temp_via,Vdd_grid.vias[i]);
      node.Vdd.vias.push_back(temp_via);
     }
  node.Vdd.name = Vdd_grid.name;
  std::cout<<"Power grid name "<<node.Vdd.name<<std::endl;
//Gnd
  for(unsigned int i=0;i<Gnd_grid.metals.size();i++){
      PnRDB::Metal temp_metal;
      ConvertToMetalPnRDB_Placed_Placed(temp_metal,Gnd_grid.metals[i]);
      node.Gnd.metals.push_back(temp_metal);
     }

  for(unsigned int i=0;i<Gnd_grid.vias.size();i++){
      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Placed(temp_via,Gnd_grid.vias[i]);
      node.Gnd.vias.push_back(temp_via);
     }
  node.Gnd.name = Gnd_grid.name;
  std::cout<<"Power grid name "<<node.Gnd.name<<std::endl;

};

void PowerRouter::ReturnPowerNetData(PnRDB::hierNode& node){

  for(unsigned int i=0;i<PowerNets.size();i++){
      
      int index=-1;
      for(unsigned int j=0;j<node.PowerNets.size();j++){
           if(PowerNets[i].netName == node.PowerNets[j].name){index = j; break;}
         }
      if (index!=-1) {
      for(unsigned int j=0;j<PowerNets[i].path_metal.size();j++){
          PnRDB::Metal temp_metal;
          ConvertToMetalPnRDB_Placed_Placed(temp_metal,PowerNets[i].path_metal[j]);
          node.PowerNets[index].path_metal.push_back(temp_metal);
         }

      for(unsigned int j=0;j<PowerNets[i].path_via.size();j++){
           PnRDB::Via temp_via;
           ConvertToViaPnRDB_Placed_Placed(temp_via,PowerNets[i].path_via[j]);
           node.PowerNets[index].path_via.push_back(temp_via);
         }
      }
     }

};
