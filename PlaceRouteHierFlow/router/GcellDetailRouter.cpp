#include "GcellDetailRouter.h"

GcellDetailRouter::GcellDetailRouter(){

};

GcellDetailRouter::GcellDetailRouter(PnRDB::hierNode& HierNode, GcellGlobalRouter& GR, int path_number, int grid_scale){

  std::cout<<"start detail router\n";
  this->Nets = GR.Nets;
  this->Blocks = GR.Blocks;
  this->Terminals = GR.Terminals;
  this->drc_info = GR.drc_info;
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

  printNetsInfo();
 
/*
  Connection();
  
  std::cout<<"***********start check overlap**********"<<std::endl;
  RecoverOverlap();
  std::cout<<"***********end check overlap*************"<<std::endl;

  //std::cout<<"********start last connection*************"<<std::endl;
  //AddMetalToPin();
  //std::cout<<"********end last connection*************"<<std::endl;
*/  

  create_detailrouter(); 

  std::cout<<"***************physical metal and via"<<std::endl;
  Physical_metal_via(); //this needs modify  

  std::cout<<"***********start return node in detail router********"<<std::endl;
  ReturnHierNode(HierNode);
  std::cout<<"************end return node in detail router**********"<<std::endl;

};

void GcellDetailRouter::printNetsInfo(){

  for(int i=0;i<Nets.size();i++){

      std::cout<<"Net name "<<Nets[i].netName<<std::endl;
          
      std::cout<<"Net pins"<<std::endl;

      for(int j=0;j<Nets[i].connectedTile.size();j++){

            for(int k=0;k<Nets[i].connectedTile[j].size();k++){

                std::cout<<Nets[i].connectedTile[j][k]<<" ";

               }
                std::cout<<std::endl;

          }

       std::cout<<"Global path"<<std::endl;
     
      int ST_index = Nets[i].STindex;

      for(int j=0;j<Nets[i].STs[ST_index].path.size();j++){

           std::cout<<" ( "<<Nets[i].STs[ST_index].path[j].first<<" "<<Nets[i].STs[ST_index].path[j].second<<" ) ";

          }
          
       std::cout<<std::endl;

     }

};

/*
void DetailRouter::create_detailrouter(){

  //initial a set for internal metal
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize( this->layerNo );
  CreatePlistBlocks(plist, this->Blocks);
  CreatePlistTerminals(plist, this->Terminals);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x;
  InsertPlistToSet_x(Set_x, plist);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_net;
  //end initial set
  //start detail router 
  for(int i=0;i<Nets.size();i++){

       //judge whether a net should be routed or not
       if(Nets[i].seg.size()==0){continue;}
       if(Nets[i].seg[0].chosenCand==-1){continue;} //this maybe revised [wbxu: need revision if only other seg has no candidate?]

       //collect pins & collect metal path
       std::cout<<"starting check find pin"<<std::endl;
       std::vector<std::vector<RouterDB::SinkData> > temp_pins = findPins_new(Nets[i]);
       std::cout<<"end check find pin"<<std::endl;

//////QQQ1 grid creation       
       std::cout<<"starting check find path"<<std::endl;
       std::vector<RouterDB::Metal> temp_path = findGlobalPath(Nets[i]);
       std::cout<<"end check find path"<<std::endl;
       //create grid
       //Grid grid(drc_info, grid_scale, lowest_metal, highest_metal, LL, UR, temp_pins, temp_path);
       Grid grid ( temp_pins, temp_path,  drc_info, LL, UR, lowest_metal, highest_metal, 1, 5);
//////QQQ1 end of grid creation

       RouterDB::point gridll=grid.GetGridLL();
       RouterDB::point gridur=grid.GetGridUR();
       std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > plist = FindsetPlist(Set_x, gridll, gridur);
       grid.InactivePointlist(plist);
      // void InactivePointlist(std::vector< std::set<RouterDB::point, RouterDB::pointXYComp> > &plist);
       
       //initial source
       std::vector<RouterDB::SinkData> temp_source;
       std::vector<std::vector<RouterDB::point> > add_plist;
       add_plist.resize(this->layerNo);
       //temp_source = temp_pins[0];
       
       for(int j = 0;j<temp_pins[0].size();j++){
            temp_source.push_back(temp_pins[0][j]);
          }

       int source_lock = 0;
       for(int j=1;j<temp_pins.size();j++){
           //create dest
           std::cout<<"Working on dest "<<j<<std::endl;
           std::vector<RouterDB::SinkData> temp_dest = temp_pins[j];
           
           std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap;
           //std::vector<RouterDB::contact> Terminal_contact=grid.setSrcDest( temp_source, temp_dest, this->width, this->height, Smap);
           grid.setSrcDest( temp_source, temp_dest, this->width, this->height, Smap);

           grid.ActivateSourceDest();
           
           std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > netplist = FindsetPlist(Set_net, gridll, gridur);
           grid.InactivePointlist(netplist);

           //std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap;
           //Terminal_contact=grid.setSrcDest_detail( temp_source, temp_dest, this->width, this->height, Smap);
           grid.setSrcDest_detail( temp_source, temp_dest, this->width, this->height, Smap);

//what about this problem?????
           grid.PrepareGraphVertices(gridll.x, gridll.y, gridur.x, gridur.y); //QQQQQto be fixed
//what about this problem?????
           //Graph graph(grid, this->path_number);
           Graph graph(grid);
           bool pathMark= graph.FindFeasiblePath(grid, this->path_number);
           std::vector<std::vector<RouterDB::Metal> > physical_path;
           if(pathMark) {
           physical_path=graph.ConvertPathintoPhysical(grid);

           //lastmile connection source
           //check first point of physical path
           lastmile_source_new(physical_path,temp_source);
           //lastmile connection dest
             //check last point of physical path
           lastmile_dest_new(physical_path,temp_dest);

           //return physical path to net
           //splitPath(physical_path, Nets[i]);
           returnPath(physical_path, Nets[i]);
           }else{
           std::cout<<"Router-Warning: feasible path might not be found\n";
           std::cout<<Nets[i].netName<<std::endl;
           }


           //update physical path to 
           UpdatePlistNets(physical_path, add_plist);

           if(source_lock==1){
              temp_source.clear();
              source_lock = 1;
             }

           //add
           updateSource(physical_path, temp_source);// wbxu: temp_dest might need be appended into temp_source

           grid.InactivateSourceDest();

           for(int p=0;p<temp_dest.size();p++){
                 temp_source.push_back(temp_dest[p]);
              }
          }

      InsertPlistToSet_x(Set_net, add_plist);

     }


};
*/

std::vector<RouterDB::Metal> GcellDetailRouter::CpSymPath(std::vector<RouterDB::Metal> temp_path, int H, int center){


  std::vector<RouterDB::Metal> sym_path;

      
     for(int j=0;j<temp_path.size();j++){

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

void GcellDetailRouter::create_detailrouter(){

  //initial a set for internal metal
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize( this->layerNo );

  std::cout<<"Gcell Detail Router Check point 1"<<std::endl;
  CreatePlistBlocks(plist, this->Blocks);

  std::cout<<"Gcell Detail Router Check point 2"<<std::endl;
  //CreatePlistTerminals(plist, this->Terminals);

  std::cout<<"Gcell Detail Router Check point 3"<<std::endl;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x;

  std::cout<<"Gcell Detail Router Check point 4"<<std::endl;
  InsertPlistToSet_x(Set_x, plist);

  std::cout<<"Gcell Detail Router Check point 5"<<std::endl;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_net;
  //end initial set
  //start detail router 
  for(int i=0;i<Nets.size();i++){

       //added for terminals
       CreatePlistTerminals(plist, this->Terminals);
       InsertPlistToSet_x(Set_x, plist);
       //added for teminals

       if(Nets[i].path_metal.size()>0){continue;}
       //judge whether a net should be routed or not
       //if(Nets[i].seg.size()==0){continue;}
       //if(Nets[i].seg[0].chosenCand==-1){continue;} //this maybe revised [wbxu: need revision if only other seg has no candidate?]

       std::vector<std::vector<RouterDB::SinkData> > temp_pins;
       std::vector<std::vector<RouterDB::SinkData> > sym_temp_pins;
       std::vector<std::vector<RouterDB::SinkData> > common_pins;

//////QQQ1 grid creation       
       //std::cout<<"starting check find path"<<std::endl;
       //std::vector<RouterDB::Metal> temp_path = findGlobalPath(Nets[i]);
       //std::cout<<"end check find path"<<std::endl;
       //create grid
       //Grid grid(drc_info, grid_scale, lowest_metal, highest_metal, LL, UR, temp_pins, temp_path);
       //Grid grid ( temp_pins, temp_path,  drc_info, LL, UR, lowest_metal, highest_metal, 1, 5);
       RouterDB::point chip_LL;
       RouterDB::point chip_UR;
       chip_LL.x = 0;
       chip_LL.y = 0;
       chip_UR.x = width;
       chip_UR.y = height;
       int STindex = Nets[i].STindex;

       std::cout<<"STindex "<<Nets[i].STindex<<std::endl;
       std::cout<<"STs size "<<Nets[i].STs.size()<<std::endl;
      
       
       for(int q=0;q<Nets[i].STs.size();q++){
           std::cout<<"STs path size "<<Nets[i].STs[q].path.size()<<std::endl;
          }

       std::vector<std::pair<int,int> > global_path = Nets[i].STs[STindex].path;
       std::pair<int,int> temp_global_path;

       for(int terminal_size=0;terminal_size<Nets[i].terminals.size();terminal_size++){

            temp_global_path.first = Nets[i].terminals[terminal_size];
            temp_global_path.second = Nets[i].terminals[terminal_size];
            global_path.push_back(temp_global_path);

          }


       if(Nets[i].symCounterpart!=-1 and Nets[i].symCounterpart < Nets.size()-1){

            int sym_ST_index = Nets[Nets[i].symCounterpart].STindex;
            for(int j=0;j<Nets[Nets[i].symCounterpart].STs[sym_ST_index].path.size();j++){
                  global_path.push_back(Nets[Nets[i].symCounterpart].STs[sym_ST_index].path[j]);
                }
             
            for(int j=0;j<Nets[Nets[i].symCounterpart].terminals.size();j++){
                  temp_global_path.first = Nets[Nets[i].symCounterpart].terminals[j];
                  temp_global_path.second = Nets[Nets[i].symCounterpart].terminals[j];
                  global_path.push_back(temp_global_path);
               }


         }

       std::cout<<"Gcell Detail Router Check point 6"<<std::endl;
       Grid grid(Gcell, global_path, drc_info, chip_LL, chip_UR, lowest_metal, highest_metal, grid_scale);
//////QQQ1 end of grid creation
       //grid.CheckVerticesTotal();
       //grid.CreateGridData();
       //collect pins & collect metal path
       std::cout<<"starting check find pin"<<std::endl;
       RouterDB::point gridll=grid.GetGridLL();
       RouterDB::point gridur=grid.GetGridUR();
       std::cout<<"Detail path region ( "<<gridll.x<<" "<<gridll.y<<") ( "<<gridur.x<<" "<<gridur.y<<" ) "<<std::endl;
//QQQQ
       std::cout<<"Gcell Detail Router Check point 8"<<std::endl;
       std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > plist = FindsetPlist(Set_x, gridll, gridur);

       std::cout<<"Gcell Detail Router Check point 9"<<std::endl;
       grid.InactivePointlist(plist);//+back

       std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > temp_netplist = FindsetPlist(Set_net, gridll, gridur);
       std::cout<<"Detail Router check point 1.3"<<std::endl;
       grid.InactivePointlist(temp_netplist);//+back

       std::cout<<"Gcell Detail Router Check point 9.1"<<std::endl;


       int sym_flag = 0;

       std::cout<<"Gcell Detail Router Check point 7"<<std::endl;
       //CheckTile(Nets[i], Gcell);

       if(Nets[i].symCounterpart!=-1 and Nets[i].symCounterpart < Nets.size()-1){       
           sym_flag = findPins_Sym(grid, Nets[i], Nets[Nets[i].symCounterpart], Nets[i].sym_H, Nets[i].center, temp_pins, sym_temp_pins, common_pins);
           if(sym_flag == 1){

             std::cout<<"sym_flag exist"<<std::endl;
             SortPins(temp_pins);
             SortPins(sym_temp_pins);
             SortPins(common_pins);
             temp_pins = common_pins;
           }

          }else{

            std::cout<<"Net index "<<i<<std::endl;
            std::cout<<"temp_ pin size "<<temp_pins.size()<<std::endl;
            temp_pins = findPins_new(grid, Nets[i]);
            std::cout<<"temp_ pin size "<<temp_pins.size()<<std::endl;
            SortPins(temp_pins);
          }

       //JudgeTileCoverage(Nets[i].STs[STindex].path, temp_pins, Gcell);

       std::cout<<"end check find pin"<<std::endl;

//QQQQ
       if(sym_flag==1 and Nets[i].global_sym!=-1 and Nets[i].global_sym <Nets.size()-1){
           
            RouterDB::point global_sym_gridll;
            RouterDB::point global_sym_gridur;
            //FindBoundryofGlobalSymNet(gridll,gridur,global_sym_gridll,global_sym_gridur,Nets[i].sym_H,Nets[i].center, Nets[i].global_sym);
           
         }



      // void InactivePointlist(std::vector< std::set<RouterDB::point, RouterDB::pointXYComp> > &plist);
       RouterDB::point sym_gridll = gridll;
       RouterDB::point sym_gridur = gridur;
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
       
       //initial source
       std::vector<RouterDB::SinkData> temp_source;
       std::vector<std::vector<RouterDB::point> > add_plist;
       add_plist.resize(this->layerNo);
       //temp_source = temp_pins[0];
       
       for(int j = 0;j<temp_pins[0].size();j++){
            temp_source.push_back(temp_pins[0][j]);
          }

       int source_lock = 0;
       for(int j=1;j<temp_pins.size();j++){
           //create dest
           std::cout<<"Working on dest "<<j<<std::endl;
           std::vector<RouterDB::SinkData> temp_dest = temp_pins[j];
           std::cout<<"Detail Router check point 1"<<std::endl;
           std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap;
           //std::vector<RouterDB::contact> Terminal_contact=grid.setSrcDest( temp_source, temp_dest, this->width, this->height, Smap);
           grid.setSrcDest( temp_source, temp_dest, this->width, this->height, Smap);
           std::cout<<"Detail Router check point 1.1"<<std::endl;
           grid.ActivateSourceDest();
           std::cout<<"Detail Router check point 1.2"<<std::endl;
           std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > netplist = FindsetPlist(Set_net, gridll, gridur);
           std::cout<<"Detail Router check point 1.3"<<std::endl;
           grid.InactivePointlist(netplist);//+back
           std::cout<<"Detail Router check point 2"<<std::endl;
           std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > sym_net_plist;
           if(sym_flag == 1){

              //inactivate the point in the sym part, then recover those node in the end
              CreatePlistSymNets(sym_net_plist, sym_gridll, sym_gridur, Nets[i].sym_H, Nets[i].center, gridll, gridll);
              grid.InactivePointlist(sym_net_plist);
              
             }

           //std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap;
           //Terminal_contact=grid.setSrcDest_detail( temp_source, temp_dest, this->width, this->height, Smap);
           grid.setSrcDest_detail( temp_source, temp_dest, this->width, this->height, Smap);

           for(int pin_size = 0; pin_size<temp_source.size(); pin_size++){

               std::cout<<"source rec ( "<<temp_source[pin_size].coord[0].x<<" "<<temp_source[pin_size].coord[0].y<<" ) ( "<<temp_source[pin_size].coord[1].x<<" "<<temp_source[pin_size].coord[1].y<<" ) "<<"metal index "<<temp_source[pin_size].metalIdx<<std::endl; 

              }

           for(int pin_size = 0; pin_size<temp_dest.size(); pin_size++){

               std::cout<<"dest rec ( "<<temp_dest[pin_size].coord[0].x<<" "<<temp_dest[pin_size].coord[0].y<<" ) ( "<<temp_dest[pin_size].coord[1].x<<" "<<temp_dest[pin_size].coord[1].y<<" ) "<<"metal index "<<temp_dest[pin_size].metalIdx<<std::endl; 

              }

           std::cout<<"Detail Router check point 3"<<std::endl;
//what about this problem?????
           grid.PrepareGraphVertices(gridll.x, gridll.y, gridur.x, gridur.y); //QQQQQto be fixed
//what about this problem?????
           //Graph graph(grid, this->path_number);
           Graph graph(grid);
           std::cout<<"Detail Router check point 4"<<std::endl;
           bool pathMark= graph.FindFeasiblePath(grid, this->path_number);
           std::cout<<"Current Net index "<<i<<"Current Net pin index "<<j<<" pathMark "<<pathMark<<std::endl;
           int stop_flag = 0;
           std::cout<<"Detail Router check point 5"<<std::endl;
           std::vector<std::vector<RouterDB::Metal> > physical_path;
           if(pathMark) {
           physical_path=graph.ConvertPathintoPhysical(grid);
           std::cout<<"Detail Router check point 6"<<std::endl;
           //lastmile connection source
           //check first point of physical path
           lastmile_source_new(physical_path,temp_source);
           //lastmile connection dest
             //check last point of physical path 
           std::cout<<"Detail Router check point 7"<<std::endl;
           lastmile_dest_new(physical_path,temp_dest);

           //return physical path to net
           //splitPath(physical_path, Nets[i]);
           returnPath(physical_path, Nets[i]);
           }else{
           std::cout<<"Router-Warning: feasible path might not be found\n";
           std::cout<<Nets[i].netName<<std::endl;
           }

           std::cout<<"Detail Router check point 8"<<std::endl;
           //update physical path to 
           UpdatePlistNets(physical_path, add_plist);
           if(sym_flag ==1){
              
             }

           if(source_lock==1){
              temp_source.clear();
              source_lock = 1;
             }

           //add
           std::cout<<"Detail Router check point 9"<<std::endl;
           updateSource(physical_path, temp_source);// wbxu: temp_dest might need be appended into temp_source
           grid.InactivateSourceDest();
           std::cout<<"Detail Router check point 9.1"<<std::endl;
           //grid.ActivePointlist(sym_net_plist);
           std::cout<<"Detail Router check point 9.2"<<std::endl;

           for(int p=0;p<temp_dest.size();p++){
                 temp_source.push_back(temp_dest[p]);
              }
          }
        std::cout<<"Detail Router check point 10"<<std::endl;
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

      std::cout<<"Detail Router check point 11"<<std::endl;
      InsertPlistToSet_x(Set_net, add_plist);

     }


};


/*
void DetailRouter::FindBoundryofGlobalSymNet(RouterDB::point &gridll,RouterDB::point &gridur, RouterDB::point &global_sym_gridll, RouterDB::point &global_sym_gridur, bool H, int center, int index_sym){

  
  FinBoundryNet(index_sym, global_sym_gridll, global_sym_gridur);

  RouterDB::SinkData temp_contact;
  RouterDB::SinkData cover_contact;

  temp_contact.metalIdx = -1;
  temp_contact.coord.push_back(gridll);
  temp_contact.coord.push_back(gridur);

  RouterDB::SinkData sym_temp_contact = Sym_contact(temp_contact, H, center);

  int common_flag = Cover_Contact(temp_contact, sym_temp_contact, cover_contact);

  if(common_flag==1){
     gridll = cover_contact.coord[0];
     gridur = cover_contact.coord[1];
    }else{
     std::cout<<"Grid boundary Error"<<std::endl;
    }


};

*/
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

  for(int i=0;i<tile_index.size();i++){

      std::cout<<"Path ( "<<Gcell.tiles_total[tile_index[i].first].x<<" "<<Gcell.tiles_total[tile_index[i].first].y<<" ) ( "<<Gcell.tiles_total[tile_index[i].second].x<<" "<<Gcell.tiles_total[tile_index[i].second].y<<" ) "<<std::endl;
      std::cout<<"Region ( "<<Gcell.tiles_total[tile_index[i].first].x - Gcell.tiles_total[tile_index[i].first].width/2<<" "<<Gcell.tiles_total[tile_index[i].first].y - Gcell.tiles_total[tile_index[i].first].height/2<<" ) ( "<<Gcell.tiles_total[tile_index[i].first].x + Gcell.tiles_total[tile_index[i].first].width/2<<" "<<Gcell.tiles_total[tile_index[i].first].y + Gcell.tiles_total[tile_index[i].first].height/2<<" ) "<<std::endl;
      std::cout<<"Region ( "<<Gcell.tiles_total[tile_index[i].second].x - Gcell.tiles_total[tile_index[i].second].width/2<<" "<<Gcell.tiles_total[tile_index[i].second].y - Gcell.tiles_total[tile_index[i].second].height/2<<" ) ( "<<Gcell.tiles_total[tile_index[i].second].x + Gcell.tiles_total[tile_index[i].second].width/2<<" "<<Gcell.tiles_total[tile_index[i].second].y + Gcell.tiles_total[tile_index[i].second].height/2<<" ) "<<std::endl;

     }

  std::cout<<"Terminal info"<<std::endl;

  for(int i=0;i<temp_net.connected.size();i++){

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

  for(int i=0;i<tile_index.size();i++){

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

  for(int i=0;i<tiles.size();i++){

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

   for(int i=0;i<temp_pins.size();i++){
       int found_flag = 0;
       for(int j=0;j<temp_pins[i].size();j++){
           for(int k=0;k<tile_range.size();k++){

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

  for(int i=0;i<temp_contact.size();i++){

       for(int j=0;j<sym_temp_contact.size();j++){

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

    for(int i=0;i<temp_pins.size();i++){

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

std::vector<std::vector<RouterDB::SinkData> > GcellDetailRouter::findPins_new(Grid& grid, RouterDB::Net &temp_net){


   std::cout<<"Check point 1"<<std::endl;

   std::vector<std::vector<RouterDB::SinkData> > temp_Pin;

   std::cout<<"connected number "<<temp_net.connected.size()<<std::endl;

   int sum = 0;

   for(int i=0;i<temp_net.connected.size();i++){

      std::vector<RouterDB::SinkData> temp_contacts;

      if(temp_net.connected[i].type == RouterDB::BLOCK){
         
         int contact_number = this->Blocks.at(temp_net.connected[i].iter2).pins.at(temp_net.connected[i].iter).pinContacts.size();

         for(int j=0;j<contact_number;j++){
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
                for(int k=0;k<Terminal_contact.size();k++){
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

/*
   std::cout<<"Seg info of Net"<<std::endl;
   std::cout<<"Seg number"<<temp_net.seg.size()<<std::endl;
   for(int i=0;i<temp_net.seg.size();i++){
       std::cout<<"sourcelist"<<std::endl;
       for(int j=0;j<temp_net.seg[i].sourceList.size();j++){
           if(temp_net.seg[i].sourceList[j].metalIdx!=-1){std::cout<<"{ ("<<temp_net.seg[i].sourceList[j].coord[0].x<<" "<<temp_net.seg[i].sourceList[j].coord[0].y<<" ),("<<temp_net.seg[i].sourceList[j].coord[1].x<<" "<<temp_net.seg[i].sourceList[j].coord[1].y<<") }"<<std::endl;}
          }

       std::cout<<"destlist"<<std::endl;
       for(int j=0;j<temp_net.seg[i].destList.size();j++){
           if(temp_net.seg[i].destList[j].metalIdx!=-1){std::cout<<"{ ("<<temp_net.seg[i].destList[j].coord[0].x<<" "<<temp_net.seg[i].destList[j].coord[0].y<<" ),("<<temp_net.seg[i].destList[j].coord[1].x<<" "<<temp_net.seg[i].destList[j].coord[1].y<<") }"<<std::endl;}
          }
       
      }
*/   

/*
   for(int i=0;i<temp_net.seg.size();i++){

       std::vector<RouterDB::SinkData> temp_pin_s;
       for(int j=0;j<temp_net.seg[i].sourceList.size();j++){
            if(temp_net.seg[i].sourceList[j].metalIdx!=-1){
                temp_pin_s.push_back(temp_net.seg[i].sourceList[j]);
              }
          }

       std::vector<RouterDB::SinkData> temp_pin_d;
       for(int j =0;j<temp_net.seg[i].destList.size();j++){
            if(temp_net.seg[i].destList[j].metalIdx!=-1){
                temp_pin_d.push_back(temp_net.seg[i].destList[j]);
              }            
          }
       
       std::vector<RouterDB::SinkData> temp_pin_ss;
       for(int j=0;j<temp_pin_s.size();j++){
            int found = 0;
            for(int k=0;k<temp_Pin.size();k++){
               for(int l=0;l<temp_Pin[k].size();l++){
                  if(temp_pin_s[j].coord[0].x==temp_Pin[k][l].coord[0].x and temp_pin_s[j].coord[0].y==temp_Pin[k][l].coord[0].y and temp_pin_s[j].coord[1].x==temp_Pin[k][l].coord[1].x and temp_pin_s[j].coord[1].y==temp_Pin[k][l].coord[1].y and temp_pin_s[j].metalIdx == temp_Pin[k][l].metalIdx){found=1;}
                  }
               }
            if(found==0){temp_pin_ss.push_back(temp_pin_s[j]);}
          }
       
       if(temp_pin_ss.size()>0){temp_Pin.push_back(temp_pin_ss);}

       std::vector<RouterDB::SinkData> temp_pin_dd;
       for(int j=0;j<temp_pin_d.size();j++){
            int found = 0;
            for(int k=0;k<temp_Pin.size();k++){
               for(int l=0;l<temp_Pin[k].size();l++){
                  if(temp_pin_d[j].coord[0].x==temp_Pin[k][l].coord[0].x and temp_pin_d[j].coord[0].y==temp_Pin[k][l].coord[0].y and temp_pin_d[j].coord[1].x==temp_Pin[k][l].coord[1].x and temp_pin_d[j].coord[1].y==temp_Pin[k][l].coord[1].y and temp_pin_d[j].metalIdx == temp_Pin[k][l].metalIdx){found=1;}
                  }
               }
            if(found==0){temp_pin_dd.push_back(temp_pin_d[j]);}
          }

       if(temp_pin_dd.size()>0){temp_Pin.push_back(temp_pin_dd);}
      }
*/
  //sort all the dis


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

  for(int i=0;i<temp_Pin.size();i++){
      int temp_dis=INT_MAX;
       for(int j=0;j<temp_Pin[i].size();j++){
            std::cout<<"temp_Pin coord size "<<temp_Pin[i][j].coord.size()<<std::endl;
            for(int k=0;k<temp_label_point.size();k++){
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
   for(int i=0;i<dis.size();i++){
       index.push_back(i);
      }

   int temp_dist;
   int temp_index;

   std::cout<<"start sort pins 3"<<std::endl;

   for(int i=0;i<dis.size();i++){
       for(int j=i+1;j<dis.size();j++){
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
   for(int i=0;i<dis.size();i++){
         Pin.push_back(temp_Pin[index[i]]);
      }
/*
  for(int i=0;i<temp_Pin.size();i++){
       for(int j=0;j<temp_Pin[i].size();j++){
            for(int k=0;k<temp_Pin.size();k++){
                 for(int l=0;l<temp_Pin[k].size();l++){ 
                       if(i==k and j==l){continue;}
                       if(temp_Pin[i][j].coord[0].x == temp_Pin[k][l].coord[0].x and temp_Pin[i][j].coord[0].y == temp_Pin[k][l].coord[0].y and temp_Pin[i][j].coord[1].x == temp_Pin[k][l].coord[1].x and temp_Pin[i][j].coord[1].y == temp_Pin[k][l].coord[1].y and temp_Pin[i][j].metalIdx == temp_Pin[k][l].metalIdx){std::cout<<"Pin Error"<<std::endl;}
                    }
               }
          }
     }
*/
  temp_Pin = Pin;

  std::cout<<"End sort pins"<<std::endl;

};



std::vector<RouterDB::Metal> GcellDetailRouter::findGlobalPath(RouterDB::Net temp_net){

  std::vector<RouterDB::Metal> temp_metal;
  
  for(int i=0;i<temp_net.seg.size();i++){

     int chosenCand = temp_net.seg[i].chosenCand;
     if(chosenCand==-1) {continue;}
     for(int j=0;j<temp_net.seg[i].candis[chosenCand].metals.size();j++){

          temp_metal.push_back(temp_net.seg[i].candis[chosenCand].metals[j]);

        }
     
     }
  
  return temp_metal;

};

void GcellDetailRouter::splitPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::Net& temp_net){

  RouterDB::point temp_point = temp_path[0][0].LinePoint[0];
  int temp_metalIdx = temp_path[0][0].MetalIdx;
  int found_index = -1;

  RouterDB::point Lpoint;
  RouterDB::point Upoint;

  for(int i = 0;i<temp_net.path_metal.size();i++){


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


void GcellDetailRouter::lastmile_source_new(std::vector<std::vector<RouterDB::Metal> > &temp_path, std::vector<RouterDB::SinkData> temp_source){

  RouterDB::point temp_point = temp_path[0][0].LinePoint[0];
  int temp_metal_metalidx = temp_path[0][0].MetalIdx;
  //int temp_metal_metalidx = 5;
  int point_flag; // 0 is ll, 1 is ur

  RouterDB::point source_point;
  int source_metal;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for(int i =0;i<temp_source.size();i++){
     
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


void GcellDetailRouter::lastmile_dest_new(std::vector<std::vector<RouterDB::Metal> > &temp_path, std::vector<RouterDB::SinkData> temp_source){

  int last_index = temp_path[0].size()-1;
  RouterDB::point temp_point = temp_path[0][last_index].LinePoint[1];
  int temp_metal_metalidx = temp_path[0][last_index].MetalIdx;
  //int temp_metal_metalidx = 6;

  RouterDB::point source_point;
  int source_metal;
  int point_flag;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for(int i =0;i<temp_source.size();i++){
     
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


void GcellDetailRouter::lastmile_source(std::vector<std::vector<RouterDB::Metal> > &temp_path, std::vector<RouterDB::SinkData> temp_source){

  RouterDB::point temp_point = temp_path[0][0].LinePoint[0];
  int temp_metal_metalidx = temp_path[0][0].MetalIdx;
  int point_flag; // 0 is ll, 1 is ur

  RouterDB::point source_point;
  int source_metal;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for(int i =0;i<temp_source.size();i++){
       
     if(temp_point.x>=temp_source[i].coord[0].x and temp_point.y>=temp_source[i].coord[0].y and temp_point.x<=temp_source[i].coord[1].x and temp_point.y<=temp_source[i].coord[1].y){connected = 1;break;}

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


  if(connected == 0){

      std::cout<<"source unconnected"<<std::endl;
      std::cout<<"Source point ("<<source_point.x<<" "<<source_point.y<<")"<<std::endl;
      std::cout<<"Dest point ("<<temp_point.x<<" "<<temp_point.y<<")"<<std::endl;      
    
      RouterDB::Metal temp_metal;
      temp_metal.MetalIdx = temp_metal_metalidx;
      temp_metal.width = drc_info.Metal_info[temp_metal_metalidx].width;

      

      if(temp_point.x == source_point.x){
        temp_metal.LinePoint.push_back(source_point); 
        temp_metal.LinePoint.push_back(temp_point);
        std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
        temp_path[0].insert(temp_path[0].begin(),temp_metal);
        std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl;           
 
        }else if(temp_point.y == source_point.y){
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
        temp_path[0].insert(temp_path[0].begin(),temp_metal);
        std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl;   


        }else {

        if(point_flag == 1){

           if(drc_info.Metal_info[temp_metal_metalidx].direct == 0 ){//v
               

               source_point.y = source_point.y-drc_info.Metal_info[temp_metal_metalidx].width/2;
               temp_metal.LinePoint.push_back(source_point);
               if(source_point.x>temp_point.x){source_point.x = temp_point.x - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.x = temp_point.x + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].begin(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.x = temp_point.x;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].begin()+1,temp_metal); 

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
               
               std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl; 
               std::cout<<temp_path[0][1].LinePoint[0].x<<" "<<temp_path[0][1].LinePoint[0].y<<" "<<temp_path[0][1].LinePoint[1].x<<" "<<temp_path[0][1].LinePoint[1].y<<std::endl;             
            
             }else{//h

               source_point.x = source_point.x-drc_info.Metal_info[temp_metal_metalidx].width/2;
               temp_metal.LinePoint.push_back(source_point);
               if(source_point.y>temp_point.y){source_point.y = temp_point.y - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.y = temp_point.y + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].begin(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.y = temp_point.y;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].begin()+1,temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
               
               std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl; 
               std::cout<<temp_path[0][1].LinePoint[0].x<<" "<<temp_path[0][1].LinePoint[0].y<<" "<<temp_path[0][1].LinePoint[1].x<<" "<<temp_path[0][1].LinePoint[1].y<<std::endl;


             }

           }else{

           if(drc_info.Metal_info[temp_metal_metalidx].direct == 0 ){//v

               source_point.y = source_point.y+drc_info.Metal_info[temp_metal_metalidx].width/2;
               temp_metal.LinePoint.push_back(source_point);
               if(source_point.x>temp_point.x){source_point.x = temp_point.x - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.x = temp_point.x + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].begin(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.x = temp_point.x;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].begin()+1,temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
               
               std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl; 
               std::cout<<temp_path[0][1].LinePoint[0].x<<" "<<temp_path[0][1].LinePoint[0].y<<" "<<temp_path[0][1].LinePoint[1].x<<" "<<temp_path[0][1].LinePoint[1].y<<std::endl;               
            
             }else{//h

               source_point.x = source_point.x+drc_info.Metal_info[temp_metal_metalidx].width/2;
               temp_metal.LinePoint.push_back(source_point);
               if(source_point.y>temp_point.y){source_point.y = temp_point.y - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.y = temp_point.y + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].begin(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.y = temp_point.y;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].begin()+1,temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
               
               std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<" "<<temp_path[0][0].LinePoint[1].y<<std::endl; 
               std::cout<<temp_path[0][1].LinePoint[0].x<<" "<<temp_path[0][1].LinePoint[0].y<<" "<<temp_path[0][1].LinePoint[1].x<<" "<<temp_path[0][1].LinePoint[1].y<<std::endl;


             }



           }
          
        }
      
     
      
    
    }

};

void GcellDetailRouter::lastmile_dest(std::vector<std::vector<RouterDB::Metal> > &temp_path, std::vector<RouterDB::SinkData> temp_source){

  int last_index = temp_path[0].size()-1;
  RouterDB::point temp_point = temp_path[0][last_index].LinePoint[1];
  //int temp_metal_metalidx = temp_path[0][last_index].MetalIdx;
  int temp_metal_metalidx = 6;

  RouterDB::point source_point;
  int source_metal;
  int point_flag;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for(int i =0;i<temp_source.size();i++){
       
       
     if(temp_point.x>=temp_source[i].coord[0].x and temp_point.y>=temp_source[i].coord[0].y and temp_point.x<=temp_source[i].coord[1].x and temp_point.y<=temp_source[i].coord[1].y){connected = 1;}

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
      temp_metal.width = drc_info.Metal_info[temp_metal_metalidx].width;
      //temp_metal.LinePoint.push_back(source_point);

      if(temp_point.x == source_point.x){
        temp_metal.LinePoint.push_back(source_point); 
        temp_metal.LinePoint.push_back(temp_point);
        std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
        temp_path[0].insert(temp_path[0].end(),temp_metal);
        int last_end_index = temp_path[0].size()-1;
        std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;           
 
        }else if(temp_point.y == source_point.y){
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
        temp_path[0].insert(temp_path[0].end(),temp_metal);
        int last_end_index = temp_path[0].size()-1;
        std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;


        }else {

        if(point_flag == 1){

           if(drc_info.Metal_info[temp_metal_metalidx].direct == 0 ){//v

               temp_metal.LinePoint.push_back(source_point);
               temp_point.y = temp_point.y - drc_info.Metal_info[temp_metal_metalidx].width/2;
               if(source_point.y>temp_point.y){source_point.y = temp_point.y - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.y = temp_point.y + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.y = temp_point.y;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
 
               int last_end_index = temp_path[0].size()-1;
               std::cout<<temp_path[0][last_end_index-1].LinePoint[0].x<<" "<<temp_path[0][last_end_index-1].LinePoint[0].y<<" "<<temp_path[0][last_end_index-1].LinePoint[1].x<<" "<<temp_path[0][last_end_index-1].LinePoint[1].y<<std::endl;
               std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;            
            
             }else{//h

               temp_metal.LinePoint.push_back(source_point);
               temp_point.x = temp_point.x - drc_info.Metal_info[temp_metal_metalidx].width/2;
               if(source_point.x>temp_point.x){source_point.x = temp_point.x - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.x = temp_point.x + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.x = temp_point.x;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
 
               int last_end_index = temp_path[0].size()-1;
               std::cout<<temp_path[0][last_end_index-1].LinePoint[0].x<<" "<<temp_path[0][last_end_index-1].LinePoint[0].y<<" "<<temp_path[0][last_end_index-1].LinePoint[1].x<<" "<<temp_path[0][last_end_index-1].LinePoint[1].y<<std::endl;
               std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;


             }

           }else{

           if(drc_info.Metal_info[temp_metal_metalidx].direct == 0 ){//v

               temp_metal.LinePoint.push_back(source_point);
               temp_point.y = temp_point.y + drc_info.Metal_info[temp_metal_metalidx].width/2;
               if(source_point.y>temp_point.y){source_point.y = temp_point.y - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.y = temp_point.y + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.y = temp_point.y;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
 
               int last_end_index = temp_path[0].size()-1;
               std::cout<<temp_path[0][last_end_index-1].LinePoint[0].x<<" "<<temp_path[0][last_end_index-1].LinePoint[0].y<<" "<<temp_path[0][last_end_index-1].LinePoint[1].x<<" "<<temp_path[0][last_end_index-1].LinePoint[1].y<<std::endl;
               std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;            
            
             }else{//h

               temp_metal.LinePoint.push_back(source_point);
               temp_point.x = temp_point.x + drc_info.Metal_info[temp_metal_metalidx].width/2;
               if(source_point.x>temp_point.x){source_point.x = temp_point.x - drc_info.Metal_info[temp_metal_metalidx].width/2;}else{source_point.x = temp_point.x + drc_info.Metal_info[temp_metal_metalidx].width/2;}
               temp_metal.LinePoint.push_back(source_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;

               source_point.x = temp_point.x;
               temp_metal.LinePoint.clear();
               temp_metal.LinePoint.push_back(source_point);
               temp_metal.LinePoint.push_back(temp_point);
               temp_path[0].insert(temp_path[0].end(),temp_metal);

               std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
 
               int last_end_index = temp_path[0].size()-1;
               std::cout<<temp_path[0][last_end_index-1].LinePoint[0].x<<" "<<temp_path[0][last_end_index-1].LinePoint[0].y<<" "<<temp_path[0][last_end_index-1].LinePoint[1].x<<" "<<temp_path[0][last_end_index-1].LinePoint[1].y<<std::endl;
               std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;


             }



           }

/*
        source_point.x = temp_point.x;
        temp_metal.LinePoint.push_back(source_point);
        std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
        temp_path[0].insert(temp_path[0].end(),temp_metal);
        temp_metal.LinePoint.clear();
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<") "<<std::endl;
        temp_path[0].insert(temp_path[0].end(),temp_metal); 
        int last_end_index = temp_path[0].size()-1;
        std::cout<<temp_path[0][last_end_index-1].LinePoint[0].x<<" "<<temp_path[0][last_end_index-1].LinePoint[0].y<<" "<<temp_path[0][last_end_index-1].LinePoint[1].x<<" "<<temp_path[0][last_end_index-1].LinePoint[1].y<<std::endl;
        std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<" "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
*/

          
        }
    }

};

void GcellDetailRouter::updateSource(std::vector<std::vector<RouterDB::Metal> > temp_path, std::vector<RouterDB::SinkData>& temp_source){

  RouterDB::SinkData temp_sink;
  int width = 1;

  for(int i=0;i<temp_path.size();i++){

     for(int j=0;j<temp_path[i].size();j++){
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

void GcellDetailRouter::returnPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::Net& temp_net){

  for(int i=0;i<temp_path.size();i++){
       
     for(int j=0;j<temp_path[i].size();j++){

         temp_net.path_metal.push_back(temp_path[i][j]);
     
        }
     }

};



void GcellDetailRouter::Physical_metal_via(){
  
   for(int i=0;i<Nets.size();i++){
             
           GetPhsical_Metal_Via(i);
     
      }

};


void GcellDetailRouter::GetPhsical_Metal_Via(int i){
  
  for(int h=0;h<Nets[i].path_metal.size();h++){

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

  for(int h=0;h<Nets[i].path_metal.size();h++){
       int temp_metal_index = Nets[i].path_metal[h].MetalIdx;
       for(int l=0;l<Nets[i].path_metal.size();l++){

            int next_metal_index = Nets[i].path_metal[l].MetalIdx;

            if(l==h){continue;}

            if(temp_metal_index == next_metal_index -1){
                
                if(Nets[i].path_metal[h].LinePoint[0].x==Nets[i].path_metal[l].LinePoint[0].x and Nets[i].path_metal[h].LinePoint[0].y==Nets[i].path_metal[l].LinePoint[0].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[0];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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

                  set_via.insert(temp_via);
                  }

                if(Nets[i].path_metal[h].LinePoint[0].x==Nets[i].path_metal[l].LinePoint[1].x and Nets[i].path_metal[h].LinePoint[0].y==Nets[i].path_metal[l].LinePoint[1].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[0];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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

                  set_via.insert(temp_via);
                  }

                if(Nets[i].path_metal[h].LinePoint[1].x==Nets[i].path_metal[l].LinePoint[0].x and Nets[i].path_metal[h].LinePoint[1].y==Nets[i].path_metal[l].LinePoint[0].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[1];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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

                  set_via.insert(temp_via);
                  }

                if(Nets[i].path_metal[h].LinePoint[1].x==Nets[i].path_metal[l].LinePoint[1].x and Nets[i].path_metal[h].LinePoint[1].y==Nets[i].path_metal[l].LinePoint[1].y){
                  temp_via.position = Nets[i].path_metal[h].LinePoint[1];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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
  int mIdx, LLx, LLy, URx, URy;
  for(std::vector<RouterDB::Block>::iterator bit=Blocks.begin(); bit!=Blocks.end(); ++bit) {
    // 1. collect pin contacts on grids
    for(std::vector<RouterDB::Pin>::iterator pit=bit->pins.begin(); pit!=bit->pins.end(); ++pit) {
      for(std::vector<RouterDB::contact>::iterator cit=pit->pinContacts.begin(); cit!=pit->pinContacts.end(); ++cit) {
        mIdx=cit->metal;
        LLx=cit->placedLL.x;
        LLy=cit->placedLL.y;
        URx=cit->placedUR.x;
        URy=cit->placedUR.y;
        
        if(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y){
            continue;
          }else{
            Contacts.push_back(*cit);
          }
      }
      for(std::vector<RouterDB::Via>::iterator cit=pit->pinVias.begin(); cit!=pit->pinVias.end(); ++cit) {
        mIdx=cit->UpperMetalRect.metal;
        LLx=cit->UpperMetalRect.placedLL.x;
        LLy=cit->UpperMetalRect.placedLL.y;
        URx=cit->UpperMetalRect.placedUR.x;
        URy=cit->UpperMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 2 "<<mIdx<<std::endl;

        if(!(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y)){
           
            Contacts.push_back(cit->UpperMetalRect);
          }

        mIdx=cit->LowerMetalRect.metal;
        LLx=cit->LowerMetalRect.placedLL.x;
        LLy=cit->LowerMetalRect.placedLL.y;
        URx=cit->LowerMetalRect.placedUR.x;
        URy=cit->LowerMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 3 "<<mIdx<<std::endl;

        if(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y){
            continue;
          }else{
            Contacts.push_back(cit->LowerMetalRect);
          }

      }
    }
    // 2. collect internal metals on grids
    for(std::vector<RouterDB::contact>::iterator pit=bit->InternalMetal.begin(); pit!=bit->InternalMetal.end(); ++pit) {
        //std::cout<<"check point createplistBlocks 4.0 "<<std::endl;
        mIdx=pit->metal;
        LLx=pit->placedLL.x;
        LLy=pit->placedLL.y;
        URx=pit->placedUR.x;
        URy=pit->placedUR.y;
        //std::cout<<"check point createplistBlocks 4 "<<mIdx<<std::endl;
        //std::cout<<"LL ("<<LLx<<","<<LLy<<") UR ("<<URx<<","<<URy<<")"<<std::endl;
        
        if(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y){
            continue;
          }else{
            Contacts.push_back(*pit);
          }

        //std::cout<<"check point createplistBlocks 4.5 "<<std::endl;
    }
    for(std::vector<RouterDB::Via>::iterator pit=bit->InternalVia.begin(); pit!=bit->InternalVia.end(); ++pit) {
        mIdx=pit->UpperMetalRect.metal;
        LLx=pit->UpperMetalRect.placedLL.x;
        LLy=pit->UpperMetalRect.placedLL.y;
        URx=pit->UpperMetalRect.placedUR.x;
        URy=pit->UpperMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 5 "<<mIdx<<std::endl;
        
        if(!(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y)){
           
            Contacts.push_back(pit->UpperMetalRect);
          }

        mIdx=pit->LowerMetalRect.metal;
        LLx=pit->LowerMetalRect.placedLL.x;
        LLy=pit->LowerMetalRect.placedLL.y;
        URx=pit->LowerMetalRect.placedUR.x;
        URy=pit->LowerMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 6 "<<mIdx<<std::endl;
        
        if(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y){
            continue;
          }else{
            Contacts.push_back(pit->LowerMetalRect);
          }

    }

  }

  for(int i=0;i<Contacts.size();i++){

        RouterDB::contact temp_sym_contact = SymContact(Contacts[i], H, center);

        Sym_Contacts.push_back(temp_sym_contact);

     }    

   CreatePlistContact(plist, Sym_Contacts);
   //InsertPlistToSet_x(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, std::vector<std::vector<RouterDB::point> >& plist){
   InsertPlistToSet_x(Set_x, plist);
   set_plist = FindsetPlist(Set_x, symgridll, symgridur);

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
        //std::cout<<"check point createplistBlocks 1 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);

     }

};

void GcellDetailRouter::CreatePlistBlocks(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Block>& Blocks){
  
  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;
  for(std::vector<RouterDB::Block>::iterator bit=Blocks.begin(); bit!=Blocks.end(); ++bit) {
    // 1. collect pin contacts on grids
    for(std::vector<RouterDB::Pin>::iterator pit=bit->pins.begin(); pit!=bit->pins.end(); ++pit) {
      for(std::vector<RouterDB::contact>::iterator cit=pit->pinContacts.begin(); cit!=pit->pinContacts.end(); ++cit) {
        mIdx=cit->metal;
        LLx=cit->placedLL.x;
        LLy=cit->placedLL.y;
        URx=cit->placedUR.x;
        URy=cit->placedUR.y;
        //std::cout<<"check point createplistBlocks 1 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
      }
      for(std::vector<RouterDB::Via>::iterator cit=pit->pinVias.begin(); cit!=pit->pinVias.end(); ++cit) {
        mIdx=cit->UpperMetalRect.metal;
        LLx=cit->UpperMetalRect.placedLL.x;
        LLy=cit->UpperMetalRect.placedLL.y;
        URx=cit->UpperMetalRect.placedUR.x;
        URy=cit->UpperMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 2 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
        mIdx=cit->LowerMetalRect.metal;
        LLx=cit->LowerMetalRect.placedLL.x;
        LLy=cit->LowerMetalRect.placedLL.y;
        URx=cit->LowerMetalRect.placedUR.x;
        URy=cit->LowerMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 3 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
      }
    }
    // 2. collect internal metals on grids
    for(std::vector<RouterDB::contact>::iterator pit=bit->InternalMetal.begin(); pit!=bit->InternalMetal.end(); ++pit) {
        //std::cout<<"check point createplistBlocks 4.0 "<<std::endl;
        mIdx=pit->metal;
        LLx=pit->placedLL.x;
        LLy=pit->placedLL.y;
        URx=pit->placedUR.x;
        URy=pit->placedUR.y;
        //std::cout<<"check point createplistBlocks 4 "<<mIdx<<std::endl;
        //std::cout<<"LL ("<<LLx<<","<<LLy<<") UR ("<<URx<<","<<URy<<")"<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
        //std::cout<<"check point createplistBlocks 4.5 "<<std::endl;
    }
    for(std::vector<RouterDB::Via>::iterator pit=bit->InternalVia.begin(); pit!=bit->InternalVia.end(); ++pit) {
        mIdx=pit->UpperMetalRect.metal;
        LLx=pit->UpperMetalRect.placedLL.x;
        LLy=pit->UpperMetalRect.placedLL.y;
        URx=pit->UpperMetalRect.placedUR.x;
        URy=pit->UpperMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 5 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
        mIdx=pit->LowerMetalRect.metal;
        LLx=pit->LowerMetalRect.placedLL.x;
        LLy=pit->LowerMetalRect.placedLL.y;
        URx=pit->LowerMetalRect.placedUR.x;
        URy=pit->LowerMetalRect.placedUR.y;
        //std::cout<<"check point createplistBlocks 6 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
    }
  }  

};



void GcellDetailRouter::CreatePlistTerminals(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::terminal> Terminals){
  
  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;

  for(int i=0;i<Terminals.size();i++){
      for(int j=0;j<Terminals[i].termContacts.size();j++){
          mIdx = Terminals[i].termContacts[j].metal;
          if(mIdx>=0){
             LLx = Terminals[i].termContacts[j].placedLL.x;
             LLy = Terminals[i].termContacts[j].placedLL.y;
             URx = Terminals[i].termContacts[j].placedUR.x;
             URy = Terminals[i].termContacts[j].placedUR.y;
             ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
           }
         }
     }

};


void GcellDetailRouter::UpdatePlistNets(std::vector<std::vector<RouterDB::Metal> > &physical_path, std::vector<std::vector<RouterDB::point> > &plist){


  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;
  
  GetPhsical_Metal(physical_path);
  
  //here intervia is not included
  for(int i=0;i<physical_path.size();i++){
      for(int j=0;j<physical_path[i].size();j++){
          mIdx = physical_path[i][j].MetalIdx;
          LLx = physical_path[i][j].MetalRect.placedLL.x;
          LLy = physical_path[i][j].MetalRect.placedLL.y;
          URx = physical_path[i][j].MetalRect.placedUR.x;
          URy = physical_path[i][j].MetalRect.placedUR.y;
          ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
         }
     }

  std::vector<RouterDB::contact> temp_via_contact;
  GetPhsical_Via_contacts(physical_path, temp_via_contact);

  for(int i=0;i<temp_via_contact.size();i++){

          mIdx = temp_via_contact[i].metal;
          LLx = temp_via_contact[i].placedLL.x;
          LLy = temp_via_contact[i].placedLL.y;
          URx = temp_via_contact[i].placedUR.x;
          URy = temp_via_contact[i].placedUR.y;
          ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
      
     }


  

};

void GcellDetailRouter::GetPhsical_Via_contacts(std::vector<std::vector<RouterDB::Metal> >physical_path, std::vector<RouterDB::contact> &temp_via_contact){


  RouterDB::Via temp_via;
  std::set<RouterDB::Via, RouterDB::ViaComp> set_via;

  for(int i=0;i<physical_path.size();i++){
       
      std::vector<RouterDB::Metal> temp_path = physical_path[i];

      for(int j=0;j<temp_path.size();j++){

           int temp_metal_index = temp_path[j].MetalIdx;
           
           for(int h=0;h<temp_path.size();h++){

               int next_metal_index = temp_path[h].MetalIdx;

               if(j==h){continue;}

               if(temp_metal_index == next_metal_index -1){
                
                if(temp_path[j].LinePoint[0].x==temp_path[h].LinePoint[0].x and temp_path[j].LinePoint[0].y==temp_path[h].LinePoint[0].y){
                  temp_via.position = temp_path[j].LinePoint[0];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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

                  set_via.insert(temp_via);
                  }

                if(temp_path[j].LinePoint[0].x==temp_path[h].LinePoint[1].x and temp_path[j].LinePoint[0].y==temp_path[h].LinePoint[1].y){
                  temp_via.position = temp_path[j].LinePoint[0];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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

                  set_via.insert(temp_via);
                  }

                if(temp_path[j].LinePoint[1].x==temp_path[h].LinePoint[0].x and temp_path[j].LinePoint[1].y==temp_path[h].LinePoint[0].y){
                  temp_via.position = temp_path[j].LinePoint[1];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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

                  set_via.insert(temp_via);
                  }

                if(temp_path[j].LinePoint[1].x==temp_path[h].LinePoint[1].x and temp_path[j].LinePoint[1].y==temp_path[h].LinePoint[1].y){
                  temp_via.position = temp_path[j].LinePoint[1];
                  temp_via.model_index = temp_metal_index;

                  //ViaRect
                  temp_via.ViaRect.metal = temp_metal_index;
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

void GcellDetailRouter::CreatePlistSymNets(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > &set_plist, RouterDB::point gridll, RouterDB::point gridur, bool H, int center, RouterDB::point symgridll, RouterDB::point symgridur){


  //RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;

  std::vector<RouterDB::contact> Contacts;
  std::vector<RouterDB::contact> Sym_Contacts; 
  //RouterDB::point tmpP;
  std::vector<std::vector<RouterDB::point> > plist;
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x; 

  for(int k=0;k<Nets.size();k++){  
    
      std::vector<std::vector<RouterDB::Metal> > physical_path;
      physical_path.push_back(Nets[k].path_metal); 
      GetPhsical_Metal(physical_path);
      
      for(int i=0;i<physical_path.size();i++){
         for(int j=0;j<physical_path[i].size();j++){
             mIdx = physical_path[i][j].MetalIdx;
             LLx = physical_path[i][j].MetalRect.placedLL.x;
             LLy = physical_path[i][j].MetalRect.placedLL.y;
             URx = physical_path[i][j].MetalRect.placedUR.x;
             URy = physical_path[i][j].MetalRect.placedUR.y;

             if(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y){
                continue;
               }else{
                Contacts.push_back(physical_path[i][j].MetalRect);
               }             

            }
        }

      std::vector<RouterDB::contact> temp_via_contact;
      GetPhsical_Via_contacts(physical_path, temp_via_contact);
      
      for(int i=0;i<temp_via_contact.size();i++){

           mIdx = temp_via_contact[i].metal;
           LLx = temp_via_contact[i].placedLL.x;
           LLy = temp_via_contact[i].placedLL.y;
           URx = temp_via_contact[i].placedUR.x;
           URy = temp_via_contact[i].placedUR.y;          

           if(!(URx<gridll.x or URy<gridll.y or LLx>gridur.x or LLy>gridur.y)){
                Contacts.push_back(temp_via_contact[i]);
               } 
        
         }
      

     }
    
  for(int i=0;i<Contacts.size();i++){

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
  for(int i=0;i<physical_path.size();i++){
       for(int j=0;j<physical_path[i].size();j++){
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
  if(drc_info.Metal_info[mIdx].direct==0) { // vertical metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_x;
    int newLLx=LLx-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    int newURx=URx+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundX=(newLLx%curlayer_unit==0) ? (newLLx+curlayer_unit) : ( (newLLx/curlayer_unit)*curlayer_unit<newLLx ? (newLLx/curlayer_unit+1)*curlayer_unit : (newLLx/curlayer_unit)*curlayer_unit  );
    for(int x=boundX; x<newURx; x+=curlayer_unit) {
      if(mIdx!=obs_l) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_y;
        int newLLy=LLy-nexlayer_unit;
        int newURy=URy+nexlayer_unit;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        for(int y=boundY; y<newURy; y+=nexlayer_unit) {
          if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_y;
        int newLLy=LLy-nexlayer_unit;
        int newURy=URy+nexlayer_unit;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        for(int y=boundY; y<newURy; y+=nexlayer_unit) {
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
        int newLLx=LLx-nexlayer_unit;
        int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        for(int x=boundX; x<newURx; x+=nexlayer_unit) {
           if(x>=LLx and x<=URx and y>=LLy and y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
           //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_x;
        int newLLx=LLx-nexlayer_unit;
        int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        for(int x=boundX; x<newURx; x+=nexlayer_unit) {
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
// Limitation: 
// 1. all the grid nodes around the rectangle will be chosen, 
// only if the rectangle boundary is exactly on grid
// 2. both nodes crossing with upper layer and lower layer will be chosen
// which results in perssimism 
//  RouterDB::point tmpP;
//  if(this->routeDirect.at(mIdx)==0) { // vertical metal layer
//    for(int x=(LLx/x_unit.at(mIdx))*x_unit.at(mIdx); x<=int(ceil((double)URx/x_unit.at(mIdx)))*x_unit.at(mIdx); x+=x_unit.at(mIdx)) {
//      if( mIdx!=this->lowest_metal ) {
//        for(int y=(LLy/y_unit.at(mIdx-1))*y_unit.at(mIdx-1); y<=int(ceil((double)URy/y_unit.at(mIdx-1)))*y_unit.at(mIdx-1); y+=y_unit.at(mIdx-1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//      if( mIdx!=this->highest_metal ) {
//        for(int y=(LLy/y_unit.at(mIdx+1))*y_unit.at(mIdx+1); y<=int(ceil((double)URy/y_unit.at(mIdx+1)))*y_unit.at(mIdx+1); y+=y_unit.at(mIdx+1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//    }
//  } else if (this->routeDirect.at(mIdx)==1) { // horizontal metal layer
//    for(int y=(LLy/y_unit.at(mIdx))*y_unit.at(mIdx); y<=int(ceil((double)URy/y_unit.at(mIdx)))*y_unit.at(mIdx); y+=y_unit.at(mIdx)) {
//      if( mIdx!=this->lowest_metal ) {
//        for(int x=(LLx/x_unit.at(mIdx-1))*x_unit.at(mIdx-1); x<=int(ceil((double)URx/x_unit.at(mIdx-1)))*x_unit.at(mIdx-1); x+=x_unit.at(mIdx-1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//      if( mIdx!=this->highest_metal ) {
//        for(int x=(LLx/x_unit.at(mIdx+1))*x_unit.at(mIdx+1); x<=int(ceil((double)URx/x_unit.at(mIdx+1)))*x_unit.at(mIdx+1); x+=x_unit.at(mIdx+1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//    }
//  } else {
//    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
//  }
}

/*
void DetailRouter::ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  RouterDB::point tmpP;
  //tmpP.iterNet = Net_index;
  if(drc_info.Metal_info[mIdx].direct==0) { // vertical metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_x;
    //int newLLx=LLx-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    //int newURx=URx+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int newLLx=LLx;
    int newURx=URx;
    int boundX=(newLLx%curlayer_unit==0) ? (newLLx+curlayer_unit) : ( (newLLx/curlayer_unit)*curlayer_unit<newLLx ? (newLLx/curlayer_unit+1)*curlayer_unit : (newLLx/curlayer_unit)*curlayer_unit  );
    for(int x=boundX; x<newURx; x+=curlayer_unit) {
      if(mIdx!=this->lowest_metal) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_y;
        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        int newLLy=LLy;
        int newURy=URy;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        for(int y=boundY; y<newURy; y+=nexlayer_unit) {
          tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=this->highest_metal) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_y;
        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        int newLLy=LLy;
        int newURy=URy;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        for(int y=boundY; y<newURy; y+=nexlayer_unit) {
          tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else if(drc_info.Metal_info[mIdx].direct==1) { // horizontal metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_y;
    int newLLy=LLy;
    int newURy=URy;
    //int newLLy=LLy-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    //int newURy=URy+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundY=(newLLy%curlayer_unit==0) ? (newLLy+curlayer_unit) : ( (newLLy/curlayer_unit)*curlayer_unit<newLLy ? (newLLy/curlayer_unit+1)*curlayer_unit : (newLLy/curlayer_unit)*curlayer_unit  );
    for(int y=boundY; y<newURy; y+=curlayer_unit) {
      if(mIdx!=this->lowest_metal) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_x;
        int newLLx=LLx;
        int newURx=URx;
        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        for(int x=boundX; x<newURx; x+=nexlayer_unit) {
          tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=this->highest_metal) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_x;
        int newLLx=LLx;
        int newURx=URx;
        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        for(int x=boundX; x<newURx; x+=nexlayer_unit) {
          tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else {
    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
  }
};
*/

void GcellDetailRouter::NetToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index){
  PnRDB::point tpoint;  

  //including via
  //std::cout<<"Start NetToNodeNet"<<std::endl;
  
  for(int i=0;i<net.path_metal.size();i++){

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
             temp_metal.MetalRect.placedBox.UL.x = net.path_metal[i].MetalRect.placedLL.x;
             temp_metal.MetalRect.placedBox.UL.y = net.path_metal[i].MetalRect.placedUR.y;
             temp_metal.MetalRect.placedBox.LR.x = net.path_metal[i].MetalRect.placedUR.x;
             temp_metal.MetalRect.placedBox.LR.y = net.path_metal[i].MetalRect.placedLL.y;
             temp_metal.MetalRect.placedCenter.x = net.path_metal[i].MetalRect.placedCenter.x;
             temp_metal.MetalRect.placedCenter.y = net.path_metal[i].MetalRect.placedCenter.y;
             //std::cout<<"checkpoint 3"<<std::endl;
             HierNode.Nets[net_index].path_metal.push_back(temp_metal);

     }

  for(int i=0;i<net.path_via.size();i++){
       PnRDB::Via temp_via;
       ConvertToViaPnRDB_Placed_Placed(temp_via,net.path_via[i]);
       HierNode.Nets[net_index].path_via.push_back(temp_via);
     }

};



void GcellDetailRouter::NetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::Net& net){
  //std::cout<<"Start NetToNodeInterMetal"<<std::endl;
  //blockspin to intermetal
  for(int i=0;i<net.connected.size();i++){
      if(net.connected[i].type == RouterDB::BLOCK){
          
          for(int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size();j++){

             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
             HierNode.interMetals.push_back(temp_contact);

             }
          for(int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size();j++){
             
             PnRDB::Via temp_via;
ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
             HierNode.interVias.push_back(temp_via);
             }
        } 
     }

  //std::cout<<"Via"<<std::endl;
  //including via
  for(int i=0;i<net.path_metal.size();i++){
      //std::cout<<"seg "<<i<<std::endl;
        PnRDB::contact temp_contact;
        ConvertToContactPnRDB_Placed_Origin(temp_contact, net.path_metal[i].MetalRect);
        HierNode.interMetals.push_back(temp_contact);
      }
  for(int i=0;i<net.path_via.size();i++){
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

  if(this->isTop){

             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Origin(temp_contact,Terminals.at(net.terminal_idx).termContacts[0]);
             temp_pin.pinContacts.push_back(temp_contact);

    }

  //blockspin to intermetal
  for(int i=0;i<net.connected.size();i++){
      if(net.connected[i].type == RouterDB::BLOCK){
          
          for(int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size();j++){

             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
             temp_pin.pinContacts.push_back(temp_contact);

             }
          for(int j=0;j<Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size();j++){
             
             PnRDB::Via temp_via;
ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
             temp_pin.pinVias.push_back(temp_via);
             }
        } 
     }

  for(int i=0;i<net.path_metal.size();i++){

             // wbxu: placed field -> origin field [fixed]
      PnRDB::contact temp_contact;
      ConvertToContactPnRDB_Placed_Origin(temp_contact,net.path_metal[i].MetalRect);
      temp_pin.pinContacts.push_back(temp_contact);
     }
  for(int i=0;i<net.path_via.size();i++){

             // wbxu: placed field -> origin field [fixed]
      PnRDB::Via temp_via;
      ConvertToViaPnRDB_Placed_Origin(temp_via, net.path_via[i]);  
      temp_pin.pinVias.push_back(temp_via);
     }
          

  HierNode.blockPins.push_back(temp_pin);    
  std::cout<<"END NetToNodeBlockPins"<<std::endl;
};


void GcellDetailRouter::ReturnHierNode(PnRDB::hierNode& HierNode)
{
  HierNode.blockPins.clear();
  HierNode.interMetals.clear();
  HierNode.interVias.clear();

  for(int i=0;i<HierNode.Terminals.size();i++){
      HierNode.Terminals[i].termContacts.clear();
     }

  for(int i=0;i<HierNode.Nets.size();i++){
        HierNode.Nets[i].path_metal.clear();
        HierNode.Nets[i].path_via.clear();
     }

  //distinguish those two net
  //std::cout<<"Start ReturnHierNode"<<std::endl;
  for(int i=0;i<Nets.size();i++){
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
       
       for(int j=0;j<HierNode.Nets.size();j++){
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
  
  if(isTop==1){
    //return terminal to node terminal
    std::cout<<"test terminal to termina: start"<<std::endl;
    TerminalToNodeTerminal(HierNode);
    std::cout<<"test terminal to termina: end"<<std::endl;
    }
  std::cout<<"test blockintermetal to node intermetal: start"<<std::endl;
  BlockInterMetalToNodeInterMetal(HierNode);
  std::cout<<"test blockintermetal to node intermetal: end"<<std::endl;
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
  temp_via.ViaRect.placedBox.UL.x = router_via.ViaRect.placedLL.x;
  temp_via.ViaRect.placedBox.UL.y = router_via.ViaRect.placedUR.y;
  temp_via.ViaRect.placedBox.LR.x = router_via.ViaRect.placedUR.x;
  temp_via.ViaRect.placedBox.LR.y = router_via.ViaRect.placedLL.y;
  temp_via.ViaRect.placedCenter.x = router_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.placedCenter.y = router_via.ViaRect.placedCenter.y; 
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=temp_via.ViaRect.placedBox.LL.x; 
  temp_point.y=temp_via.ViaRect.placedBox.LL.y;
  temp_via.ViaRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.ViaRect.placedBox.UL.x; 
  temp_point.y=temp_via.ViaRect.placedBox.UL.y;
  temp_via.ViaRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.ViaRect.placedBox.UR.x; 
  temp_point.y=temp_via.ViaRect.placedBox.UR.y;
  temp_via.ViaRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.ViaRect.placedBox.LR.x; 
  temp_point.y=temp_via.ViaRect.placedBox.LR.y;
  temp_via.ViaRect.placedBox.polygon.push_back(temp_point);

  //LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Metal_info[router_via.LowerMetalRect.metal].name;
  temp_via.LowerMetalRect.placedBox.LL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.placedBox.LL.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.placedBox.UR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.placedBox.UR.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.placedBox.UL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.placedBox.UL.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.placedBox.LR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.placedBox.LR.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.placedCenter.x = router_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.placedCenter.y = router_via.LowerMetalRect.placedCenter.y;
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=temp_via.LowerMetalRect.placedBox.LL.x; 
  temp_point.y=temp_via.LowerMetalRect.placedBox.LL.y;
  temp_via.LowerMetalRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.LowerMetalRect.placedBox.UL.x; 
  temp_point.y=temp_via.LowerMetalRect.placedBox.UL.y;
  temp_via.LowerMetalRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.LowerMetalRect.placedBox.UR.x; 
  temp_point.y=temp_via.LowerMetalRect.placedBox.UR.y;
  temp_via.LowerMetalRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.LowerMetalRect.placedBox.LR.x; 
  temp_point.y=temp_via.LowerMetalRect.placedBox.LR.y;
  temp_via.LowerMetalRect.placedBox.polygon.push_back(temp_point);

  //UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Metal_info[router_via.UpperMetalRect.metal].name;
  temp_via.UpperMetalRect.placedBox.LL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.placedBox.LL.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.placedBox.UR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.placedBox.UR.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.placedBox.UL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.placedBox.UL.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.placedBox.LR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.placedBox.LR.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.placedCenter.x = router_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.placedCenter.y = router_via.UpperMetalRect.placedCenter.y;
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=temp_via.UpperMetalRect.placedBox.LL.x; 
  temp_point.y=temp_via.UpperMetalRect.placedBox.LL.y;
  temp_via.UpperMetalRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.UpperMetalRect.placedBox.UL.x; 
  temp_point.y=temp_via.UpperMetalRect.placedBox.UL.y;
  temp_via.UpperMetalRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.UpperMetalRect.placedBox.UR.x; 
  temp_point.y=temp_via.UpperMetalRect.placedBox.UR.y;
  temp_via.UpperMetalRect.placedBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.UpperMetalRect.placedBox.LR.x; 
  temp_point.y=temp_via.UpperMetalRect.placedBox.LR.y;
  temp_via.UpperMetalRect.placedBox.polygon.push_back(temp_point);

};

void GcellDetailRouter::ConvertToContactPnRDB_Placed_Origin(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact){

  PnRDB::point temp_point;
  pnr_contact.metal = drc_info.Metal_info[router_contact.metal].name;
  pnr_contact.originBox.LL.x = router_contact.placedLL.x;
  pnr_contact.originBox.LL.y = router_contact.placedLL.y;
  pnr_contact.originBox.UR.x = router_contact.placedUR.x;
  pnr_contact.originBox.UR.y = router_contact.placedUR.y;
  pnr_contact.originBox.UL.x = router_contact.placedLL.x;
  pnr_contact.originBox.UL.y = router_contact.placedUR.y;
  pnr_contact.originBox.LR.x = router_contact.placedUR.x;
  pnr_contact.originBox.LR.y = router_contact.placedLL.y;
  pnr_contact.originCenter.x = router_contact.placedCenter.x;
  pnr_contact.originCenter.y = router_contact.placedCenter.y; 
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=pnr_contact.originBox.LL.x; 
  temp_point.y=pnr_contact.originBox.LL.y;
  pnr_contact.originBox.polygon.push_back(temp_point);
  temp_point.x=pnr_contact.originBox.UL.x; 
  temp_point.y=pnr_contact.originBox.UL.y;
  pnr_contact.originBox.polygon.push_back(temp_point);
  temp_point.x=pnr_contact.originBox.UR.x; 
  temp_point.y=pnr_contact.originBox.UR.y;
  pnr_contact.originBox.polygon.push_back(temp_point);
  temp_point.x=pnr_contact.originBox.LR.x; 
  temp_point.y=pnr_contact.originBox.LR.y;
  pnr_contact.originBox.polygon.push_back(temp_point);

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
  temp_via.ViaRect.originBox.UL.x = router_via.ViaRect.placedLL.x;
  temp_via.ViaRect.originBox.UL.y = router_via.ViaRect.placedUR.y;
  temp_via.ViaRect.originBox.LR.x = router_via.ViaRect.placedUR.x;
  temp_via.ViaRect.originBox.LR.y = router_via.ViaRect.placedLL.y;
  temp_via.ViaRect.originCenter.x = router_via.ViaRect.placedCenter.x;
  temp_via.ViaRect.originCenter.y = router_via.ViaRect.placedCenter.y; 
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=temp_via.ViaRect.originBox.LL.x; 
  temp_point.y=temp_via.ViaRect.originBox.LL.y;
  temp_via.ViaRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.ViaRect.originBox.UL.x; 
  temp_point.y=temp_via.ViaRect.originBox.UL.y;
  temp_via.ViaRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.ViaRect.originBox.UR.x; 
  temp_point.y=temp_via.ViaRect.originBox.UR.y;
  temp_via.ViaRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.ViaRect.originBox.LR.x; 
  temp_point.y=temp_via.ViaRect.originBox.LR.y;
  temp_via.ViaRect.originBox.polygon.push_back(temp_point);

  //LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Metal_info[router_via.LowerMetalRect.metal].name;
  temp_via.LowerMetalRect.originBox.LL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.originBox.LL.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.originBox.UR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.originBox.UR.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.originBox.UL.x = router_via.LowerMetalRect.placedLL.x;
  temp_via.LowerMetalRect.originBox.UL.y = router_via.LowerMetalRect.placedUR.y;
  temp_via.LowerMetalRect.originBox.LR.x = router_via.LowerMetalRect.placedUR.x;
  temp_via.LowerMetalRect.originBox.LR.y = router_via.LowerMetalRect.placedLL.y;
  temp_via.LowerMetalRect.originCenter.x = router_via.LowerMetalRect.placedCenter.x;
  temp_via.LowerMetalRect.originCenter.y = router_via.LowerMetalRect.placedCenter.y;
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=temp_via.LowerMetalRect.originBox.LL.x; 
  temp_point.y=temp_via.LowerMetalRect.originBox.LL.y;
  temp_via.LowerMetalRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.LowerMetalRect.originBox.UL.x; 
  temp_point.y=temp_via.LowerMetalRect.originBox.UL.y;
  temp_via.LowerMetalRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.LowerMetalRect.originBox.UR.x; 
  temp_point.y=temp_via.LowerMetalRect.originBox.UR.y;
  temp_via.LowerMetalRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.LowerMetalRect.originBox.LR.x; 
  temp_point.y=temp_via.LowerMetalRect.originBox.LR.y;
  temp_via.LowerMetalRect.originBox.polygon.push_back(temp_point);

  //UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Metal_info[router_via.UpperMetalRect.metal].name;
  temp_via.UpperMetalRect.originBox.LL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.originBox.LL.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.originBox.UR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.originBox.UR.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.originBox.UL.x = router_via.UpperMetalRect.placedLL.x;
  temp_via.UpperMetalRect.originBox.UL.y = router_via.UpperMetalRect.placedUR.y;
  temp_via.UpperMetalRect.originBox.LR.x = router_via.UpperMetalRect.placedUR.x;
  temp_via.UpperMetalRect.originBox.LR.y = router_via.UpperMetalRect.placedLL.y;
  temp_via.UpperMetalRect.originCenter.x = router_via.UpperMetalRect.placedCenter.x;
  temp_via.UpperMetalRect.originCenter.y = router_via.UpperMetalRect.placedCenter.y;
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=temp_via.UpperMetalRect.originBox.LL.x; 
  temp_point.y=temp_via.UpperMetalRect.originBox.LL.y;
  temp_via.UpperMetalRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.UpperMetalRect.originBox.UL.x; 
  temp_point.y=temp_via.UpperMetalRect.originBox.UL.y;
  temp_via.UpperMetalRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.UpperMetalRect.originBox.UR.x; 
  temp_point.y=temp_via.UpperMetalRect.originBox.UR.y;
  temp_via.UpperMetalRect.originBox.polygon.push_back(temp_point);
  temp_point.x=temp_via.UpperMetalRect.originBox.LR.x; 
  temp_point.y=temp_via.UpperMetalRect.originBox.LR.y;
  temp_via.UpperMetalRect.originBox.polygon.push_back(temp_point);

};

void GcellDetailRouter::TerminalToNodeTerminal(PnRDB::hierNode& HierNode){

   //including via
   //includeing blockpin also

  for(int i=0;i<this->Terminals.size();i++){
       //pins
       for(int j=0;j<this->Terminals[i].termContacts.size();j++){
             
             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Placed(temp_contact,this->Terminals[i].termContacts[j]);

             HierNode.Terminals[i].termContacts.push_back(temp_contact);
                

          }
      }

       
};

void GcellDetailRouter::BlockInterMetalToNodeInterMetal(PnRDB::hierNode& HierNode){

   //including via
   //includeing blockpin also

  for(int i=0;i<Blocks.size();i++){
/*
       //pins
       for(int j=0;j<Blocks[i].pins.size();j++){
           for(int k=0;k<Blocks[i].pins[j].pinContacts;k++){
                //to internal metal
             
             PnRDB::contact temp_contact;
ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[i].pins[j].pinContacts[k]);
             HierNode.interMetals.push_back(temp_contact);
                
              }
           for(int k=0;k<Blocks[i].pins[j].pinVias;k++){
             //to internal via
             PnRDB::Via temp_via;
             ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[i].pins[j].pinVias[k]);             

             HierNode.interVias.push_back(temp_via);   
                
              }
          }
*/
       //InternalMetal
       for(int j=0;j<Blocks[i].InternalMetal.size();j++){
            //to internal metal
             PnRDB::contact temp_contact;
             ConvertToContactPnRDB_Placed_Origin(temp_contact,Blocks[i].InternalMetal[j]);
             HierNode.interMetals.push_back(temp_contact);
          }
       //via
       for(int j=0;j<Blocks[i].InternalVia.size();j++){
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
  pnr_contact.placedBox.UL.x = router_contact.placedLL.x;
  pnr_contact.placedBox.UL.y = router_contact.placedUR.y;
  pnr_contact.placedBox.LR.x = router_contact.placedUR.x;
  pnr_contact.placedBox.LR.y = router_contact.placedLL.y;
  pnr_contact.placedCenter.x = router_contact.placedCenter.x;
  pnr_contact.placedCenter.y = router_contact.placedCenter.y; 
  // wbxu: polygon in originBox should be updated! [fixed]
  temp_point.x=pnr_contact.placedBox.LL.x; 
  temp_point.y=pnr_contact.placedBox.LL.y;
  pnr_contact.placedBox.polygon.push_back(temp_point);
  temp_point.x=pnr_contact.placedBox.UL.x; 
  temp_point.y=pnr_contact.placedBox.UL.y;
  pnr_contact.placedBox.polygon.push_back(temp_point);
  temp_point.x=pnr_contact.placedBox.UR.x; 
  temp_point.y=pnr_contact.placedBox.UR.y;
  pnr_contact.placedBox.polygon.push_back(temp_point);
  temp_point.x=pnr_contact.placedBox.LR.x; 
  temp_point.y=pnr_contact.placedBox.LR.y;
  pnr_contact.placedBox.polygon.push_back(temp_point);

};
