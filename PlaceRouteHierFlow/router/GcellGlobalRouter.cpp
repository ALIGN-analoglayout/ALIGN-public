#include "GcellGlobalRouter.h"


extern "C"
{
#include <stdio.h>
#include "lp_lib.h"
#define LPSOLVEAPIFROMLIBDEF
#include "lp_explicit.h"
}



GcellGlobalRouter::GcellGlobalRouter(){

};

GcellGlobalRouter::GcellGlobalRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, const std::string &binaryDIR){
  
  //1. Initial Drcdata and design data
  std::cout<<"Test 1"<<std::endl;
  getDRCdata(drcData);
  getData(node, Lmetal, Hmetal);
  if(node.isIntelGcellGlobalRouter == false){
    placeTerminals();
  }
  std::cout<<"Test 2"<<std::endl;

  //2. create GcellGlobalGrid
  //CreateGrid for within the region LL, UR
  int tile_size = 0;
  if(UR.x*UR.y<1000000){
      tile_size = 20;
    }else if(UR.x*UR.y<10000000000){
      tile_size = 100;
    }else if(UR.x*UR.y<1000000000000){
      tile_size = 1000;
    }else if(UR.x*UR.y<100000000000000){
      tile_size = 10000;
    }else {
      tile_size = 100000;
    }




  int tileLayerNo = Hmetal-Lmetal + 1;
  if(node.isIntelGcellGlobalRouter == true){
    //SMB Override for Intel router
     tileLayerNo = 1;
     tile_size = 10;
  }
  GlobalGrid Initial_Gcell = GlobalGrid(drc_info, UR.x, UR.y, Lmetal, Hmetal, tileLayerNo, tile_size);
  std::cout<<"Test 3"<<std::endl;
  Initial_Gcell.ConvertGlobalInternalMetal(Blocks);
  std::cout<<"Test 4"<<std::endl;
  Initial_Gcell.AdjustVerticalEdgeCapacityfromInternalMetal(Blocks);
  std::cout<<"Test 5"<<std::endl;
  this->Gcell = GlobalGrid(Initial_Gcell);
  //Gcell = GlobalGrid(Initial_Gcell);
  //for(int i=0;i<Nets.size();++i){
     std::cout<<"Test 6"<<std::endl;
     Gcell.ConvertGlobalBlockPin(Blocks, Nets, Nets.size());
     std::cout<<"Test 7"<<std::endl;
     Gcell.AdjustPlateEdgeCapacity();
     std::cout<<"Test 8"<<std::endl;
     Gcell.AdjustVerticalEdgeCapacityfromBlockPin(Blocks, Nets, Nets.size());
     std::cout<<"Test 9"<<std::endl;
     
  //}
  std::cout<<"Test 10"<<std::endl;
  Gcell.SetNetSink(Blocks, Nets, Terminals);
  //Gcell.CreateGridDataNCap();
  //Gcell.CreateGridDataCap();

  for(unsigned int i=0;i<Nets.size();++i){
     //for(int j=0;j<Nets[i].connectedTile.size();++j){
         std::cout<<"Net "<<i<<" number of connectedTile "<<Nets[i].connectedTile.size()<<std::endl;
         std::cout<<"number of connnected "<<Nets[i].connected.size()<<std::endl;
      //  }
     }

  //return;
  //end of global Grid

  int ST_number = 5;
  std::cout<<"Test 11"<<std::endl;
  GlobalGraph GGgraph(Gcell);

  //here create a tiles set;
  std::set<RouterDB::tile, RouterDB::tileComp> Tile_Set = CreateTileSet(Gcell);

  SymNet(Gcell, Tile_Set);  
  
  for(unsigned int i=0;i<this->Nets.size();++i){

     std::cout<<"Nets symmetry part "<<this->Nets.at(i).symCounterpart<<" Nets global symmetry part "<<this->Nets.at(i).global_sym<<std::endl;
     

     }    

  //3. STs generation
  for(unsigned int i = 0;i<Nets.size();++i){
     //std::cout<<"Nets index "<<i<<std::endl;
     //set terminals
     std::cout<<"Test 12"<<std::endl;
     GGgraph.clearPath();
     std::cout<<"Net index "<<i<<std::endl;
     std::cout<<"Net terminals size "<<Nets[i].terminals.size()<<std::endl;
     GGgraph.setterminals(Nets[i].terminals);
     GGgraph.setTerminals(Nets[i].connectedTile);
     
     std::vector<int> Pontential_Stiner_node = Get_Potential_Steiner_node(Nets[i].terminals, Tile_Set, Gcell);

     //std::cout<<"terminal size "<<Nets[i].terminals.size()<<std::endl;
     //find STs
     std::cout<<"Test 13"<<std::endl;
     GGgraph.FindSTs(Gcell,ST_number,Pontential_Stiner_node);
     //return STs
     std::cout<<"Test 14"<<std::endl;
     std::vector<std::vector<std::pair<int,int> > > temp_path = GGgraph.returnPath();
     RouterDB::SteinerTree temp_st;

     for(unsigned int j=0;j<temp_path.size();++j){
               
          temp_st.path = temp_path[j];
          Nets[i].STs.push_back(temp_st);          

        }
     }


  for(unsigned int i=0;i<this->Nets.size();++i){

     std::cout<<"Nets symmetry part "<<this->Nets.at(i).symCounterpart<<" Nets global symmetry part "<<this->Nets.at(i).global_sym<<std::endl;

     }


  for(unsigned int i=0;i<this->Nets.size();++i){

     std::cout<<"Before mirror Nets index "<<i<<std::endl;
     
     for(unsigned int j=0;j<this->Nets.at(i).STs.size();++j){

        std::cout<<"STs path size "<<this->Nets.at(i).STs[j].path.size()<<std::endl;

        }

     }    
 

  //4. LP solve Q1. Symmetry here
  MirrorSymSTs(Gcell, Tile_Set);

  for(unsigned int i=0;i<this->Nets.size();++i){

     std::cout<<"After mirror  Nets index "<<i<<std::endl;
     
     for(unsigned int j=0;j<this->Nets.at(i).STs.size();++j){

        std::cout<<"STs path size "<<this->Nets.at(i).STs[j].path.size()<<std::endl;

        }

     }

  for(unsigned int i=0;i<this->Nets.size();++i){

     std::cout<<"Nets symmetry part "<<this->Nets.at(i).symCounterpart<<" Nets global symmetry part "<<this->Nets.at(i).global_sym<<std::endl;

     }    

 
  std::cout<<"Test 15"<<std::endl;
  ILPSolveRouting(Gcell,GGgraph,Tile_Set);
  std::cout<<"Test 16"<<std::endl;
  //5. Return hierNode  Q2. return some to hierNode for detial router
  ReturnHierNode(node);

};

std::vector<int> GcellGlobalRouter::GenerateSTsUniqueV(RouterDB::Net &temp_net){

  std::set<int> unique_set;
  std::vector<int> unique;
  for(unsigned int i=0;i<temp_net.STs.size();++i){
      for(unsigned int j=0;j<temp_net.STs[i].path.size();++j){
           unique_set.insert(temp_net.STs[i].path[j].first);
           unique_set.insert(temp_net.STs[i].path[j].second);
         }
     }

  std::set<int>::iterator it,it_low,it_up;
  it_low = unique_set.begin();
  it_up = unique_set.end();

  for(it = it_low;it!=it_up;++it){
       unique.push_back(*it);
     }

  return unique;

};

void GcellGlobalRouter::CopySTs(RouterDB::Net &temp_net, RouterDB::Net &sy_temp_net, std::map<int,int> &temp_map, std::map<int,int> &sy_temp_map){

  std::vector<std::vector<std::pair<int,int> > > path;
  
  std::vector<std::vector<std::pair<int,int> > > sy_path;

  for(unsigned int i=0;i<temp_net.STs.size();++i){

      std::vector<std::pair<int,int> > temp_sy_path;
      int cp_flag = CopyPath(temp_net.STs[i].path, temp_map, temp_sy_path);
      if(cp_flag){
           std::cout<<"Origin path size "<<temp_net.STs[i].path.size()<<std::endl;
           path.push_back(temp_net.STs[i].path);
           std::cout<<"SYM path size "<<temp_sy_path.size()<<std::endl;
           sy_path.push_back(temp_sy_path);
        }

     }


  for(unsigned int i=0;i<sy_temp_net.STs.size();++i){

      std::vector<std::pair<int,int> > temp_sy_path;
      int cp_flag = CopyPath(sy_temp_net.STs[i].path, sy_temp_map, temp_sy_path);
      if(cp_flag){

           std::cout<<"Origin path size "<<temp_net.STs[i].path.size()<<std::endl;
           sy_path.push_back(temp_net.STs[i].path);
           std::cout<<"SYM path size "<<temp_sy_path.size()<<std::endl;
           path.push_back(temp_sy_path);
        }

     }

   if(path.size()>0){
       temp_net.STs.clear();
       for(unsigned int i=0;i<path.size();++i){
            RouterDB::SteinerTree temp_tree;
            temp_tree.path = path[i];
            std::cout<<"Origin path size "<<path[i].size()<<std::endl;
            temp_net.STs.push_back(temp_tree);
          }
       sy_temp_net.STs.clear();
       for(unsigned int i=0;i<sy_path.size();++i){
            RouterDB::SteinerTree sy_temp_tree;
            sy_temp_tree.path = sy_path[i];
            std::cout<<"Origin path size "<<sy_path[i].size()<<std::endl;
            sy_temp_net.STs.push_back(sy_temp_tree);
          }

     }else{
       temp_net.global_sym = -1;
       sy_temp_net.global_sym = -1;
     }
  



};

void GcellGlobalRouter::MirrorSymSTs(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set){

  for(unsigned int i=0;i<this->Nets.size();++i){

    if(this->Nets.at(i).global_sym != -1 and this->Nets.at(i).global_sym < (int)this->Nets.size() -1 ){
   
          int global_sym = this->Nets.at(i).global_sym;
          std::vector<int> temp_vector = GenerateSTsUniqueV(this->Nets.at(i)) ;
          std::vector<int> sy_vector = GenerateSTsUniqueV(this->Nets.at(global_sym)) ;        
          std::map<int,int> temp_map = GenerateSymMap(grid, Tile_Set, temp_vector, this->Nets.at(i).sym_H, this->Nets.at(i).global_sym);
          std::map<int,int> sy_temp_map = GenerateSymMap(grid, Tile_Set, sy_vector, this->Nets.at(global_sym).sym_H, this->Nets.at(global_sym).global_sym);
          CopySTs(this->Nets.at(i), this->Nets.at(global_sym), temp_map, sy_temp_map);

        }

     }


};

std::map<int,int> GcellGlobalRouter::GenerateSymMap(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, std::vector<int> terminals, bool H, int center){

      std::map<int,int> sy_map;      

      for(unsigned int i=0;i<terminals.size();++i){

           RouterDB::tile temp_tile;
           temp_tile = grid.tiles_total[terminals[i]];
           if(H){
              temp_tile.y = 2*center - temp_tile.y;
             }else{
              temp_tile.x = 2*center - temp_tile.x;
             }
           std::set<RouterDB::tile, RouterDB::tileComp>::iterator temp_it;
           temp_it = Tile_Set.find(temp_tile);
           if(temp_it==Tile_Set.end()){
               sy_map.insert(map<int,int>::value_type(terminals[i],-1));
             }else{
               sy_map.insert(map<int,int>::value_type(terminals[i],temp_it->index));
             }
            
          }

       return sy_map;

};

int GcellGlobalRouter::PrimeSetGenerate(std::vector<std::vector<int> > &connectedTiles, std::vector<std::vector<int> > &sy_connectedTiles, std::map<int,int> &net_map, std::map<int,int> &sy_net_map){

  int unmap_flag = 0;

  for(unsigned int i=0;i<connectedTiles.size();++i){
      std::set<int> temp_sy_set;
      std::set<int> sy_set;
      std::vector<int> sy_prime;
      std::vector<int> prime;

      for(unsigned int j=0;j<connectedTiles[i].size();++j){
          temp_sy_set.insert(net_map[connectedTiles[i][j]]);
         }
      for(unsigned int j=0;j<sy_connectedTiles[i].size();++j){
          if(temp_sy_set.find(sy_connectedTiles[i][j])!=temp_sy_set.end()){
              sy_prime.push_back(sy_connectedTiles[i][j]);
            }
         }

      for(unsigned int j=0;j<sy_prime.size();++j){
           sy_set.insert(sy_net_map[sy_prime[j]]);           
         }
      for(unsigned int j=0;j<connectedTiles[i].size();++j){
          if(sy_set.find(connectedTiles[i][j])!=sy_set.end()){
              prime.push_back(connectedTiles[i][j]);
            }
         }
       
       if(sy_prime.size()!=0 and prime.size()!=0){
          connectedTiles[i] = prime;
          sy_connectedTiles[i] = sy_prime;
         }else{ 
          unmap_flag = 1;
         }

     }

  if(unmap_flag ==0){
       return 1;
    }else{
       return 0;
    }

};

void GcellGlobalRouter::Update_terminals(RouterDB::Net &temp_net){

  std::set<int> temp_set;
  std::vector<int> temp_terminals;

  for(unsigned int i=0;i<temp_net.connectedTile.size();++i){

      for(unsigned int j=0;j<temp_net.connectedTile[i].size();++j){

           temp_set.insert(temp_net.connectedTile[i][j]);         

         }

     }
  
  std::set<int>::iterator it,it_low,it_up;

  it_low = temp_set.begin();
  it_up = temp_set.end();

  for(it=it_low;it!=it_up;++it){

      temp_terminals.push_back(*it);      

     }


  temp_net.terminals = temp_terminals;
};

void GcellGlobalRouter::transformCenter(bool H, int &center, GlobalGrid &grid){

  int dist = INT_MAX;
  int index = -1;

  for(unsigned int i=0;i<grid.tiles_total.size();++i){

       if(H){
          //y
          if(abs(center-grid.tiles_total[i].y)<dist){
              dist = abs(center-grid.tiles_total[i].y);
              index = i;
             }
         }else{
          //x
          if(abs(center-grid.tiles_total[i].x)<dist){
              dist = abs(center-grid.tiles_total[i].x);
              index = i;
             }
         }
    
      }

  if(H){
      center = grid.tiles_total[index].y;
    }else{
      center = grid.tiles_total[index].x;
    }


};

void GcellGlobalRouter::SymNet(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set){

     for(unsigned int i=0;i<this->Nets.size();++i){
      
       if(this->Nets.at(i).symCounterpart!=-1 and this->Nets.at(i).symCounterpart<(int)this->Nets.size()-1){

            int symCounterpart = this->Nets.at(i).symCounterpart;

            bool H = this->Nets.at(i).sym_H;
            int center = this->Nets.at(i).center;
            this->Nets.at(i).global_center = center;
            transformCenter(H, this->Nets.at(i).global_center, grid);
            
            int prime_flag = SymNetTerminal_PrimeSet(grid, Tile_Set, this->Nets.at(i), this->Nets.at(symCounterpart), H, center);

            if(prime_flag){
  
                 this->Nets.at(i).global_sym= symCounterpart;
                 this->Nets.at(symCounterpart).global_sym= i;
              
               }

           }

        }

};

int GcellGlobalRouter::SymNetTerminal_PrimeSet(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, RouterDB::Net &temp_net, RouterDB::Net &sym_net, bool H, int center){ // H is 1 (y), then V (x)

  //sym
  //std::vector<std::pair<int,int> > sym_pair_net;
  //std::pair sym_temp_pair;

  if(temp_net.connectedTile.size()==sym_net.connectedTile.size()){

      //create sy point
      //create prime set

      std::map<int,int> net_sy_map;
      std::map<int,int> sym_sy_map;
      
      net_sy_map = GenerateSymMap(grid, Tile_Set, temp_net.terminals, H, center);
      sym_sy_map = GenerateSymMap(grid, Tile_Set, sym_net.terminals, H, center);

      int prime_flag = PrimeSetGenerate( temp_net.connectedTile, sym_net.connectedTile, net_sy_map, sym_sy_map);

      Update_terminals(temp_net);
      Update_terminals(sym_net);


      if(prime_flag == 1){
          return 1;
        }else{
          return 0;
        }


     }else{
  
        return 0;
     
     }

};


std::vector<int> GcellGlobalRouter::Get_Potential_Steiner_node(std::vector<int> t, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, GlobalGrid &grid){

    std::vector<RouterDB::tile> Temp_tile;
    for(unsigned int i=0;i<t.size();++i){
        for(unsigned int j=0;j<t.size();++j){
            if(i!=j){
                RouterDB::tile temp_tile;
                temp_tile = grid.tiles_total[t[i]];
                temp_tile.y = grid.tiles_total[t[j]].y;
                Temp_tile.push_back(temp_tile);
                temp_tile.y = grid.tiles_total[t[i]].y;
                temp_tile.x = grid.tiles_total[t[j]].x;
                Temp_tile.push_back(temp_tile);

                temp_tile = grid.tiles_total[t[j]];
                temp_tile.y = grid.tiles_total[t[i]].y;
                Temp_tile.push_back(temp_tile);
                temp_tile.y = grid.tiles_total[t[j]].y;
                temp_tile.x = grid.tiles_total[t[i]].x;
                Temp_tile.push_back(temp_tile);
                
              }
           }
       }

    std::set<int> stiner_node_set;
    std::set<int>::iterator it_stiner, it_low, it_up;

    std::set<RouterDB::tile, RouterDB::tileComp>::iterator it;

    for(unsigned int i=0;i<Temp_tile.size();++i){

          it = Tile_Set.find(Temp_tile[i]);
          if(it!=Tile_Set.end()){
          stiner_node_set.insert(it->index); 
          }         

       }    

    std::vector<int> stiner_node;

    it_low = stiner_node_set.begin();
    it_up = stiner_node_set.end();

    for(it_stiner=it_low;it_stiner!=it_up;++it_stiner){
          stiner_node.push_back(*it_stiner);
        
       }
    
    return stiner_node;


};

std::set<RouterDB::tile, RouterDB::tileComp> GcellGlobalRouter::CreateTileSet(GlobalGrid &grid){

  std::set<RouterDB::tile, RouterDB::tileComp> Tile_set;

  for(unsigned int i=0;i<grid.tiles_total.size();++i){

       Tile_set.insert(grid.tiles_total[i]);

     }

  return Tile_set;

};

// added by wbxu
void GcellGlobalRouter::placeTerminals() {
  // Limitation: assume that only 1 terminal for each net
  //bool mark;
  int mj;
  for(unsigned int i=0;i<this->Nets.size();++i) {
    this->Nets.at(i).isTerminal=false;
    bool mark=false;
    for(unsigned int j=0;j<this->Nets.at(i).connected.size();++j) {
      if(this->Nets.at(i).connected.at(j).type==RouterDB::TERMINAL) {
        mj=j; mark=true; break;
      }
    }
    if(mark) {
      if(!this->isTop) {
        this->Nets.at(i).connected.erase(this->Nets.at(i).connected.begin()+mj);
        this->Nets.at(i).degree--;
      }
      this->Nets.at(i).isTerminal=true;
    }
  }
}

long int GcellGlobalRouter::get_number(string str)
{
    long int val=0;
    for (unsigned int number=0; number < str.length(); ++number)
                {
                    if (isdigit (str[number]))
                    val=(10*val)+(str[number]-48);
                }
    return val;

};



void GcellGlobalRouter::getData(PnRDB::hierNode& node, int Lmetal, int Hmetal){

  std::cout<<"Router-Info: begin to import data"<<std::endl;
  this->isTop = node.isTop;
  this->topName=node.name;
  this->width=node.width;
  this->height=node.height;
  this->LL.x=0; this->LL.y=0;
  this->UR.x=node.width;
  this->UR.y=node.height;
  this->path_number=5; // number of candidates
  int max_width = node.width;
  int max_height = node.height;
  //int threshold = 10000000;
  lowest_metal = Lmetal;
  highest_metal = Hmetal;


  //grid_alpha should be adjusted according to the size of node
  //more adjust is necessry for detail router?
  if(max_height*max_width<=100000000){
     grid_scale = 1;
    }else{
     grid_scale = 4;
    }

  //For terminals	
  for(unsigned int i=0;i<node.Terminals.size();++i){	
      RouterDB::terminal temp_terminal;
      temp_terminal.netIter = node.Terminals[i].netIter;
      if(isTop) {
      for(unsigned int j=0;j<node.Terminals[i].termContacts.size();++j){
          RouterDB::contact temp_contact;
          //cout<<node.Terminals[i].termContacts[j].metal<<endl;
          //if(drc_info.Metalmap.find(node.Terminals[i].termContacts[j].metal)!=drc_info.Metalmap.end()){
          //  temp_contact.metal = drc_info.Metalmap[node.Terminals[i].termContacts[j].metal];
            // wbxu: Terminals in hierNode only has placedCenter field
            //temp_contact.placedLL.x =node.Terminals[i].termContacts[j].placedBox.LL.x; 
            //temp_contact.placedLL.y =node.Terminals[i].termContacts[j].placedBox.LL.y;           
            //temp_contact.placedUR.x =node.Terminals[i].termContacts[j].placedBox.UR.x; 
            //temp_contact.placedUR.y =node.Terminals[i].termContacts[j].placedBox.UR.y; 
            temp_contact.placedCenter.x =node.Terminals[i].termContacts[j].placedCenter.x;
            temp_contact.placedCenter.y =node.Terminals[i].termContacts[j].placedCenter.y;
            temp_contact.metal = -1;
            temp_terminal.termContacts.push_back(temp_contact);
          //}else{
          //  std::cout<<"Router-Error: incorrect metal for contact - from node to router"<<std::endl;
          //}			
      }
      }
      temp_terminal.name=node.Terminals[i].name;
      Terminals.push_back(temp_terminal);	
  }

  int temp_type; 
  //For nets	
  //need modify with power router.... here the method is just remove the single terminal, but not vdd/gnd
  //wbxu: pay attention to dangling nets and power nets
  for(unsigned int i=0;i<node.Nets.size();++i){	
      RouterDB::Net temp_net;		
      //if(node.Nets[i].connected.size()!=1){
         //temp_net.isTerminal=0;	
         temp_net.degree=node.Nets[i].degree;
         temp_net.netName=node.Nets[i].name;
         temp_net.shielding=node.Nets[i].shielding;
         temp_net.sink2Terminal=node.Nets[i].sink2Terminal;
         temp_net.symCounterpart=node.Nets[i].symCounterpart;
         temp_net.iter2SNetLsit=node.Nets[i].iter2SNetLsit;
         temp_net.priority=node.Nets[i].priority;

         if(node.Nets[i].axis_dir == PnRDB::H){
             temp_net.sym_H = 1;
            }else if(node.Nets[i].axis_dir == PnRDB::V){
             temp_net.sym_H = 0;
            }        
         temp_net.center = node.Nets[i].axis_coor;
         /*
         if(temp_net.symCounterpart!=-1){
            if(i < temp_net.symCounterpart){
               symnet_idx.push_back(temp_net.symCounterpart);
              }else{
               symnet_idx.push_back(i);
              }
           }  // wbxu? symnet_idx undefined
          */

          for(unsigned int j=0;j<node.Nets[i].connected.size();++j){
              RouterDB::connectNode temp_connectNode;
              temp_type = RouterDB::NType(node.Nets[i].connected[j].type);  // wbxu? Not Omark, replace with NType
              
              if(temp_type ==0 ){			
                 temp_connectNode.type=RouterDB::BLOCK;	
                }else{
                 temp_connectNode.type=RouterDB::TERMINAL;
                 temp_net.isTerminal=1;
                 temp_net.terminal_idx=node.Nets[i].connected[j].iter;
                }
               // assume that at most one terminal connected to one net 
               temp_connectNode.iter=node.Nets[i].connected[j].iter;
               temp_connectNode.iter2=node.Nets[i].connected[j].iter2;
               temp_net.connected.push_back(temp_connectNode);
              }
          Nets.push_back(temp_net);		
       //}else{
       // cout<<"Remove one connection terminal"<<endl;
       //}	
     }
	
  //For blocks	
  for(unsigned int i=0;i<node.Blocks.size();++i){
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

      for(unsigned int j=0;j<node.Blocks[i].instance[slcNumber].blockPins.size();++j){
          RouterDB::Pin temp_pin;
          temp_pin.pinName=node.Blocks[i].instance[slcNumber].blockPins[j].name;
          temp_pin.netIter=node.Blocks[i].instance[slcNumber].blockPins[j].netIter;
          for(unsigned int k=0;k<node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts.size();++k){
             RouterDB::contact temp_contact;
             if(drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].metal)!=drc_info.Metalmap.end()){
                 temp_contact.metal=drc_info.Metalmap[node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].metal];
               }else{
                 std::cout<<"Router-Error: the metal pin contact of block is not found"<<std::endl;
               }
             temp_contact.placedLL.x=node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].placedBox.LL.x;
             temp_contact.placedLL.y=node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].placedBox.LL.y;
             temp_contact.placedUR.x=node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].placedBox.UR.x;
             temp_contact.placedUR.y=node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].placedBox.UR.y;
             temp_contact.placedCenter.x=node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].placedCenter.x;
             temp_contact.placedCenter.y=node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].placedCenter.y;
             temp_pin.pinContacts.push_back(temp_contact);
             }
          

          for(unsigned int k=0;k<node.Blocks[i].instance[slcNumber].blockPins[j].pinVias.size();++k){
               RouterDB::Via temp_via;
               temp_via.model_index = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].model_index;
               temp_via.position.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].placedpos.x;
               temp_via.position.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].placedpos.y;
               //ViaRect

               if(drc_info.Viamap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.metal)!=drc_info.Viamap.end()){
                   temp_via.ViaRect.metal = drc_info.Viamap[node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.metal];
                 }else{
                   std::cout<<"Router-Error: - Viamap Error"<<std::endl;
                 }
               temp_via.ViaRect.placedLL.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.placedBox.LL.x;
               temp_via.ViaRect.placedLL.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.placedBox.LL.y;
               temp_via.ViaRect.placedUR.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.placedBox.UR.x;
               temp_via.ViaRect.placedUR.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.placedBox.UR.y;
               temp_via.ViaRect.placedCenter.x=node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.placedCenter.x;
               temp_via.ViaRect.placedCenter.y=node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.placedCenter.y;
               //LowerRect //LowerMetalRect
               if(drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.metal)!=drc_info.Metalmap.end()){
                  temp_via.LowerMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.metal];
               }else{
                  std::cout<<"Router-Error: Metal map error"<<std::endl;
               }
               temp_via.LowerMetalRect.placedLL.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.placedBox.LL.x;
               temp_via.LowerMetalRect.placedLL.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.placedBox.LL.y;
               temp_via.LowerMetalRect.placedUR.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.placedBox.UR.x;
               temp_via.LowerMetalRect.placedUR.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.placedBox.UR.y;
               temp_via.LowerMetalRect.placedCenter.x=node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.placedCenter.x;
               temp_via.LowerMetalRect.placedCenter.y=node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.placedCenter.y;
               //UpperRect //UpperMetalRect
               if(drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.metal)!=drc_info.Metalmap.end()){
                  temp_via.UpperMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.metal];
               }else{
                  std::cout<<"Router-Error: Metal map error"<<std::endl;
               }
               temp_via.UpperMetalRect.placedLL.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.placedBox.LL.x;
               temp_via.UpperMetalRect.placedLL.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.placedBox.LL.y;
               temp_via.UpperMetalRect.placedUR.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.placedBox.UR.x;
               temp_via.UpperMetalRect.placedUR.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.placedBox.UR.y;
               temp_via.UpperMetalRect.placedCenter.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.placedCenter.x;
               temp_via.UpperMetalRect.placedCenter.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.placedCenter.y;

               temp_pin.pinVias.push_back(temp_via);
             }

          temp_block.pins.push_back(temp_pin);
      }

   for(unsigned int j=0;j<node.Blocks[i].instance[slcNumber].interMetals.size();++j){
       RouterDB::contact temp_metal;
       if(drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].interMetals[j].metal)!=drc_info.Metalmap.end()){
           temp_metal.metal=drc_info.Metalmap[node.Blocks[i].instance[slcNumber].interMetals[j].metal];
           //temp_metal.width=drc_info.Metal_info[temp_metal.MetalIdx].width;
         }else{
           std::cout<<"Router-Error: interMetal info missing metal"<<std::endl;
         }
       RouterDB::point temp_point;
       temp_metal.placedLL.x = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.LL.x;     
       temp_metal.placedLL.y = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.LL.y;
       temp_metal.placedUR.x = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.UR.x;      
       temp_metal.placedUR.y = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.UR.y;  
       temp_metal.placedCenter.x = (temp_metal.placedLL.x + temp_metal.placedUR.x)/2;
       temp_metal.placedCenter.y = (temp_metal.placedLL.y + temp_metal.placedUR.y)/2;
       temp_block.InternalMetal.push_back(temp_metal);
      }
	
   for(unsigned int j=0;j<node.Blocks[i].instance[slcNumber].interVias.size();++j){
       RouterDB::Via temp_via;
       temp_via.model_index=node.Blocks[i].instance[slcNumber].interVias[j].model_index;
       temp_via.position.x=node.Blocks[i].instance[slcNumber].interVias[j].placedpos.x;
       temp_via.position.y=node.Blocks[i].instance[slcNumber].interVias[j].placedpos.y;
       //ViaRect

       if(drc_info.Viamap.find(node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.metal)!=drc_info.Metalmap.end()){
                   temp_via.ViaRect.metal = drc_info.Viamap[node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.metal];
                 }else{
                   std::cout<<"Router-Error: - Viamap Error"<<std::endl;
                 }
               temp_via.ViaRect.placedLL.x = node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.placedBox.LL.x;
               temp_via.ViaRect.placedLL.y = node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.placedBox.LL.y;
               temp_via.ViaRect.placedUR.x = node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.placedBox.UR.x;
               temp_via.ViaRect.placedUR.y = node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.placedBox.UR.y;
               temp_via.ViaRect.placedCenter.x = node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.placedCenter.x;
               temp_via.ViaRect.placedCenter.y = node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.placedCenter.y;
               //LowerRect //LowerMetalRect
               if(drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.metal)!=drc_info.Metalmap.end()){
                  temp_via.LowerMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.metal];
               }else{
                  std::cout<<"Router-Error: Metal map error"<<std::endl;
               }
               temp_via.LowerMetalRect.placedLL.x = node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.placedBox.LL.x;
               temp_via.LowerMetalRect.placedLL.y = node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.placedBox.LL.y;
               temp_via.LowerMetalRect.placedUR.x = node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.placedBox.UR.x;
               temp_via.LowerMetalRect.placedUR.y = node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.placedBox.UR.y;
               temp_via.LowerMetalRect.placedCenter.x = node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.placedCenter.x;
               temp_via.LowerMetalRect.placedCenter.y = node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.placedCenter.y;
               //UpperRect //UpperMetalRect
               if(drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.metal)!=drc_info.Metalmap.end()){
                  temp_via.UpperMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.metal];
               }else{
                  std::cout<<"Router-Error: Metal map error"<<std::endl;
               }
               temp_via.UpperMetalRect.placedLL.x = node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.placedBox.LL.x;
               temp_via.UpperMetalRect.placedLL.y = node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.placedBox.LL.y;
               temp_via.UpperMetalRect.placedUR.x = node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.placedBox.UR.x;
               temp_via.UpperMetalRect.placedUR.y = node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.placedBox.UR.y;       
               temp_via.UpperMetalRect.placedCenter.x = node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.placedCenter.x;
               temp_via.UpperMetalRect.placedCenter.y = node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.placedCenter.y;

       temp_block.InternalVia.push_back(temp_via);
      }
   Blocks.push_back(temp_block);
  }

  //getPowerGridData(node);
  //getPowerNetData(node);

  std::cout<<"Router-Info: complete importing data"<<std::endl;
};

/*
void GlobelRouter::getPowerNetData(PnRDB::hierNode& node){
	
  //For power net

  for(int i=0;i<node.PowerNets.size();++i){
      RouterDB::PowerNet temp_net;
      temp_net.netName = node.PowerNets[i].name;
      //temp_net.shielding = node.Nets[i].shielding;
      temp_net.power = node.PowerNets[i].power;
      //path_metal
      for(int j=0;j<node.PowerNets[i].path_metal.size();++j){
          RouterDB::Metal temp_metal;
          ConvertMetal(temp_metal, node.PowerNets[i].path_metal[j]);
          temp_net.path_metal.push_back(temp_metal);          
         }
      
      //path via
      for(int j=0;j<node.PowerNets[i].path_via.size();++j){
          RouterDB::Via temp_via;
          ConvertVia(temp_via,node.PowerNets[i].path_via[j]);
          temp_net.path_via.push_back(temp_via);          

         }

      //pins

      for(int j=0;j<node.PowerNets[i].Pins.size();++j){
          RouterDB::Pin temp_pin;
          ConvertPin(temp_pim, node.PowerNets[i].Pins[j]);
          temp_net.pins.push_back(temp_pin);
      }
      

      PowerNets.push_back(temp_net);
     
     }
};

void GlobalRouter::ConverContact(RouterDB::contact& temp_metal, PnRDB::contact& pnr_metal){

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

void GlobalRouter::ConvertMetal(RouterDB::Metal& temp_metal,PnRDB::Metal& pnr_metal){

  //RouterDB::Metal temp_metal;
  temp_metal.MetalIdx = pnr_metal.MetalIdx;
  temp_metal.LinePoint[0].x = pnr_metal.LinePoint[0].x;
  temp_metal.LinePoint[0].y = pnr_metal.LinePoint[0].y;
  temp_metal.LinePoint[1].x = pnr_metal.LinePoint[1].x;
  temp_metal.LinePoint[1].y = pnr_metal.LinePoint[1].y;
  temp_metal.width = pnr_metal.width;
  //contact
  RouterDB::contact temp_contact;

  if(drc_info.Metalmap.find(pnr_metal.MetalRect.metal)!=drc_info.Metalmap.end()){
    temp_contact.metal=drc_info.Metalmap[pnr_metal.MetalRect.metal];
  }else{
    std::cout<<"Router-Error: the metal pin contact of block is not found"<<std::endl;
  }

  //temp_contact.metal = drc_info.Metalmap[node.Nets[i].path_metal[j].MetalRect.metal];

  temp_contact.placedLL.x = pnr_metal.MetalRect.placedBox.LL.x;
  temp_contact.placedLL.y = pnr_metal.MetalRect.placedBox.LL.y;
  temp_contact.placedUR.x = pnr_metal.MetalRect.placedBox.UR.x;
  temp_contact.placedUR.y = pnr_metal.MetalRect.placedBox.UR.y;
  temp_contact.placedCenter.x = pnr_metal.MetalRect.placedCenter.x;
  temp_contact.placedCenter.y = pnr_metal.MetalRect.placedCenter.y;
  temp_metal.MetalRect = temp_contact;

};


void GlobalRouter::getPowerGridData(PnRDB::hierNode & node){


  //Vdd_grid
  Vdd_grid.power = node.Vdd.power;

  for(int i =0;i<node.Vdd.metals.size();++i){
       RouterDB::Metal temp_metal;
       ConvertMetal(temp_metal, node.Vdd.metals[i]);
       Vdd_grid.metals.push_back(temp_metal);
     }

  for(int i =0;i<node.Vdd.vias.size();++i){
       RouterDB::Via temp_via;
       ConvertVia(temp_via, node.Vdd.vias[i]);
       Vdd_grid.vias.push_back(temp_via);
     }

  //Gnd_grid
  Gnd_grid.power = node.Gnd.power;

  for(int i =0;i<node.Gnd.metals.size();++i){
       RouterDB::Metal temp_metal;
       ConvertMetal(temp_metal, node.Gnd.metals[i]);
       Gnd_grid.metals.push_back(temp_metal);
     }

  for(int i =0;i<node.Gnd.vias.size();++i){
       RouterDB::Via temp_via;
       ConvertVia(temp_via, node.Gnd.vias[i]);
       Gnd_grid.vias.push_back(temp_via);
     }

};

void GlobelRouter::ConvertVia(RouterDB::Via &temp_via,PnRDB::Via& pnr_via){

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

void GlobalRouter::ConvertPin(RouterDB::Pin& temp_pin,PnRDB::pin& pnr_pin){

  //RouterDB::Pin temp_pin;
  temp_pin.pinName=pnr_pin.name;
  temp_pin.netIter=pnr_pin.netIter;
  for(int k=0;k<pnr_pin.pinContacts.size();++k){
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
          

  for(int k=0;k<pnr_pin.pinVias.size();++k){
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
*/

void GcellGlobalRouter::getDRCdata(PnRDB::Drc_info& drcData){

  drc_info = drcData; 

};



//return some to hierNode for detailed router
/*
void GcellGlobalRouter::returnGlobalPath(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index){

  
 
};
*/

int GcellGlobalRouter::CopyPath(std::vector<std::pair<int,int> > &path, std::map<int,int> &temp_map, std::vector<std::pair<int,int> > &sy_path){

  //std::vector<std::pair<int,int> > sy_path;
  std::pair<int,int> temp_path;
  for(unsigned int i=0;i<path.size();++i){

       if(temp_map.find(path[i].first)!=temp_map.end() and temp_map[path[i].first]!= -1){
            temp_path.first = temp_map[path[i].first];
         }else{
            return 0;
         }

       if(temp_map.find(path[i].second)!=temp_map.end() and temp_map[path[i].second]!= -1){
            temp_path.second = temp_map[path[i].second];
         }else{
            return 0;
         }

       sy_path.push_back(temp_path);

     }

  return 1;

};

int  GcellGlobalRouter::JudgeSymmetry(std::vector<std::pair<int,int> > &path,std::vector<std::pair<int,int> > &sy_path, std::map<int,int> &sy_map){
 
  //map the path
  std::vector<std::pair<int,int> > map_path;
  std::pair<int,int> temp_path;
  
  for(unsigned int i=0;i<path.size();++i){
      if(sy_map.find(path[i].first)==sy_map.end()){
       std::cout<<"SY map Error";
      }else{
       temp_path.first = sy_map[path[i].first];
      }

     if(sy_map.find(path[i].second)==sy_map.end()){
       std::cout<<"SY map Error";
      }else{
       temp_path.second = sy_map[path[i].second];
      }

      if(temp_path.first == -1 or temp_path.second == -1){
          return 0;
        }else{
 
          map_path.push_back(temp_path);

        }
     }

     std::set<std::pair<int,int>, RouterDB::pairComp> map_path_set;
     std::set<std::pair<int,int>, RouterDB::pairComp> sy_path_set;

     std::pair<int,int> temp_pair;

     for(unsigned int i = 0; i<map_path.size();++i){

         if(map_path[i].first<map_path[i].second){
            temp_pair = map_path[i];
            map_path_set.insert(temp_pair);
           }else{
            temp_pair.first = map_path[i].second;
            temp_pair.second = map_path[i].first;
            map_path_set.insert(temp_pair);
           }

        }

     for(unsigned int i = 0; i<sy_path.size();++i){

         if(sy_path[i].first<sy_path[i].second){
            temp_pair = sy_path[i];
            sy_path_set.insert(temp_pair);
           }else{
            temp_pair.first = sy_path[i].second;
            temp_pair.second = sy_path[i].first;
            sy_path_set.insert(temp_pair);
           }

        }

     if(map_path_set.size()!=sy_path_set.size()){return 0;}

     std::set<std::pair<int,int> >::iterator map_it,sy_it;

     for(map_it = map_path_set.begin(),sy_it = sy_path_set.begin(); map_it!=map_path_set.end(); ++map_it, ++sy_it){
         if(*map_it!=*sy_it){
             return 0;
           }
        }

     return 1;

};


int GcellGlobalRouter::ILPSolveRouting(GlobalGrid &grid, GlobalGraph &graph, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set) {
  std::cout<< "Status Log: ILP Solving Starts"<<std::endl;
  # if defined ERROR
  #  undef ERROR
  # endif
  //# define ERROR() { fprintf(stderr, "Error\n"); return(1); }
  # define ERROR() { fprintf(stderr, "Error\n"); }

  // start of lp_solve
  int majorversion, minorversion, release, build;
  char buf[1024];
  hlpsolve lpsolve;
  # if defined WIN32
  #   define lpsolvelib "lpsolve55.dll"
  # else
  #   define lpsolvelib "liblpsolve55.so"
  # endif
  lpsolve = open_lpsolve_lib(const_cast<char*>(lpsolvelib));
  if (lpsolve == NULL) {
    fprintf(stderr, "Unable to load lpsolve shared library (%s).\nIt is probably not in the correct path.\n", lpsolvelib);
    //ERROR();
  }

  if (!init_lpsolve(lpsolve)) {
    fprintf(stderr, "Unable to initialize lpsolve shared library (%s)\n      ", lpsolvelib);
    //ERROR();
  }

  //std::ofstream output_Final_Selected_Candidates;
  //output_Final_Selected_Candidates.open("./Debug/Final_Selected_Candidates.txt",std::ofstream::app);
  //std::ofstream lp_solve_matrix;
  //lp_solve_matrix.open("./Debug/lp_solve_matrix.txt", std::ofstream::app);
  //lp_solve_matrix.close();

  // 1. collect number of STs
  int NumberOfSTs = 0;
  int NumberOfNets = 0;
  valInfo vi;


  for(unsigned int h=0;h<this->Nets.size();++h) { //  for each net
    vi.netIter=h;
    for(unsigned int i=0;i<this->Nets[h].STs.size();++i) {// for each segment
      vi.STIter=i;
      vi.candIter=-1;
      vi.segIter=-1;
      vi.valIter=NumberOfSTs;
      this->Nets[h].STs[i].valIdx = NumberOfSTs;
      NumberOfSTs++;
      ValArray.push_back(vi);
    }
   NumberOfNets++;
  }
  std::cout<<"TotNumberOfNest "<<NumberOfNets<<" TotNumberOfSTs "<<NumberOfSTs<<std::endl;
  this->NumOfVar=NumberOfSTs;//#Variable initialization

  if ((lp = make_lp(0,NumOfVar+1)) == NULL) {fprintf(stderr, "Error\n");} //ERROR();}
  lp_solve_version(&majorversion, &minorversion, &release, &build);
  sprintf(buf, "lp_solve %d.%d.%d.%d demo\n\n", majorversion, minorversion, release, build);//lp_solve 5.5.2.0 
  print_str(lp, buf);
  put_logfunc(lp, NULL, 0);
  set_outputfile(lp, const_cast<char*>("./Debug/lp_solve_result.txt"));

  // 2. Initialize matrix without constraints  Q1? A 0 is inserted to the temp_row, so the valInfo maybe not correct

  //std::cout<<"testcase 1"<<std::endl;

  //int CurNet = 0;

  for(int i=0;i<NumberOfNets;++i){

      int CurNet = i;
      std::vector<double> temp_row;
      temp_row.push_back(0);//0th column "0" Q2?

      for(unsigned int j=0;j<this->Nets.size();++j){

          for(unsigned int k=0;k<this->Nets.at(j).STs.size();++k){

	    if((int)j==CurNet) {
                temp_row.push_back(1);
               } else {
                temp_row.push_back(0);
               }   
             }
         }

       temp_row.push_back(0);
       double* row = &temp_row[0];
       if (!add_constraint(lp, row, EQ, 1)) {fprintf(stderr, "Error\n");} //ERROR();}
     
     }

  //symmetry problem

  for(unsigned int i=0;i<this->Nets.size();++i){

    if(this->Nets.at(i).global_sym!=-1 and this->Nets.at(i).global_sym < (int)this->Nets.size()-1){
          std::cout<<"net index "<<i<<" global_sym "<< this->Nets.at(i).global_sym<<std::endl;
          int global_sym = this->Nets.at(i).global_sym;   
          for(unsigned int j=0;j<this->Nets.at(i).STs.size();++j){

               std::vector<double> temp_row;
               temp_row.push_back(0);//0th column "0" Q2?   

               for(int val_number = 0; val_number < NumberOfSTs+1 ; ++val_number){
                      if(val_number == this->Nets.at(global_sym).STs[j].valIdx){
                           temp_row.push_back(1);
                        }else if(val_number == this->Nets.at(i).STs[j].valIdx){
                           temp_row.push_back(-1);
                        }else{
                           temp_row.push_back(0);
                        }
                                               
                    }

                double* row = &temp_row[0];
                std::cout<<"Adding SYM constraints"<<std::endl;
                if (!add_constraint(lp, row, EQ, 0)) {fprintf(stderr, "Error\n");} //ERROR();}
       
             }
        
        }
     
     }

/*
  std::cout<<"start sy flag"<<std::endl;
  for(int i=0;i<this->Nets.size();++i){
      
      if(this->Nets.at(i).symCounterpart!=-1 and this->Nets.at(i).symCounterpart<this->Nets.size()-1){

          int symCounterpart = this->Nets.at(i).symCounterpart;
          if(this->Nets.at(i).connectedTile.size() == this->Nets.at(symCounterpart).connectedTile.size()){

             //calculate center if all the same then do sym judging
             std::vector<std::pair<double,double> > center;
             
             for(int k=0;k<this->Nets.at(i).connectedTile.size();++k){
                  
                  int distance = INT_MAX;
                  std::pair<double, double> temp_center;

                  for(int p = 0;p<this->Nets.at(i).connectedTile[k].size();++p){
                       for(int q = 0; q<this->Nets.at(symCounterpart).connectedTile[k].size();++q){
                            int tile_index = this->Nets.at(i).connectedTile[k][p];
                            int tile_index_sym = this->Nets.at(symCounterpart).connectedTile[k][q];
                            if(abs(grid.tiles_total[tile_index].x-grid.tiles_total[tile_index_sym].x)+abs(grid.tiles_total[tile_index].y-grid.tiles_total[tile_index_sym].y)<distance){
                                temp_center.first = (double) (grid.tiles_total[tile_index].x+grid.tiles_total[tile_index_sym].x)/2;
                                temp_center.second = (double) (grid.tiles_total[tile_index].y+grid.tiles_total[tile_index_sym].y)/2;
                                distance = abs(grid.tiles_total[tile_index].x-grid.tiles_total[tile_index_sym].x)+abs(grid.tiles_total[tile_index].y-grid.tiles_total[tile_index_sym].y);
                              }
                           }
                      }

                  center.push_back(temp_center);
                  

                }

                std::cout<<"start sy flag 1"<<std::endl;
                //end calculate center
                int sy_flag_x = 1;
                int sy_flag_y = 1;
                int sy_direction = -1; // 1 is V, x; 0 is H, y; 
                double center_axis = -1;
                 
                for(int k=0;k<center.size()-1;++k){

                     if(center[k].first != center[k+1].first){
                         sy_flag_x = 0; 
                       }
                     
                     if(center[k].second != center[k+1].second){
                         sy_flag_y = 0; 
                       }

                   }

                if(sy_flag_x==1){
                    sy_direction = 1;
                    center_axis = center.back().first;
                   }else if(sy_flag_y==1){
                    sy_direction = 0;
                    center_axis = center.back().second;
                  }

                if(sy_direction != -1){
                    //map sym sts, then compare it
                    std::set<int> tiles_set_sy;                    
                    std::set<int>::iterator it, it_low, it_up;
                    for(int st_number = 0; st_number < this->Nets.at(symCounterpart).STs.size(); ++st_number){
                          for(int path_number_st = 0; path_number_st< this->Nets.at(symCounterpart).STs[st_number].path.size();path_number_st++){
                                tiles_set_sy.insert(this->Nets.at(symCounterpart).STs[st_number].path[path_number_st].first);
                                tiles_set_sy.insert(this->Nets.at(symCounterpart).STs[st_number].path[path_number_st].second);
                              }
                       }
                    
                    it_low = tiles_set_sy.begin();
                    it_up = tiles_set_sy.end();
                    std::vector<int> unique_tiles;

                    for(it=it_low;it!=it_up;++it){
                         unique_tiles.push_back(*it);
                       }

                    std::map<int,int> sy_map;
                    
                    for(int q=0;q<unique_tiles.size();++q){

                         RouterDB::tile temp_tile;
                         temp_tile = grid.tiles_total[unique_tiles[q]];
                         if(sy_direction==1){temp_tile.x = 2*center_axis - temp_tile.x ;}
                         if(sy_direction==0){temp_tile.y = 2*center_axis - temp_tile.y ;}
                         std::set<RouterDB::tile, RouterDB::tileComp>::iterator temp_it;
                         temp_it = Tile_Set.find(temp_tile);
                         if(temp_it==Tile_Set.end()){
                            sy_map.insert(map<int,int>::value_type(unique_tiles[q],-1));
                           }else{
                            sy_map.insert(map<int,int>::value_type(unique_tiles[q],temp_it->index));
                           }

                       }

                     std::cout<<"start sy flag 2"<<std::endl;

                     //based on this map, transform to sy part;
                       for(int p =0;p<this->Nets.at(symCounterpart).STs.size();++p){
                           for(int q=0;q<this->Nets.at(i).STs.size();++q){
                                std::cout<<"start sy flag 3"<<std::endl;
                                int symmetry = JudgeSymmetry(Nets.at(symCounterpart).STs[p].path,Nets.at(i).STs[q].path,sy_map);
                                std::cout<<"start sy flag 4"<<std::endl;
                                if(symmetry){
                                   //add sy constraint

                                    std::vector<double> temp_row;
                                    temp_row.push_back(0);//0th column "0" Q2?   

      
                                    for(int val_number = 0; val_number < NumberOfSTs+1 ; ++val_number){
                                        if(val_number == this->Nets.at(symCounterpart).STs[p].valIdx){
                                          temp_row.push_back(1);
                                          }else if(val_number == this->Nets.at(i).STs[q].valIdx){
                                          temp_row.push_back(-1);
                                          }else{
                                          temp_row.push_back(0);
                                          }
                                               
                                      }

                                    double* row = &temp_row[0];
                                    if (!add_constraint(lp, row, LE, 0)) {fprintf(stderr, "Error\n");} //ERROR();}
                                    std::cout<<"start sy flag 5"<<std::endl;
                                   
                                  }
                              }

                          }

                  }

             


            }
        }
     
     }

  std::cout<<"End sy flag"<<std::endl;
*/

  //QQQ remove the duplicated constraints

  //symmetry constraint
  //Q3? how to judge whether the final layout is symmetry is difficult.

/*
  for(int i=0;i<this->Nets.size();++i){
     
      if(this->Nets.at(i).symCounterpart!=-1){
        
         if(this->Nets.at(i).terminals.size() == this->Nets.at(this->Nets.at(i).symCounterpart).terminals.size()){

             double center_xl = 0;
             double center_yl = 0;
             double center_xr = 0;
             double center_yr = 0;
             double center_x = -1;
             double center_y = -1;

             for(int k = 0; k <this->Nets.at(i).terminals.size();++k){

                   center_xl = center_xl + (double) grid.tiles_total[this->Nets.at(i).terminals[k]].x;
                   center_yl = center_yl + (double) grid.tiles_total[this->Nets.at(i).terminals[k]].y;
                
                }


             for(int k = 0; k <this->Nets.at(this->Nets.at(i).symCounterpart).terminals.size();++k){

                   center_xr = center_xr + (double) grid.tiles_total[this->Nets.at(this->Nets.at(i).symCounterpart).terminals[k]].x;
                   center_yr = center_yr + (double) grid.tiles_total[this->Nets.at(this->Nets.at(i).symCounterpart).terminals[k]].y;
                
                }

             if(center_xl == center_xr and center_yl != center_yr){
                 center_y = (center_yl + center_yr)/(2*this->Nets.at(i).terminals.size());
               }else if(center_yl == center_yr and center_xl != center_xr){
                 center_x = (center_xl + center_xr)/(2*this->Nets.at(i).terminals.size());
               }else if(center_xl == center_xr and center_yl == center_yr){
                 center_x = (center_xl + center_xr)/(2*this->Nets.at(i).terminals.size());
               }

              //then judge whether that is symmetry or not for each ST
              if(center_x!=-1){
                //add symmetry flag

                judge_symmety(this->Nets.at(i),this->Nets.at(this->Nets.at(i).symCounterpart),  center_x, 0);

                }else if(center_y!=-1){
                //add symmetry flag

                judge_symmety(this->Nets.at(i),this->Nets.at(this->Nets.at(i).symCounterpart), center_y, 1);

                }
           
           }
        
        }
      
     }
*/


  //CalCulated_Sym_Ax(this->Nets[i].terminals,this->Nets[j].terminals, center_x, center_y, H_or_V); //H_or_V is H if 1, else V (0);
  // 1. Based on real pin determine the center terminal position or the coordinate of ;
  // 2. Based on the STs calclated the co

  //capacity edge constraint
  //Q4?

  //std::cout<<"testcase 2"<<std::endl;

  std::vector<std::pair<int,int> > Edges;
  std::vector<int> Capacities;
  std::vector<std::vector<int> > Edges_To_Var;

  NumberOfSTs = 0;

  for(unsigned int i=0;i<this->Nets.size();++i){
      for(unsigned int j=0;j<this->Nets.at(i).STs.size();++j){
          NumberOfSTs++;
          for(unsigned int k=0;k<this->Nets.at(i).STs[j].path.size();++k){
               
               int found = 0;
               int index = -1;
               for(unsigned int l=0;l<Edges.size();++l){
                      
                    if((this->Nets.at(i).STs[j].path[k].first == Edges[l].first and this->Nets.at(i).STs[j].path[k].second == Edges[l].second) or (this->Nets.at(i).STs[j].path[k].first == Edges[l].second and this->Nets.at(i).STs[j].path[k].second == Edges[l].first ) ){
                      found = 1;
                      index = l;
                      break;
                      }
                     
                  }

               if(found ==1){
                  //std::cout<<"Break down"<<std::endl;
                  Edges_To_Var[index].push_back(NumberOfSTs); //push_back the var number??        
                    
                 }else{

                  for(unsigned int p = 0;p<graph.graph[this->Nets.at(i).STs[j].path[k].first].list.size();++p){
                       if(graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].dest == this->Nets.at(i).STs[j].path[k].second){
                           Capacities.push_back(graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].capacity);
                           std::cout<<"Edge capacity "<<graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].capacity<<std::endl;
                           Edges.push_back(this->Nets.at(i).STs[j].path[k]);
                           std::vector<int> temp_var;
                           Edges_To_Var.push_back(temp_var);

                           break;
                         }
                     }
                 }
             }

        }
     }

  //std::cout<<"testcase 3"<<std::endl;

/*

  for(int i=0;i<Edges_To_Var.size();++i){

      std::vector<double> temp_row;
      temp_row.push_back(0);//0th column "0" Q2?   

       for(int j=0;j<NumberOfSTs;++j){
           temp_row.push_back(0);
          }
       temp_row.push_back(-Capacities[i]);
       for(int j=0;j<Edges_To_Var[i].size();++j){
          temp_row[Edges_To_Var[i][j]]=1;
          }

       double* row = &temp_row[0];
       if (!add_constraint(lp, row, LE, 0)) {fprintf(stderr, "Error\n");} //ERROR();}
     
     }
*/

  for(unsigned int i=0;i<Edges_To_Var.size();++i){

      std::vector<double> temp_row;
      temp_row.push_back(0);//0th column "0" Q2?   

       for(int j=0;j<NumberOfSTs;++j){
            int found_flag = 0;
            for(unsigned int k=0;k<Edges_To_Var[i].size();++k){
                if(Edges_To_Var[i][k]==j){found_flag=1;}
               }
            if(found_flag==1){
              temp_row.push_back(1);
              }else{
              temp_row.push_back(0);
              }
          }

       temp_row.push_back(-Capacities[i]);
       std::cout<<"Constraint Capacity "<<Capacities[i]<<std::endl;

       double* row = &temp_row[0];
       if (!add_constraint(lp, row, LE, 0)) {fprintf(stderr, "Error\n");} //ERROR();}
     
     }

  //std::cout<<"testcase 4"<<std::endl;

  print_lp(lp);
  // 4. Set binary variables (candidates + slacks)
  for(int i=1;i<=this->NumOfVar;++i){
    set_binary(lp, i, TRUE);//"TRUE": set variable to be a binary. upper bound=1, lower bound=0
  }
  
  set_bounds(lp, this->NumOfVar+1, 0.0, 1.0);

  printf("Set the objective function\n");
  printf("set_obj_fn(lp, {nets[h].seg[i].candis[j].TotMetalWeightByLength})\n");

  // 5. Set objective function
  vector<double> temp_row;
  temp_row.push_back(0);
  for(int i=0;i<this->NumOfVar;++i){
     temp_row.push_back(0);
  }
  temp_row.push_back(1);
  double *row = &temp_row[0];
  if (!set_obj_fn(lp, row)){std::cout <<"Router-Error: Objective insertion Error"<<std::endl;}

  //std::cout<<"testcase 5"<<std::endl;

  // 6. Solve with lp
  set_minim(lp);
  set_solutionlimit(lp, 10); 
  set_presolve(lp, PRESOLVE_PROBEFIX | PRESOLVE_ROWDOMINATE, get_presolveloops(lp));
  print_lp(lp);

  int ret = solve(lp);
  if(ret== 0){
          std::cout << "Status Log: Optimal Solution Found Success"<<std::endl;
  }
  else if(ret==2){
          std::cout <<"Status Log: Model is Infeasible"<<std::endl;
  }
  else if(ret==1){
          std::cout <<"Status Log: Suboptimal Solution Found"<<std::endl;
  }
  else if(ret==-2){
          std::cout <<"Status Log: Out of memory"<<std::endl;
  }
  else if(ret==7){
          std::cout <<"Status Log: Timeout(set via set_timeout)"<<std::endl;
  }
  else{
          std::cout <<"Status Log: Refer Function solve in lp_solve(http://lpsolve.sourceforge.net/5.5/)"<<std::endl;
  }

  printf("#Constraints: lp row:  %d \n", lp->rows);
  printf("#Variables: lp col:  %d \n", lp->columns);

  // 7. Get results and store back to data structure
  // Q5?
  double Vars[NumOfVar];
  get_variables(lp, Vars);

  //std::cout<<"testcase 6"<<std::endl;
  for(int i=0;i<NumOfVar;++i){
      if(Vars[i]==1){
         this->Nets.at(ValArray[i].netIter).STindex=ValArray[i].STIter;
        }
     }
  //std::cout<<"testcase 7"<<std::endl;
  delete_lp(lp);
  return ret;
}


/*
void GlobalRouter::judge_symmety(RouterDB::Net &temp_net1, RouterDB::Net &temp_net2, int center, int H){

//H is 0 is x, else y

   for(int i=0;i<temp_net1.STs.size();++i){

       for(int j=0;j<temp_net2.STs.size();++j){

            if(temp_net1.STs[i].path.size() == temp_net2.STs[j].path.size()){

                if(H){ // heriotal symmetry
                     //std::vector<std::pair<int,int> > 
                     
                  }else{
                  
                  }
                 
              }
          }
      
      }
}
*/

void GcellGlobalRouter::ReturnHierNode(PnRDB::hierNode& HierNode) {
    HierNode.tiles_total = Gcell.tiles_total;
    for(vector<PnRDB::net>::iterator H_NET_it=HierNode.Nets.begin();H_NET_it!=HierNode.Nets.end();++H_NET_it){
        for(vector<RouterDB::Net>::const_iterator NET_it=Nets.begin(); NET_it!=Nets.end(); ++NET_it){
            if(H_NET_it->name!=NET_it->netName){
                continue;
            }else{
                std::vector<std::pair<int,int> > path = NET_it->STs.at(NET_it->STindex).path;
                H_NET_it->GcellGlobalRouterPath = path;
                H_NET_it->connectedTile = NET_it->connectedTile;
                break;
            }
        }
    }
    std::cout << std::endl;
}
