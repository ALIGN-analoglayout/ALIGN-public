#include "GlobalGrid.h"
#include "spdlog/spdlog.h"

GlobalGrid::GlobalGrid(){

}

void GlobalGrid::CreateGridDataCap(bool Cap_Ncap){
  // if Cap_Ncap == 1, Ncap; else cap;
  std::ofstream matlabfile;
  matlabfile.open("GlobalGrid_Cap.txt");

  auto write_out_matlab_file = [&](const auto&p, const auto&q){

    matlabfile<<tiles_total[p].x;
    matlabfile<<" ";
    matlabfile<<tiles_total[p].y;
    matlabfile<<" ";
    matlabfile<<tiles_total[p].tileLayer;
    matlabfile<<" ";

    matlabfile<<tiles_total[q].x;
    matlabfile<<" ";
    matlabfile<<tiles_total[q].y;
    matlabfile<<" ";
    matlabfile<<tiles_total[q].tileLayer;
    matlabfile<<" ";
              
    matlabfile<<std::endl;

  };

  for(unsigned int i=0;i<tiles_total.size();i++){

      for(unsigned int j=0;j<tiles_total[i].north.size();j++){

           if(tiles_total[i].north[j].capacity>0 or Cap_Ncap){    
              write_out_matlab_file(i,tiles_total[i].north[j].next); 
             }
          }

      for(unsigned int j=0;j<tiles_total[i].south.size();j++){

           if(tiles_total[i].south[j].capacity>0 or Cap_Ncap){    
              write_out_matlab_file(i,tiles_total[i].south[j].next); 
             }
          }

      for(unsigned int j=0;j<tiles_total[i].east.size();j++){

           if(tiles_total[i].east[j].capacity>0 or Cap_Ncap){    
              write_out_matlab_file(i,tiles_total[i].east[j].next); 
             }
          }


      for(unsigned int j=0;j<tiles_total[i].west.size();j++){

           if(tiles_total[i].west[j].capacity>0 or Cap_Ncap){    
              write_out_matlab_file(i,tiles_total[i].west[j].next); 
             }
          }


      for(unsigned int j=0;j<tiles_total[i].down.size();j++){

           if(tiles_total[i].down[j].capacity>0 or Cap_Ncap){    
              write_out_matlab_file(i,tiles_total[i].down[j].next);  
             }
          }

      for(unsigned int j=0;j<tiles_total[i].up.size();j++){

           if(tiles_total[i].up[j].capacity>0 or Cap_Ncap){    
              write_out_matlab_file(i,tiles_total[i].up[j].next);  
             }
          }

       }


  matlabfile.close();

}

GlobalGrid::GlobalGrid(const GlobalGrid& other):x_unit(other.x_unit), y_unit(other.y_unit), metal2tile(other.metal2tile), tile2metal(other.tile2metal), Start_index(other.Start_index), End_index(other.End_index), tiles_total(other.tiles_total), drc_info(other.drc_info), layerNo(other.layerNo), metalLayerNo(other.metalLayerNo), lowest_metal(other.lowest_metal), highest_metal(other.highest_metal), maxXidx(other.maxXidx), maxYidx(other.maxYidx), LL(other.LL), UR(other.UR), XYmap(other.XYmap), YXmap(other.YXmap), XYSet(other.XYSet), YXSet(other.YXSet) {
   ////this->x_unit         =other.x_unit;
   //this->y_unit         =other.y_unit;
   //this->metal2tile     =other.metal2tile;
   //this->tile2metal     =other.tile2metal;
   //this->Start_index    =other.Start_index;
   //this->End_index      =other.End_index;
   //this->tiles_total    =other.tiles_total;
   //this->drc_info       =other.drc_info;
   //this->layerNo        =other.layerNo;
   //this->metalLayerNo   =other.metalLayerNo;
   //this->lowest_metal   =other.lowest_metal;
   //this->highest_metal  =other.highest_metal;
   //this->LL             =other.LL;
   //this->UR             =other.UR ;
   //this->XYmap          =other.XYmap;
   //this->YXmap          =other.YXmap;
   //this->XYSet          =other.XYSet;
   //this->YXSet          =other.YXSet;
   //this->maxXidx        =other.maxXidx;
   //this->maxYidx        =other.maxYidx;
}

GlobalGrid::GlobalGrid(PnRDB::Drc_info& drc_info, int LLx, int LLy, int URx, int URy, int Lmetal, int Hmetal, int tileLayerNo, int scale) {
  this->lowest_metal=Lmetal;
  this->highest_metal=Hmetal;
  this->layerNo=ceil(double(Hmetal-Lmetal+1)/tileLayerNo); // no of tile layer
  this->metalLayerNo=drc_info.Metal_info.size(); // no of max metal layer
  this->Start_index.resize(this->layerNo,0);
  this->End_index.resize(this->layerNo,-1);
  this->XYmap.resize(this->layerNo); // XYmap
  this->YXmap.resize(this->layerNo); // YXmap
  this->XYSet.resize(this->metalLayerNo);
  this->YXSet.resize(this->metalLayerNo);
  this->IDXmap.resize(this->layerNo);
  this->drc_info=drc_info;
  this->LL.x=LLx; this->LL.y=LLy;
  this->UR.x=URx; this->UR.y=URy;
  this->maxXidx=0; this->maxYidx=0;

  if(drc_info.Metal_info.at(Lmetal).direct==0) { //vertical
    this->x_unit=drc_info.Metal_info.at(Lmetal).grid_unit_x*scale;
    this->y_unit=drc_info.Metal_info.at(Lmetal+1).grid_unit_y*scale;
  } else { // horizontal
    this->x_unit=drc_info.Metal_info.at(Lmetal+1).grid_unit_x*scale;
    this->y_unit=drc_info.Metal_info.at(Lmetal).grid_unit_y*scale;
  }
  // 1. Create tiles
  spdlog::debug("GlobalGrid-Info: create tiles");

  for(int i=Lmetal;i<=Hmetal;i+=tileLayerNo) {
    spdlog::debug("layer {0}",i);
    int layerIdx=(i-Lmetal)/tileLayerNo; // current tile index
    this->tile2metal[layerIdx].clear();
    std::vector<int> tmpV;
    for(int j=0;j<tileLayerNo and i+j<=Hmetal;j++) {
      spdlog::debug("Traverse layer ",j);
      this->metal2tile[i+j]=layerIdx;
      this->tile2metal[layerIdx].insert(i+j);
      tmpV.push_back(i+j);
    }
    spdlog::debug("start of creating tiles");
    this->Start_index.at(layerIdx)=this->tiles_total.size();
    for(int X=this->LL.x; X<this->UR.x; X+=this->x_unit) {

      int Xidx=(X-this->LL.x)/this->x_unit;
      if(Xidx>this->maxXidx) {this->maxXidx=Xidx;}
      RouterDB::tile tmpT;
      if( X+this->x_unit > this->UR.x ) {
        tmpT.width=(this->UR.x-X);
      } else {
        tmpT.width=this->x_unit;
      }
      tmpT.x=X+tmpT.width/2;
      for(int Y=this->LL.y; Y<this->UR.y; Y+=this->y_unit) {
        int Yidx=(Y-this->LL.y)/this->y_unit;
        if(Yidx>this->maxYidx) {this->maxYidx=Yidx;}
        if( Y+this->y_unit > this->UR.y ) {
          tmpT.height=(this->UR.y-Y);
        } else {
          tmpT.height=this->y_unit;
        }
        tmpT.y=Y+tmpT.height/2;
        tmpT.index=this->tiles_total.size();
        tmpT.metal=tmpV;
        tmpT.Xidx=Xidx; tmpT.Yidx=Yidx;
        tmpT.tileLayer=layerIdx;
        //tmpT.metal.clear();
        //for(int j=0;j<tileLayerNo and i+j<=Hmetal;j++) {
        //  tmpT.metal.insert(i+j);
        //}
        RouterDB::point tmpP;
        tmpP.x=tmpT.x; tmpP.y=tmpT.y;
        this->tiles_total.push_back(tmpT);
        this->XYmap.at(layerIdx).insert( std::pair<RouterDB::point, int>(tmpP, this->tiles_total.size()-1) );
        this->YXmap.at(layerIdx).insert( std::pair<RouterDB::point, int>(tmpP, this->tiles_total.size()-1) );
        tmpP.x=Xidx; tmpP.y=Yidx;
        this->IDXmap.at(layerIdx).insert( std::pair<RouterDB::point, int>(tmpP, this->tiles_total.size()-1) );
      }
    }
    this->End_index.at(layerIdx)=this->tiles_total.size()-1;
    spdlog::debug("end of layer {0}", i);
  }
  
  // 2. Add tile edges
  spdlog::debug("GlobalGrid-Info: add tile connections");
  for(int i=Lmetal;i<=Hmetal;++i) {
    int layerIdx=this->metal2tile[i];
    spdlog::debug("layer {0} tile layer {1}",i,layerIdx); //# =======
    std::cout<<"layer "<<i<<" tile layer "<<layerIdx<<std::endl;
    if(drc_info.Metal_info.at(i).direct==0) { //vertical
      std::cout<<"vertical\n";
      for(std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit=this->XYmap.at(layerIdx).begin(); mit!=this->XYmap.at(layerIdx).end(); ++mit) {
        std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit2=mit;
        std::advance(mit2,1);
        if(mit2==this->XYmap.at(layerIdx).end()) {continue;}
        int pre=mit->second; int post=mit2->second;
        RouterDB::tileEdge tmpE;
        if( (mit->first).x!=(mit2->first).x ) {continue;}
        if(this->tiles_total.at(pre).north.empty()) {
          std::cout<<"unit_X 1"<<drc_info.Metal_info.at(i).grid_unit_x<<std::endl;
          tmpE.next=post; tmpE.capacity=this->tiles_total.at(pre).width/drc_info.Metal_info.at(i).grid_unit_x;
          this->tiles_total.at(pre).north.push_back(tmpE);
          std::cout<<"add north edge between "<<pre<<" and "<<post<<std::endl;
        } else {
          std::cout<<"unit_X 2"<<drc_info.Metal_info.at(i).grid_unit_x<<std::endl;
          this->tiles_total.at(pre).north[0].capacity+=this->tiles_total.at(pre).width/drc_info.Metal_info.at(i).grid_unit_x;
          std::cout<<"update north edge between "<<pre<<" and "<<post<<std::endl;
        }
        if(this->tiles_total.at(post).south.empty()) {
          std::cout<<"unit_X 3"<<drc_info.Metal_info.at(i).grid_unit_x<<std::endl;
          tmpE.next=pre; tmpE.capacity=this->tiles_total.at(post).width/drc_info.Metal_info.at(i).grid_unit_x;
          this->tiles_total.at(post).south.push_back(tmpE);
          std::cout<<"add south edge between "<<post<<" and "<<pre<<std::endl;
        } else {
          std::cout<<"unit_X 4"<<drc_info.Metal_info.at(i).grid_unit_x<<std::endl;
          this->tiles_total.at(post).south[0].capacity+=this->tiles_total.at(post).width/drc_info.Metal_info.at(i).grid_unit_x;
          std::cout<<"update south dge between "<<post<<" and "<<pre<<std::endl;
        }
      }
    } else { // horizontal
      std::cout<<"horizotal\n";
      for(std::map<RouterDB::point, int, RouterDB::pointYXComp>::iterator mit=this->YXmap.at(layerIdx).begin(); mit!=this->YXmap.at(layerIdx).end(); ++mit) {
        std::map<RouterDB::point, int, RouterDB::pointYXComp>::iterator mit2=mit;
        std::advance(mit2,1);
        if(mit2==this->YXmap.at(layerIdx).end()) {continue;}
        int pre=mit->second; int post=mit2->second;
        RouterDB::tileEdge tmpE;
        if( (mit->first).y!=(mit2->first).y ) {continue;}
        if(this->tiles_total.at(pre).east.empty()) {
          std::cout<<"unit_y 1"<<drc_info.Metal_info.at(i).grid_unit_y<<std::endl;
          tmpE.next=post; tmpE.capacity=this->tiles_total.at(pre).height/drc_info.Metal_info.at(i).grid_unit_y;
          this->tiles_total.at(pre).east.push_back(tmpE);
          std::cout<<"add east edge between "<<pre<<" and "<<post<<std::endl;
        } else {
          std::cout<<"unit_y 2"<<drc_info.Metal_info.at(i).grid_unit_y<<std::endl;
          this->tiles_total.at(pre).east[0].capacity+=this->tiles_total.at(pre).height/drc_info.Metal_info.at(i).grid_unit_y;
          std::cout<<"update east edge between "<<pre<<" and "<<post<<std::endl;
        }
        if(this->tiles_total.at(post).west.empty()) {
          std::cout<<"unit_y 3"<<drc_info.Metal_info.at(i).grid_unit_y<<std::endl;
          tmpE.next=pre; tmpE.capacity=this->tiles_total.at(post).height/drc_info.Metal_info.at(i).grid_unit_y;
          this->tiles_total.at(post).west.push_back(tmpE);
          std::cout<<"add west edge between "<<post<<" and "<<pre<<std::endl;
        } else {
          std::cout<<"unit_y 4"<<drc_info.Metal_info.at(i).grid_unit_y<<std::endl;
          this->tiles_total.at(post).west[0].capacity+=this->tiles_total.at(post).height/drc_info.Metal_info.at(i).grid_unit_y;
          std::cout<<"update west edge between "<<post<<" and "<<pre<<std::endl;
        }
      }
    }
  }
  for(int k=0;k<this->layerNo-1;++k) {
    for(int i=this->Start_index.at(k);i<=this->End_index.at(k);++i){
      RouterDB::point tmpp;
      tmpp.x=this->tiles_total[i].x;
      tmpp.y=this->tiles_total[i].y;
      std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit=this->XYmap.at(k+1).find(tmpp);
      if(mit!=this->XYmap.at(k+1).end()) {
        // how about the spacing of via?
        RouterDB::tileEdge tmpE;
        int viaNo=this->tiles_total.at(i).metal.back();
        int viaSize=(drc_info.Via_info.at(viaNo).width+drc_info.Via_info.at(viaNo).dist_ss)*( drc_info.Via_info.at(viaNo).width_y+drc_info.Via_info.at(viaNo).dist_ss_y);
        int tileSize=this->tiles_total.at(i).width*this->tiles_total.at(i).height;
        int cap=tileSize/viaSize;
        tmpE.next=mit->second; tmpE.capacity=cap;
        this->tiles_total.at(i).up.push_back(tmpE);
        tmpE.next=i;
        this->tiles_total.at(mit->second).down.push_back(tmpE);
        std::cout<<"add up/down edge between "<<i<<" and "<<mit->second<<std::endl;
      } else {
        std::cout<<"GlobalGrid-Warning: cnnot create vertical edges\n";
      }
    }
  }
}

void GlobalGrid::ConvertRect2Points(int metalIdx, int LLx, int LLy, int URx, int URy) {
  if(this->drc_info.Metal_info.at(metalIdx).direct==0) { // vertical net
    int mainUnit=this->y_unit;
    int minUnit=this->drc_info.Metal_info.at(metalIdx).grid_unit_x;
    int LLy_cc=ceil(double(LLy)/mainUnit)*mainUnit;
    int LLx_cc=ceil(double(LLx)/minUnit)*minUnit;
    for(int y=LLy_cc;y<=URy;y+=mainUnit) {
      for(int x=LLx_cc;x<=URx;x+=minUnit) {
        RouterDB::point tmpP;
        tmpP.x=x; tmpP.y=y;
        this->YXSet.at(metalIdx).insert(tmpP);
      }
    }
  } else { // horizontal net
    int mainUnit=this->x_unit;
    int minUnit=this->drc_info.Metal_info.at(metalIdx).grid_unit_y;
    int LLy_cc=ceil(double(LLy)/minUnit)*minUnit;
    int LLx_cc=ceil(double(LLx)/mainUnit)*mainUnit;
    for(int y=LLy_cc;y<=URy;y+=minUnit) {
      for(int x=LLx_cc;x<=URx;x+=mainUnit) {
        RouterDB::point tmpP;
        tmpP.x=x; tmpP.y=y;
        this->XYSet.at(metalIdx).insert(tmpP);
      }
    }
  }
}

void GlobalGrid::ConvertMetal2Points(int mIdx, int x, int y, int X, int Y) {
  int LLx=x;
  int LLy=y;
  int URx=X;
  int URy=Y;
  if(this->drc_info.Metal_info.at(mIdx).direct==0) { // vertical
    LLx-=this->drc_info.Metal_info.at(mIdx).dist_ss;
    URx+=this->drc_info.Metal_info.at(mIdx).dist_ss;
    LLy-=this->drc_info.Metal_info.at(mIdx).dist_ee;
    URy+=this->drc_info.Metal_info.at(mIdx).dist_ee;
  } else { // horizontal
    LLx-=this->drc_info.Metal_info.at(mIdx).dist_ee;
    URx+=this->drc_info.Metal_info.at(mIdx).dist_ee;
    LLy-=this->drc_info.Metal_info.at(mIdx).dist_ss;
    URy+=this->drc_info.Metal_info.at(mIdx).dist_ss;
  }
  if(LLx<this->LL.x) {LLx=this->LL.x;}
  if(LLy<this->LL.y) {LLy=this->LL.y;}
  if(URx>this->UR.x) {URx=this->UR.x;}
  if(URy>this->UR.y) {URy=this->UR.y;}
  ConvertRect2Points(mIdx, LLx, LLy, URx, URy);
}

void GlobalGrid::ConvertGlobalInternalMetal(std::vector<RouterDB::Block>& Blocks) {
  //std::vector< std::set<RouterDB::point, RouterDB::pointXYComp> > XYset;
  //std::vector< std::set<RouterDB::point, RouterDB::pointYXComp> > YXSet;
  //int mIdx, LLx, LLy, URx, URy;
  for(std::vector<RouterDB::Block>::iterator bit=Blocks.begin(); bit!=Blocks.end(); ++bit) {
    for(std::vector<RouterDB::contact>::iterator pit=bit->InternalMetal.begin(); pit!=bit->InternalMetal.end(); ++pit) {
      ConvertMetal2Points(pit->metal, pit->placedLL.x, pit->placedLL.y, pit->placedUR.x, pit->placedUR.y);
    }
  }
}

void GlobalGrid::ConvertGlobalBlockPin(std::vector<RouterDB::Block>& Blocks, std::vector<RouterDB::Net>& Nets, int excNet) {
  for(std::vector<RouterDB::Net>::iterator nit=Nets.begin(); nit!=Nets.end(); ++nit) {
    if(nit-Nets.begin()==excNet) {continue;}
    for(std::vector<RouterDB::connectNode>::iterator cit=nit->connected.begin(); cit!=nit->connected.end(); ++cit) {
      if(cit->type==RouterDB::BLOCK) {
        int iter=cit->iter; int iter2=cit->iter2;
        for(std::vector<RouterDB::contact>::iterator pit=Blocks.at(iter2).pins.at(iter).pinContacts.begin(); pit!=Blocks.at(iter2).pins.at(iter).pinContacts.end(); ++pit ) {
          ConvertMetal2Points(pit->metal, pit->placedLL.x, pit->placedLL.y, pit->placedUR.x, pit->placedUR.y);
        }
      }
    }
  }
}

void GlobalGrid::AdjustPlateEdgeCapacity() {

  //limits: capacity unbalanced between the edges from one tile, which has little intermetal, and another tile, which has a lot of intermetal. In this case, the capacity should be keep along with the smaller capacity;
 // solution, find all set of intermetal, then adjust the capacity;
  double scale_number = 1.5;
  for(int k=0;k<this->layerNo;++k) {
    std::cout<<"layer "<<k<<std::endl;
    for(int i=this->Start_index.at(k);i<=this->End_index.at(k);++i) {
      std::cout<<"find tile "<<i<<std::endl;
      int x=this->tiles_total.at(i).x;
      int y=this->tiles_total.at(i).y;
      int w=this->tiles_total.at(i).width;
      int h=this->tiles_total.at(i).height;
      int LLx=x-w/2; int LLy=y-h/2;
      int URx=x+w/2; int URy=y+h/2;
      RouterDB::point LL,UL,UR,LR;
      LL.x=LLx; LL.y=LLy; UL.x=LLx; UL.y=URy;
      UR.x=URx; UR.y=URy; LR.x=URx; LR.y=LLy;
      for(unsigned int j=0;j<this->tiles_total.at(i).metal.size();++j) {
        int mIdx=this->tiles_total.at(i).metal.at(j);
        std::cout<<"\t check metal "<<j<<"@"<<mIdx<<" {"<<LLx<<","<< LLy<<"} {"<< URx<<"," <<URy<<"}"<<std::endl;
        int capR;
        if(this->drc_info.Metal_info.at(mIdx).direct==0) { // vertical
          std::cout<<"\t horizontal\n";
          std::set<RouterDB::point, RouterDB::pointYXComp>::iterator itlow, itup;
          itlow=this->YXSet.at(mIdx).lower_bound(LL);
          itup=this->YXSet.at(mIdx).upper_bound(LR);
          capR=0;
          for(std::set<RouterDB::point, RouterDB::pointYXComp>::iterator ii=itlow; ii!=itup; ++ii) {++capR;}
          if(!this->tiles_total.at(i).south.empty()) {
            std::cout<<"\t south cap -"<<capR<<std::endl;
            this->tiles_total.at(i).south[0].capacity-=capR*scale_number;
            if(this->tiles_total.at(i).south[0].capacity<0) {this->tiles_total.at(i).south[0].capacity=0;}
          }
          itlow=this->YXSet.at(mIdx).lower_bound(UL);
          itup=this->YXSet.at(mIdx).upper_bound(UR);
          capR=0;
          for(std::set<RouterDB::point, RouterDB::pointYXComp>::iterator ii=itlow; ii!=itup; ++ii) {++capR;}
          if(!this->tiles_total.at(i).north.empty()) {
            this->tiles_total.at(i).north[0].capacity-=capR*scale_number;
            std::cout<<"\t north cap -"<<capR<<std::endl;
            if(this->tiles_total.at(i).north[0].capacity<0) {this->tiles_total.at(i).north[0].capacity=0;}
          }
        } else { // horizontal
          std::cout<<"\t horizontal\n";
          std::set<RouterDB::point, RouterDB::pointXYComp>::iterator itlow, itup;
          itlow=this->XYSet.at(mIdx).lower_bound(LL);
          itup=this->XYSet.at(mIdx).upper_bound(UL);
          capR=0;
          for(std::set<RouterDB::point, RouterDB::pointXYComp>::iterator ii=itlow; ii!=itup; ++ii) {++capR;}
          if(!this->tiles_total.at(i).west.empty()) {
            std::cout<<"\t west cap -"<<capR<<std::endl;
            this->tiles_total.at(i).west[0].capacity-=capR*scale_number;
            if(this->tiles_total.at(i).west[0].capacity<0) {this->tiles_total.at(i).west[0].capacity=0;}
          }
          itlow=this->XYSet.at(mIdx).lower_bound(LR);
          itup=this->XYSet.at(mIdx).upper_bound(UR);
          capR=0;
          for(std::set<RouterDB::point, RouterDB::pointXYComp>::iterator ii=itlow; ii!=itup; ++ii) {++capR;}
          if(!this->tiles_total.at(i).east.empty()) {
            std::cout<<"\t east cap -"<<capR<<std::endl;
            this->tiles_total.at(i).east[0].capacity-=capR*scale_number;
            if(this->tiles_total.at(i).east[0].capacity<0) {this->tiles_total.at(i).east[0].capacity=0;}
          }
        }
      }
    }
  }
}

void GlobalGrid::AdjustVerticalEdgeCapacityfromInternalMetal( std::vector<RouterDB::Block>& Blocks ) {

  //limits: via capacity is a approximate version. Maybe needs to be improved in the future.
  double scale_number = 2;
  for(int k=0;k<this->layerNo-1;++k) {
    if(this->Start_index.at(k)>this->End_index.at(k)) {
      std::cout<<"GlobalGrid-Error: no tiles on layer "<<k<<std::endl;
      continue;
    }
    int viaNo=this->tiles_total.at( this->Start_index.at(k) ).metal.back();
    for(std::vector<RouterDB::Block>::iterator bit=Blocks.begin(); bit!=Blocks.end(); ++bit) {
      for(std::vector<RouterDB::Via>::iterator pit=bit->InternalVia.begin(); pit!=bit->InternalVia.end(); ++pit) {
        if(viaNo==this->drc_info.Via_model.at(pit->model_index).ViaIdx) {
          int LLx=floor(double(pit->position.x)/this->x_unit);
          int URx=ceil(double(pit->position.x)/this->x_unit);
          int LLy=floor(double(pit->position.y)/this->y_unit);
          int URy=ceil(double(pit->position.y)/this->y_unit);
          if(LLx<this->LL.x) {LLx=this->LL.x;}
          if(LLy<this->LL.y) {LLy=this->LL.y;}
          if(URx>this->UR.x) {URx=this->UR.x;}
          if(URy>this->UR.y) {URy=this->UR.y;}
          RouterDB::point tmpp; tmpp.x=(LLx+URx)/2; tmpp.y=(LLy+URy)/2;
          std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit=this->XYmap.at(k).find(tmpp);
          if(mit!=this->XYmap.at(k).end()) {
            if(!this->tiles_total.at(mit->second).up.empty()) {
              this->tiles_total.at(mit->second).up[0].capacity-=1*scale_number;
              if( this->tiles_total.at(mit->second).up[0].capacity<0 ) {this->tiles_total.at(mit->second).up[0].capacity=0;}
            }
          } else {
            std::cout<<"GlobalGrid-Warning: cannot find tiles to adjust vertical edge cap\n";
          }
          mit=this->XYmap.at(k+1).find(tmpp);
          if(mit!=this->XYmap.at(k+1).end()) {
            if(!this->tiles_total.at(mit->second).down.empty()) {
              this->tiles_total.at(mit->second).down[0].capacity-=1*scale_number;
              if( this->tiles_total.at(mit->second).down[0].capacity<0 ) {this->tiles_total.at(mit->second).down[0].capacity=0;}
            }
          } else {
            std::cout<<"GlobalGrid-Warning: cannot find tiles to adjust vertical edge cap\n";
          }
        }
      }
    }
  }
}

void GlobalGrid::AdjustVerticalEdgeCapacityfromBlockPin( std::vector<RouterDB::Block>& Blocks, std::vector<RouterDB::Net>& Nets, int excNet  ) {
  double scale_number = 2;
  for(int k=0;k<this->layerNo-1;++k) {
    if(this->Start_index.at(k)>this->End_index.at(k)) {
      std::cout<<"GlobalGrid-Error: no tiles on layer "<<k<<std::endl;
      continue;
    }
    int viaNo=this->tiles_total.at( this->Start_index.at(k) ).metal.back();
    for(std::vector<RouterDB::Net>::iterator nit=Nets.begin(); nit!=Nets.end(); ++nit) {
      if(nit-Nets.begin()==excNet) {continue;}
      for(std::vector<RouterDB::connectNode>::iterator cit=nit->connected.begin(); cit!=nit->connected.end(); ++cit) {
        if(cit->type==RouterDB::BLOCK) {
          int iter=cit->iter; int iter2=cit->iter2;
          for(std::vector<RouterDB::Via>::iterator pit=Blocks.at(iter2).pins.at(iter).pinVias.begin(); pit!=Blocks.at(iter2).pins.at(iter).pinVias.end(); ++pit ) {
            if(viaNo==this->drc_info.Via_model.at(pit->model_index).ViaIdx) {
              int LLx=floor(double(pit->position.x)/this->x_unit);
              int URx=ceil(double(pit->position.x)/this->x_unit);
              int LLy=floor(double(pit->position.y)/this->y_unit);
              int URy=ceil(double(pit->position.y)/this->y_unit);
              if(LLx<this->LL.x) {LLx=this->LL.x;}
              if(LLy<this->LL.y) {LLy=this->LL.y;}
              if(URx>this->UR.x) {URx=this->UR.x;}
              if(URy>this->UR.y) {URy=this->UR.y;}
              RouterDB::point tmpp; tmpp.x=(LLx+URx)/2; tmpp.y=(LLy+URy)/2;
              std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit=this->XYmap.at(k).find(tmpp);
              if(mit!=this->XYmap.at(k).end()) {
                if(!this->tiles_total.at(mit->second).up.empty()) {
                  this->tiles_total.at(mit->second).up[0].capacity-=1*scale_number;
                  if( this->tiles_total.at(mit->second).up[0].capacity<0 ) {this->tiles_total.at(mit->second).up[0].capacity=0;}
                }
              } else {
                std::cout<<"GlobalGrid-Warning: cannot find tiles to adjust vertical edge cap\n";
              }
              mit=this->XYmap.at(k+1).find(tmpp);
              if(mit!=this->XYmap.at(k+1).end()) {
                if(!this->tiles_total.at(mit->second).down.empty()) {
                  this->tiles_total.at(mit->second).down[0].capacity-=1*scale_number;
                  if( this->tiles_total.at(mit->second).down[0].capacity<0 ) {this->tiles_total.at(mit->second).down[0].capacity=0;}
                }
              } else {
                std::cout<<"GlobalGrid-Warning: cannot find tiles to adjust vertical edge cap\n";
              }
            }
          }
        }
      }
    }
  }
}

void GlobalGrid::ConvertNetBlockPin(std::set<int>& sSet, std::vector<int>& sVec, int metalIdx, int LLx, int LLy, int URx, int URy) {
  int layerIdx=this->metal2tile[metalIdx];
  std::cout<<"Convert block pin {"<<LLx<<","<<LLy<<"} {"<<URx<<","<<URy<<"} @metal "<<metalIdx<<std::endl;
  int LLx_cc = floor(double(LLx - this->LL.x) / this->x_unit) * this->x_unit + this->LL.x;
  int LLy_cc = floor(double(LLy - this->LL.y) / this->y_unit) * this->y_unit + this->LL.y;
  std::cout<<"LLx_cc "<<LLx_cc<<" LLy_cc "<<LLy_cc<<std::endl;
  for(int x=LLx_cc; x<URx; x+=this->x_unit) {
    for(int y=LLy_cc; y<URy; y+=this->y_unit) {
      RouterDB::point tmpp; 
      std::cout<<"Or check "<<x<<" , "<<y<<std::endl;
      if (x + this->x_unit > this->UR.x) {
        tmpp.x = x + (this->UR.x - x) / 2;
      } else {
        tmpp.x = x + this->x_unit / 2;
      }

      if (y + this->y_unit > this->UR.y) {
        tmpp.y = y + (this->UR.y - y) / 2;
      } else {
        tmpp.y = y + this->y_unit / 2;
      }

      std::cout << "check " << tmpp.x << " , " << tmpp.y << std::endl;
      std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit=this->XYmap.at(layerIdx).find(tmpp);
      if(mit!=this->XYmap.at(layerIdx).end()) {
        sSet.insert(mit->second);
        sVec.push_back(mit->second);
      } else {
        std::cout<<"GlobalGrid-Warning: cannot map block pin to tiles\n";
      }
    }
  }
}

void GlobalGrid::ConverNetTerminal(std::set<int>& sSet, std::vector<int>& sVec, int metalIdx, int x, int y) {
  int layerIdx=this->metal2tile[metalIdx];
  RouterDB::point tmpp;
  int x_cc=floor(double(x)/this->x_unit)*this->x_unit;
  int y_cc=floor(double(y)/this->y_unit)*this->y_unit;

  if(x==this->UR.x and x%this->x_unit==0) { tmpp.x=x-this->x_unit/2;
  } else if( x_cc+this->x_unit > this->UR.x ) { tmpp.x=x_cc+(this->UR.x-x_cc)/2;
  } else {tmpp.x=x_cc+this->x_unit/2;}

  if(y==this->UR.y and y%this->y_unit==0) { tmpp.y=y-this->y_unit/2;
  } else if( y_cc+this->y_unit > this->UR.y ) { tmpp.y=y_cc+(this->UR.y-y_cc)/2;
  } else {tmpp.y=y_cc+this->y_unit/2;}

  std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit=this->XYmap.at(layerIdx).find(tmpp);
  if(mit!=this->XYmap.at(layerIdx).end()) {
    sSet.insert(mit->second);
    sVec.push_back(mit->second);
  } else {
    std::cout<<"GlobalGrid-Warning: cannot map terminal to tiles\n";
  }
}

void GlobalGrid::SetNetSink(std::vector<RouterDB::Block>& Blocks, std::vector<RouterDB::Net>& Nets, std::vector<RouterDB::terminal>& Terminals, bool terminal_routing ) {
  int net_index = 0;
  for(std::vector<RouterDB::Net>::iterator nit=Nets.begin(); nit!=Nets.end(); ++nit) {
    std::cout<<"For Net "<<net_index<<std::endl;
    net_index= net_index +1;
    int cNO=nit->connected.size();
    nit->terminals.clear(); nit->connectedTile.clear();
    nit->connectedTile.resize(cNO);
    std::set<int> tSet;
    for(int i=0;i<cNO;++i) {
      int iter=nit->connected.at(i).iter;
      int iter2=nit->connected.at(i).iter2;
      if(nit->connected.at(i).type==RouterDB::BLOCK) { // block pin
        for( std::vector<RouterDB::contact>::iterator cit=Blocks.at(iter2).pins.at(iter).pinContacts.begin(); cit!=Blocks.at(iter2).pins.at(iter).pinContacts.end(); ++cit) {
          ConvertNetBlockPin(tSet, nit->connectedTile.at(i), cit->metal, cit->placedLL.x, cit->placedLL.y, cit->placedUR.x, cit->placedUR.y);
          std::cout<<"Pin Contact LL ( "<<cit->placedLL.x<<" "<<cit->placedLL.y<<" ) UR ( "<<cit->placedUR.x<<" "<<cit->placedUR.y<<" )"<<std::endl;
        }
      } else if(terminal_routing){ // terminal

        for( std::vector<RouterDB::contact>::iterator cit=Terminals.at(iter).termContacts.begin(); cit!=Terminals.at(iter).termContacts.end(); ++cit) {
          //ConverNetTerminal(tSet, nit->connectedTile.at(i), this->lowest_metal, cit->placedCenter.x, cit->placedCenter.y);
          ConvertNetBlockPin(tSet, nit->connectedTile.at(i), cit->metal, cit->placedLL.x, cit->placedLL.y, cit->placedUR.x, cit->placedUR.y);
          std::cout<<"Terminal Contact Center ( "<<cit->placedCenter.x<<" "<<cit->placedCenter.y<<" )"<<std::endl;
        }
/*
        for( std::vector<RouterDB::contact>::iterator cit=Terminals.at(iter).termContacts.begin(); cit!=Terminals.at(iter).termContacts.end(); ++cit) {
          ConverNetTerminal(tSet, nit->connectedTile.at(i), this->lowest_metal, cit->placedCenter.x, cit->placedCenter.y);
          std::cout<<"Terminal Contact Center ( "<<cit->placedCenter.x<<" "<<cit->placedCenter.y<<" )"<<std::endl;
        }
*/
      }
    }
    for(std::set<int>::iterator tit=tSet.begin(); tit!=tSet.end(); ++tit) {
      nit->terminals.push_back(*tit);
    }
    for(unsigned int i=0;i<nit->terminals.size();i++){

        std::cout<<"terminal tile index"<< nit->terminals[i]<<"center ( "<<tiles_total[nit->terminals[i]].x<<" "<<tiles_total[nit->terminals[i]].y<<std::endl;
       
       }
    std::cout<<std::endl;
  }
}
