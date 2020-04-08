#include "Router.h"

/*
Router::Router(PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, std::string binaryDIR) {
  this->GR=NULL;
  GlobalRouter GR2(node, drcData, Lmetal, Hmetal, binaryDIR);
  DetailRouter(node, GR2, 1, 1);
  
};
*/

void Router::RouteWork(int mode, PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, std::string binaryDIR, int h_skip_factor, int v_skip_factor) {
  //mode 0 global router, 1 detail router, 2 power grid router, 3 power net router, 4 gcell global router, 5 gcell detail router
  //mode 6 intel gcell global router
  if(mode==0) {
    std::cout<<"RouteWork "<<mode<<std::endl;
    this->GR=new GlobalRouter(node, drcData, Lmetal, Hmetal, binaryDIR);
  } else if(mode==1){
    std::cout<<"RouteWork "<<mode<<std::endl;
    DetailRouter(node, *(this->GR), 1, 1);
  } else if(mode==2){
    std::cout<<"RouteWork "<<mode<<std::endl;
    PowerRouter(node, drcData, Lmetal, Hmetal, 1, h_skip_factor, v_skip_factor);  
  } else if(mode==3){
    std::cout<<"RouteWork "<<mode<<std::endl;
    PowerRouter(node, drcData, Lmetal, Hmetal, 0, h_skip_factor, v_skip_factor);
  } else if(mode==4){
    std::cout<<"RouteWork "<<mode<<std::endl;
    this->GGR = new GcellGlobalRouter(node, drcData, Lmetal, Hmetal, binaryDIR);
  } else if(mode==5){
    std::cout<<"RouteWork "<<mode<<std::endl;
    GcellDetailRouter(node, *(this->GGR), 1, 1);
  } else if(mode==6){
    std::cout<<"RouteWork "<<mode<<std::endl;
    node.isIntelGcellGlobalRouter = true;
    this->GGR = new GcellGlobalRouter(node, drcData, Lmetal, Hmetal, binaryDIR);
  }
 
};
