#include "Router.h"

Router::Router(PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, std::string binaryDIR) {
  GlobalRouter GR2(node, drcData, Lmetal, Hmetal, binaryDIR);
  DetailRouter(node, GR2, 1, 1);
  
};

void Router::RouteWork(int mode, PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, std::string binaryDIR) {
  //GlobalRouter GR(node, drcData, Lmetal, Hmetal, binaryDIR);
  //DetailRouter(node, GR, 1, 1);
  //mode 0 global router, 1 detail router, 2 power grid router, 3 power net router
  if(mode==0) {
    std::cout<<"RouteWork "<<mode<<std::endl;
    this->GR=new GlobalRouter(node, drcData, Lmetal, Hmetal, binaryDIR);
  } else if(mode==1){
    std::cout<<"RouteWork "<<mode<<std::endl;
    DetailRouter(node, *(this->GR), 1, 1);
  } else if(mode==2){
    std::cout<<"RouteWork "<<mode<<std::endl;
    PowerRouter(node, drcData, Lmetal, Hmetal, 1);  
  } else if(mode==3){
    std::cout<<"RouteWork "<<mode<<std::endl;
    PowerRouter(node, drcData, Lmetal, Hmetal, 0);
  }
 
};
