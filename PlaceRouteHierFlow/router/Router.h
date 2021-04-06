#ifndef ROUTER_H_
#define ROUTER_H_


#include <string>
#include "../PnRDB/datatype.h"

class GlobalRouter;
class GcellGlobalRouter;

class Router {
  private:
    GlobalRouter *GR;
    GcellGlobalRouter *GGR;
  public:
    Router() {};
    void RouteWork(int mode, PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, std::string binaryDIR, int h_skip_factor, int v_skip_factor, std::string inputfile);
};
#endif
