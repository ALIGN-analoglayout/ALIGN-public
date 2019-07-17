#ifndef ROUTER_H_
#define ROUTER_H_

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <cmath>
#include <algorithm>
#include <limits.h>
#include <bitset>
#include <cstdlib>
#include <iterator>
#include <cctype>
#include <unistd.h>

#include "Rdatatype.h"
#include "GlobalRouter.h"
#include "GcellGlobalRouter.h"
#include "DetailRouter.h"
#include "GcellDetailRouter.h"
#include "PowerRouter.h"
#include "../PnRDB/datatype.h"
//using std::cout;
//using std::endl;


class Router {
  private:
    GlobalRouter *GR;
    GcellGlobalRouter *GGR;
  public:
    Router() {};
    Router(PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, std::string binaryDIR);
    void RouteWork(int mode, PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, std::string binaryDIR);
};
#endif
