#ifndef PowerRouter_H_
#define PowerRouter_H_

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <set>
#include <cmath>
#include <algorithm>
#include <limits.h>
#include <bitset>
#include <cstdlib> // system
#include <iterator>
#include <cctype>
#include <unistd.h> // getcwd
#include <map>
#include <set>
#include <utility>//std::pair, make_pair
#include "Grid.h"
#include "Graph.h"
#include "RawRouter.h"
#include "Rdatatype.h"
#include "DetailRouter.h"
#include "../PnRDB/datatype.h"

class PowerRouter : public DetailRouter {

  friend class Grid;

  private:

    vector<double> utilization;//drc_info something like this
    
    PnRDB::Drc_info PowerGrid_Drc_info;
    
    //return PowerGrid to PnRDB
    

  public:
    
    //initialize nets, blocks, based on PnRDB::node & node
    //create power grid,call global router, return some lowest level nodes which is vdd / gnd
    //create some dummy net with source and dest in nets
    //call detail router

    PowerRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, int power_grid, double rate);
    void PowerNetRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, double rate);
    void CreatePowerGrid(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, double rate);
    void returnPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::PowerNet& temp_net);
    void SetSrcDest(RouterDB::Pin temp_pin, RouterDB::PowerGrid Vdd_grid, std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest);
    void Physical_metal_via();
    void Physical_metal_via_power_grid(RouterDB::PowerGrid &temp_grid);
    void GetPhsical_Metal_Via(int i);
    void CreatePowerGridDrc_info();
    void GetData(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, double rate);
    void getBlockData(PnRDB::hierNode& node, int Lmetal, int Hmetal);
    void getNetData(PnRDB::hierNode& node);
    void getPowerGridData(PnRDB::hierNode & node);
    void getTerminalData(PnRDB::hierNode& node);
    void getPowerNetData(PnRDB::hierNode& node);
    void ConvertTerminal(RouterDB::terminal& temp_terminal, PnRDB::terminal pnr_terminal);
    void ConvertContact(RouterDB::contact& temp_metal, PnRDB::contact& pnr_metal);
    void ConvertMetal(RouterDB::Metal& temp_metal,PnRDB::Metal& pnr_metal);
    void ConvertVia(RouterDB::Via &temp_via,PnRDB::Via& pnr_via);
    void ConvertPin(RouterDB::Pin& temp_pin,PnRDB::pin& pnr_pin);
    void CreatePlistNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Net>& Nets);
    void CreatePlistPowerNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::PowerNet>& Nets);
    void CreatePlistPowerGrid(std::vector<std::vector<RouterDB::point> >& plist, RouterDB::PowerGrid Nets);
    void ConvertToMetalPnRDB_Placed_Placed(PnRDB::Metal &temp_metal,RouterDB::Metal router_metal);
    void ReturnPowerGridData(PnRDB::hierNode& node);
    void ReturnPowerNetData(PnRDB::hierNode& node);
    void UpdateVia(RouterDB::Via &temp_via);

};


#endif
