#ifndef PowerRouter_H_
#define PowerRouter_H_

#include <assert.h>
#include <limits.h>

#include <algorithm>
#include <bitset>
#include <cctype>
#include <cmath>
#include <cstdlib>  // system
#include <fstream>
#include <iostream>
#include <iterator>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#ifdef WINDOWS
#include <Windows.h>  // getcwd
#else
#include <unistd.h>  // getcwd
#endif
#include <map>
#include <set>
#include <utility>  //std::pair, make_pair

#include "../PnRDB/datatype.h"
#include "A_star.h"
#include "GcellDetailRouter.h"
#include "Graph.h"
#include "Grid.h"
#include "RawRouter.h"
#include "Rdatatype.h"

class PowerRouter : public GcellDetailRouter {
  friend class Grid;

  private:
  PnRDB::Drc_info PowerGrid_Drc_info;
  vector<double> utilization;

  // return PowerGrid to PnRDB

  public:
  // initialize nets, blocks, based on PnRDB::node & node
  // create power grid,call global router, return some lowest level nodes which is vdd / gnd
  // create some dummy net with source and dest in nets
  // call detail router

  PowerRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, int power_grid, int h_skip_factor, int v_skip_factor);
  PowerRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, int power_grid, string inputfile);
  void PowerNetRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal);
  void CreatePowerGrid(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, int hskip_factor, int v_skip_factor);
  void returnPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::PowerNet& temp_net, std::vector<std::vector<int> > extend_labels);
  void SetSrcDest(RouterDB::Pin temp_pin, RouterDB::PowerGrid Vdd_grid, std::vector<RouterDB::SinkData>& temp_source,
                  std::vector<RouterDB::SinkData>& temp_dest);
  void Physical_metal_via();
  void Physical_metal_via_power_grid(RouterDB::PowerGrid& temp_grid);
  void GetPhsical_Metal_Via(int i);
  void CreatePowerGridDrc_info(int hskip_factor, int v_skip_factor);
  void GetData(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal);
  void getBlockData(PnRDB::hierNode& node, int Lmetal, int Hmetal);
  void getNetData(PnRDB::hierNode& node);
  void getPowerGridData(PnRDB::hierNode& node);
  void getTerminalData(PnRDB::hierNode& node);
  void getPowerNetData(PnRDB::hierNode& node);
  void ConvertTerminal(RouterDB::terminal& temp_terminal, PnRDB::terminal pnr_terminal);
  void ConvertContact(RouterDB::contact& temp_metal, PnRDB::contact& pnr_metal);
  void ConvertMetal(RouterDB::Metal& temp_metal, PnRDB::Metal& pnr_metal);
  void ConvertVia(RouterDB::Via& temp_via, PnRDB::Via& pnr_via);
  void ConvertPin(RouterDB::Pin& temp_pin, PnRDB::pin& pnr_pin);
  void CreatePlistNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Net>& Nets);
  void CreatePlistPowerNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::PowerNet>& Nets);
  void CreatePlistPowerGrid(std::vector<std::vector<RouterDB::point> >& plist, RouterDB::PowerGrid Nets);
  void ConvertToMetalPnRDB_Placed_Placed(PnRDB::Metal& temp_metal, RouterDB::Metal router_metal);
  void ReturnPowerGridData(PnRDB::hierNode& node);
  void ReturnPowerNetData(PnRDB::hierNode& node);
  void UpdateVia(RouterDB::Via& temp_via);
  void ExtendMetal();
  void ExtendMetals(int i);
  void UpdateMetalContact(RouterDB::Metal& temp_metal);
  void ExtendY(RouterDB::Metal& temp_metal, int extend_dis);
  void ExtendX(RouterDB::Metal& temp_metal, int extend_dis);
  void ReturnInternalMetalContact(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x_contact, int net_num);
  void InsertRoutingContact(A_star& a_star, Grid& grid, std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp>& Pset_via,
                            std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& contacts, int net_num);
  void InsertInternalVia_PowerGrid(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp>& Pset_via, RouterDB::PowerGrid& temp_grid);
  void InsertInternalVia_Net(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp>& Pset_via, std::vector<RouterDB::Net>& temp_Nets);
  void Initial_powerrouter_report_info(PnRDB::routing_net& temp_routing_net, int i);
  void Update_powerrouter_report_info(PnRDB::routing_net& temp_routing_net, int i, int j, int pathMark);
  void Max_Min_Contact(PnRDB::contact& temp_contact, int& LLx, int& LLy, int& URx, int& URy);
  int FindMulti_Connection_Number(int i, PnRDB::hierNode& node);
  void CreatePowerGridDrc_info_DC(string inputfile);
  void CreatePowerGrid_DC(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, int Lmetal, int Hmetal, string inputfile);
  void ExtendX_PN(RouterDB::Metal& temp_metal, int extend_dis, bool P);
  void ExtendY_PN(RouterDB::Metal& temp_metal, int extend_dis, bool P);
  void UpdatePowerGridLLUR(int Lmetal, int Hmetal);
};

#endif
