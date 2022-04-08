#ifndef GCELLDETAILROUTER_H_
#define GCELLDETAILROUTER_H_

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
#include "GcellGlobalRouter.h"
#include "GlobalGraph.h"
#include "GlobalGrid.h"
#include "GlobalRouter.h"
#include "Graph.h"
#include "Grid.h"
#include "RawRouter.h"
#include "Rdatatype.h"
#include "math.h"

class GcellDetailRouter : public GcellGlobalRouter {
  friend class GlobalGrid;
  friend class Grid;
  friend class PowerRouter;

  private:
  GlobalGrid Gcell;
  PnRDB::Router_report temp_report;
  std::string HierName;
  /*
     int End_Metal_Flag = 1;

     struct DetailSegMark{
       //for each segment
       int overlapFlag_seg = -1; //-1 not routered, 0 nonoverlap, 1 overlapped
       std::vector<int> overlapFlag_metal; // 0 nonoverlap, 1 overlapped
       std::vector<int> iterMetals; //iter to the index of cleanMetals
       std::vector<std::vector<RouterDB::Metal> > cleanMetals; //clean metals for overlapped metal
     };

     struct DetailNetMark{
        std::vector<DetailSegMark> Mark_seg;
     };

     std::vector<DetailNetMark> DetailRouterMarks;
  */
  public:
  GcellDetailRouter();  // initial Nets & Blocks with node data
  GcellDetailRouter(PnRDB::hierNode &HierNode, GcellGlobalRouter &GR, int path_number, int grid_scale);
  // void RecoverOverlap();
  // void Connection();
  // bool CheckOverlapped_part(int i, int j, int k);
  // bool CheckConnection_Source(RouterDB::Segment& temp_seg);
  // bool CheckConnection_Dest(RouterDB::Segment& temp_seg);
  void CreatePlistBlocks(std::vector<std::vector<RouterDB::point>> &plist, std::vector<RouterDB::Block> &Blocks);
  // void CreatePlistNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Net>& Nets);
  void CreatePlistTerminals(std::vector<std::vector<RouterDB::point>> &plist, std::vector<RouterDB::terminal> &Terminals);
  // void CreatePlistNets_DetailRouter(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Net>& Nets);
  void UpdatePlistNets(std::vector<std::vector<RouterDB::Metal>> &physical_path, std::vector<std::vector<RouterDB::point>> &plist,std::vector<std::vector<int>> extend_labels);
  void GetPhsical_Metal(std::vector<std::vector<RouterDB::Metal>> &physical_path);
  // void InsertPathToCand_Start(std::vector<std::vector<RouterDB::Metal> > &physical_path, RouterDB::Segment temp_seg);
  // void InsertPathToCand_Start(std::vector<std::vector<RouterDB::Metal> > &physical_path, RouterDB::Segment &temp_seg);
  // void InsertPathToCand_End(std::vector<std::vector<RouterDB::Metal> > &physical_path, RouterDB::Segment &temp_seg);
  void ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point>> &plist, int mIdx, int LLx, int LLy, int URx, int URy);
  // void CheckOverlapMetals(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x, std::vector<RouterDB::Net>& nets);
  void Physical_metal_via();
  // void AddMetalToPin();
  // void checkPathMetalToPin(int i, int j);
  void calculate_extension_length();
  void create_detailrouter();
  void create_detailrouter_old();
  // std::vector<std::vector<RouterDB::SinkData> > findPins(RouterDB::Net temp_net);
  std::vector<RouterDB::Metal> findGlobalPath(RouterDB::Net &temp_net);
  void splitPath(std::vector<std::vector<RouterDB::Metal>> &temp_path, RouterDB::Net &temp_net);
  void lastmile_source(std::vector<std::vector<RouterDB::Metal>> &temp_path, std::vector<RouterDB::SinkData> &temp_source);
  void lastmile_dest(std::vector<std::vector<RouterDB::Metal>> &temp_path, std::vector<RouterDB::SinkData> &temp_source);
  void lastmile_source_new(std::vector<std::vector<RouterDB::Metal>> &temp_path, std::vector<RouterDB::SinkData> &temp_source);
  void lastmile_dest_new(std::vector<std::vector<RouterDB::Metal>> &temp_path, std::vector<RouterDB::SinkData> &temp_source);
  void updateSource(std::vector<std::vector<RouterDB::Metal>> &temp_path, std::vector<RouterDB::SinkData> &temp_source);

  void NetToNodeNet(PnRDB::hierNode &HierNode, RouterDB::Net &net, int net_index);
  void NetToNodeInterMetal(PnRDB::hierNode &HierNode, RouterDB::Net &net);
  void NetToNodeBlockPins(PnRDB::hierNode &HierNode, RouterDB::Net &net);
  void returnPath(std::vector<std::vector<RouterDB::Metal>> &temp_path, RouterDB::Net &temp_net, std::vector<std::vector<int>> extend_labels);
  std::vector<RouterDB::Metal> CpSymPath(std::vector<RouterDB::Metal> &temp_path, int H, int center);
  RouterDB::contact SymContact(RouterDB::contact &temp_contact, bool H, int center);
  RouterDB::SinkData Sym_contact(RouterDB::SinkData &temp_contact, bool H, int center);
  int Cover_Contact(RouterDB::SinkData &temp_contact, RouterDB::SinkData &sym_temp_contact, RouterDB::SinkData &cover_contact);
  std::vector<RouterDB::SinkData> FindCommon_Contact(std::vector<RouterDB::SinkData> &temp_contact, std::vector<RouterDB::SinkData> &sym_temp_contact, bool H,
                                                     int center);
  int findPins_Sym(Grid &grid, RouterDB::Net &temp_net, RouterDB::Net &sym_temp_net, bool H, int center,
                   std::vector<std::vector<RouterDB::SinkData>> &temp_pins, std::vector<std::vector<RouterDB::SinkData>> &sym_temp_pins,
                   std::vector<std::vector<RouterDB::SinkData>> &Common_contacts);
  std::vector<std::vector<RouterDB::SinkData>> findPins_new(Grid &grid, RouterDB::Net &temp_net);
  std::vector<std::vector<RouterDB::SinkData>> findPins_new_old(Grid &grid, RouterDB::Net &temp_net);
  void SortPins(std::vector<std::vector<RouterDB::SinkData>> &temp_Pin);
  void CreatePlistSymBlocks(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &set_plist, RouterDB::point gridll, RouterDB::point gridur, int H,
                            int center, RouterDB::point symgridll, RouterDB::point symgridur);
  void CreatePlistContact(std::vector<std::vector<RouterDB::point>> &plist, std::vector<RouterDB::contact> &Contacts);
  void CreatePlistSymNets(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &set_plist, RouterDB::point gridll, RouterDB::point gridur, bool H,
                          int center, RouterDB::point symgridll, RouterDB::point symgridur);
  // std::vector<std::vector<RouterDB::SinkData> > findPins_new(Grid& grid, RouterDB::Net &temp_net);
  // std::vector<std::vector<RouterDB::SinkData> > findPins(RouterDB::Net temp_net);

  // void BlockInterMetalToNodeInterMetal(PnRDB::hierNode& HierNode);
  void ReturnHierNode(PnRDB::hierNode &HierNode);
  void printNetsInfo();
  // void ConvertToContactPnRDB_Placed_Origin(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
  // void ConvertToContactPnRDB_Placed_Placed(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
  // void ConvertToViaPnRDB_Placed_Origin(PnRDB::Via& temp_via, RouterDB::Via& router_via);
  // void ConvertToViaPnRDB_Placed_Placed(PnRDB::Via& temp_via, RouterDB::Via& router_via);
  // void TerminalToNodeTerminal(PnRDB::hierNode& HierNode);
  void GetPhsical_Metal_Via(int i);
  void BlockInterMetalToNodeInterMetal(PnRDB::hierNode &HierNode);
  void TerminalToNodeTerminal(PnRDB::hierNode &HierNode);
  void ConvertToViaPnRDB_Placed_Origin(PnRDB::Via &temp_via, RouterDB::Via &router_via);
  void ConvertToContactPnRDB_Placed_Origin(PnRDB::contact &pnr_contact, RouterDB::contact &router_contact);
  void ConvertToViaPnRDB_Placed_Placed(PnRDB::Via &temp_via, RouterDB::Via &router_via);
  void ConvertToContactPnRDB_Placed_Placed(PnRDB::contact &pnr_contact, RouterDB::contact &router_contact);
  void JudgeTileCoverage(std::vector<std::pair<int, int>> &tile_index, std::vector<std::vector<RouterDB::SinkData>> &temp_pins, GlobalGrid &Gcell);
  int Tile_Cover_Contact(RouterDB::SinkData &temp_contact, RouterDB::SinkData &sym_temp_contact);
  void CheckTile(RouterDB::Net &temp_net, GlobalGrid &Gcell);
  void GetPhsical_Via_contacts(std::vector<std::vector<RouterDB::Metal>> &physical_path, std::vector<RouterDB::contact> &temp_via_contact);
  std::vector<std::pair<int, int>> MappingToConnected(RouterDB::R_const &temp_R, RouterDB::Net &temp_net);
  void GatherSourceDest(std::vector<std::pair<int, int>> &global_path, std::vector<int> &temp_src, std::vector<int> &temp_dest, std::vector<int> &Tile_Source,
                        std::vector<int> &Tile_Dest);
  std::vector<int> EstimateDist(RouterDB::R_const &temp_R, RouterDB::Net &temp_net);
  int Estimate_multi_connection_number(RouterDB::R_const &temp_R, std::vector<int> &temp_dis);
  void ExtendMetal();
  void ExtendY(RouterDB::Metal &temp_metal, int extend_dis);
  void ExtendX(RouterDB::Metal &temp_metal, int extend_dis);
  void UpdateMetalContact(RouterDB::Metal &temp_metal);
  void UpdateVia(RouterDB::Via &temp_via);
  void CreatePlistSingleContact(std::vector<std::vector<RouterDB::point>> &plist, RouterDB::contact &Contacts);
  void CreatePlistSrc_Dest(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &src_dest_plist, std::vector<RouterDB::SinkData> &temp_src,
                           std::vector<RouterDB::SinkData> &temp_dest);
  void SinkData_contact(RouterDB::SinkData &temp_contact, RouterDB::contact &result_contact);
  void modify_tile_metals(RouterDB::Net &Net, bool set);
  void Copy_tile_metals();
  void Adding_tiles_for_terminal(int tile_index, std::vector<std::pair<int, int>> &global_path);
  void ConvertRect2GridPoints_Via(std::vector<std::vector<RouterDB::point>> &plist, int mIdx, int LLx, int LLy, int URx, int URy);
  void Generate_Block_Terminal_Internal_Metal_Set(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x);
  void ReturnInternalMetalContact(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x_contact, int net_num);
  void Initial_rouer_report_info(PnRDB::routing_net &temp_routing_net, int i);
  int R_constraint_based_Parallel_routing_number(int i);
  void Global_Path_Operation_For_Pins(int i, std::vector<std::pair<int, int>> &global_path);
  void Global_Path_Operation_For_Symmetry_Pins(int i, std::vector<std::pair<int, int>> &global_path);
  Grid Generate_Grid_Net(int i);
  void Grid_Inactive(Grid &grid, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net,
                     RouterDB::point &gridll, RouterDB::point &gridur);
  int Found_Pins_and_Symmetry_Pins(Grid &grid, int i, std::vector<std::vector<RouterDB::SinkData>> &temp_pins);
  void Symmetry_metal_Inactive(int i, int sym_flag, Grid &grid, RouterDB::point sym_gridll, RouterDB::point sym_gridur, RouterDB::point &gridll,
                               RouterDB::point &gridur);
  std::vector<RouterDB::SinkData> Initial_source_pin(std::vector<std::vector<RouterDB::SinkData>> &temp_pins, int &source_lock);
  void Update_rouer_report_info(PnRDB::routing_net &temp_routing_net, int i, int j, int pathMark);
  void Detailed_router_set_src_dest(Grid &grid, std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest, int i,
                                    RouterDB::point &sym_gridll, RouterDB::point &sym_gridur, RouterDB::point &gridll, RouterDB::point &gridur,
                                    std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &src_dest_plist,
                                    std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net, int sym_flag);
  void Update_Grid_Src_Dest(Grid &grid, int source_lock, std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &src_dest_plist,
                            std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest,
                            std::vector<std::vector<RouterDB::Metal>> &physical_path);
  void Symmetry_Routing(int sym_flag, int i, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net);
  void InsertInternalVia(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, std::vector<RouterDB::Block> &Blocks);
  void InsertRoutingVia(A_star &a_star, Grid &grid, std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via);
  void AddViaSpacing(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, Grid &grid, RouterDB::point LL, RouterDB::point UR);
  void AddViaEnclosure(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, Grid &grid,
                       std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net,
                       RouterDB::point LL, RouterDB::point UR);
  void AddViaEnclosure_old(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via, Grid &grid,
                           std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net);
  RouterDB::SinkData Contact2Sinkdata(RouterDB::contact &contact);
  void InsertContact2Contact(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &from, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &to);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> CombineTwoSets(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &set1,
                                                                      std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &set2);
  void InsertRoutingContact(A_star &a_star, Grid &grid, std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> &Pset_via,
                            std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &contacts, int net_num);
  void ExtendMetals(int i);
  void Topology_extraction(vector<RouterDB::Metal> &temp_path);
  void Mirror_Topology(std::vector<RouterDB::Metal> &sym_path, int HV_sym, int center);
  void ExtendX_PN(RouterDB::Metal &temp_metal, int extend_dis, bool P);
  void ExtendY_PN(RouterDB::Metal &temp_metal, int extend_dis, bool P);
  void get_internal_metal_via();

  void create_detailrouter_new();
  void InsertPhysicalPathToSetX(int net_index, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x);
  void Refresh_Grid(Grid &grid);
  void returnPath_new(std::vector<std::vector<RouterDB::Metal>> &temp_path, int net_index, std::vector<std::vector<int>> extend_labels);
  void ReturnInternalMetalContactALL(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x_contact);
  void Grid_Inactive_new(Grid &grid, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set, RouterDB::point &gridll, RouterDB::point &gridur);
  void Detailed_router_set_src_dest_new(Grid &grid, std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest,
                                                     int i, RouterDB::point &sym_gridll, RouterDB::point &sym_gridur, RouterDB::point &gridll,
                                                     RouterDB::point &gridur, std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &src_dest_plist,
                                                     std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_net, int sym_flag);
  void EraseSourceDestPinContact(std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x_contact);
  void ExtendMetalsPhysicalPath(std::vector<std::vector<RouterDB::Metal>> &physical_path, std::vector<std::vector<int>> &extend_labels);
  void generate_set_data(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x);
  void InsertSourceDestPinContact(std::vector<RouterDB::SinkData> &temp_source, std::vector<RouterDB::SinkData> &temp_dest, std::set<RouterDB::SinkData, RouterDB::SinkDataComp> &Set_x_contact);

};

#endif
