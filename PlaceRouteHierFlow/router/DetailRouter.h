#ifndef DETAILROUTER_H_
#define DETAILROUTER_H_

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
#include "GlobalRouter.h"
#include "Graph.h"
#include "Grid.h"
#include "RawRouter.h"
#include "Rdatatype.h"

class DetailRouter : public GlobalRouter {
  friend class Grid;
  // friend class PowerRouter;

  private:
  int global_grid_scale;

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
  DetailRouter();  // initial Nets & Blocks with node data
  DetailRouter(PnRDB::hierNode& HierNode, GlobalRouter& GR, int path_number, int grid_scale);
  // void RecoverOverlap();
  // void Connection();
  // bool CheckOverlapped_part(int i, int j, int k);
  // bool CheckConnection_Source(RouterDB::Segment& temp_seg);
  // bool CheckConnection_Dest(RouterDB::Segment& temp_seg);
  void CreatePlistBlocks(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Block>& Blocks);
  // void CreatePlistNets(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Net>& Nets);
  void CreatePlistTerminals(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::terminal> Terminals);
  // void CreatePlistNets_DetailRouter(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Net>& Nets);
  void UpdatePlistNets(std::vector<std::vector<RouterDB::Metal> >& physical_path, std::vector<std::vector<RouterDB::point> >& plist);
  void GetPhsical_Metal(std::vector<std::vector<RouterDB::Metal> >& physical_path);
  // void InsertPathToCand_Start(std::vector<std::vector<RouterDB::Metal> > &physical_path, RouterDB::Segment temp_seg);
  // void InsertPathToCand_Start(std::vector<std::vector<RouterDB::Metal> > &physical_path, RouterDB::Segment &temp_seg);
  // void InsertPathToCand_End(std::vector<std::vector<RouterDB::Metal> > &physical_path, RouterDB::Segment &temp_seg);
  void ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy);
  // void CheckOverlapMetals(std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x, std::vector<RouterDB::Net>& nets);
  void Physical_metal_via();
  // void AddMetalToPin();
  // void checkPathMetalToPin(int i, int j);

  void create_detailrouter();
  std::vector<std::vector<RouterDB::SinkData> > findPins(RouterDB::Net temp_net);
  std::vector<RouterDB::Metal> findGlobalPath(RouterDB::Net temp_net);
  void splitPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::Net& temp_net);
  void lastmile_source(std::vector<std::vector<RouterDB::Metal> >& temp_path, std::vector<RouterDB::SinkData> temp_source);
  void lastmile_dest(std::vector<std::vector<RouterDB::Metal> >& temp_path, std::vector<RouterDB::SinkData> temp_source);
  void lastmile_source_new(std::vector<std::vector<RouterDB::Metal> >& temp_path, std::vector<RouterDB::SinkData> temp_source);
  void lastmile_dest_new(std::vector<std::vector<RouterDB::Metal> >& temp_path, std::vector<RouterDB::SinkData> temp_source);
  void updateSource(std::vector<std::vector<RouterDB::Metal> > temp_path, std::vector<RouterDB::SinkData>& temp_source);

  void NetToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index);
  void NetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::Net& net);
  void NetToNodeBlockPins(PnRDB::hierNode& HierNode, RouterDB::Net& net);
  void returnPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::Net& temp_net);

  // void BlockInterMetalToNodeInterMetal(PnRDB::hierNode& HierNode);
  void ReturnHierNode(PnRDB::hierNode& HierNode);
  // void ConvertToContactPnRDB_Placed_Origin(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
  // void ConvertToContactPnRDB_Placed_Placed(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
  // void ConvertToViaPnRDB_Placed_Origin(PnRDB::Via& temp_via, RouterDB::Via& router_via);
  // void ConvertToViaPnRDB_Placed_Placed(PnRDB::Via& temp_via, RouterDB::Via& router_via);
  // void TerminalToNodeTerminal(PnRDB::hierNode& HierNode);
  void GetPhsical_Metal_Via(int i);
  void GetPhsical_Via_contacts(std::vector<std::vector<RouterDB::Metal> > physical_path, std::vector<RouterDB::contact>& temp_via_contact);
  void UpdateVia(RouterDB::Via& temp_via);
};

#endif
