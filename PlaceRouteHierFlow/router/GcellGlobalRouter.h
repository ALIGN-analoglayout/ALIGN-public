#ifndef GCELLGLOBALROUTER_H_
#define GCELLGLOBALROUTER_H_

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <cmath>
#include <algorithm>
#include <limits.h>
#include <bitset>
#include <cstdlib> // system
#include <iterator>
#include <assert.h>
#include <cctype>
#include <unistd.h> // getcwd
#include <map>
#include <set>
#include <utility>//std::pair, make_pair
#include "GlobalGrid.h"
#include "GlobalGraph.h"
//#include "GlobalRouter.h"
#include "RawRouter.h"
#include "Rdatatype.h"
#include "../PnRDB/datatype.h"

/*
#ifdef _cplusplus
extern "C" {
#endif

#include <stdio.h>
#include "lp_lib.h"
#define LPSOLVEAPIFROMLIBDEF
#include "lp_explicit.h"

#ifdef _cplusplus
}
#endif
*/


extern "C"
{
#include <stdio.h>
#include "lp_lib.h"
}


class GcellGlobalRouter : public RawRouter {
 
  friend class GlobalGrid;
  friend class GcellDetailRouter;
  
  private:
    struct IntPairComp {
      bool operator() (const std::pair<int,int>& lhs, const std::pair<int,int>& rhs) const
      {
        if(lhs.first==rhs.first) {
        return lhs.second<rhs.second;
        } else {
        return lhs.first<rhs.first;
        }
      }
    };
    struct valInfo {
      int netIter;
      int STIter;
      int segIter;
      int candIter;
      int valIter;
    };
    struct slackInfo {
      int valIter;
      int pieceType; // 0 for metal, 1 for via
      int pieceIter1;
      int pieceIter2;
    };

    char cwd[PATH_MAX];
    std::vector<valInfo> ValArray;
    int NumOfVar;
    lprec *lp;//Data structure for lp_solve
    GlobalGrid Gcell;
    //vector<RouterDB::Net> Nets;
    //vector<RouterDB::Block> Blocks;
    //RouterDB::point LL; //LL for entire node
    //RouterDB::point UR; //UR for entire node
    //RouterDB::point LL_graph; //LL for create graph
    //RouterDB:;point UR_graph; //UR for create graph
    //vector<RouterDB::SinkData> Source; //what is the correct defination of Source and Dest?
    //vector<RouterDB::SinkData> Dest; //what is the correct defination of Source and Dest?
    //int path_number = 5; //number candidate path
    //vector<PnRDB::Drc_info> drc_info;
    //int lowest_metal, highest_metal; //index of lowest metal & highest metal
    //int grid_scale; //dynamic grid_scal

  public:
    GcellGlobalRouter();
    GcellGlobalRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, const std::string &bianryDIR); //initial Nets & Blocks with node data, also LL, UR
//    void UpdateLLURSD(int i, int j);// Update Source and Dest based on j-th segment of i-th net; Also LL_graph UR_graph
//    void listSegments(); //mutlipin to two pin based on stiner tree
//    void GetShorestPath(Graph& graph);//return the shortest path to Nets
//    void LP_solver();
//    // added by wbxu
    long int get_number(string str);
    void placeTerminals(); // reuse original function: placeTerminals
    //void listSegments(const std::string &binaryDIR); // reuse original function
    //std::vector<RouterDB::point> GetMaxMinSrcDest(std::vector<RouterDB::SinkData>& source, std::vector<RouterDB::SinkData>& dest);
    void getData(PnRDB::hierNode& node, int Lmetal, int Hmetal);
    void getDRCdata(PnRDB::Drc_info& drcData);
    int ILPSolveRouting(GlobalGrid &grid, GlobalGraph &graph, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set);
    std::set<RouterDB::tile, RouterDB::tileComp> CreateTileSet(GlobalGrid &grid);
    std::vector<int> Get_Potential_Steiner_node(std::vector<int> t, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, GlobalGrid &grid);
    int JudgeSymmetry(std::vector<std::pair<int,int> > &path,std::vector<std::pair<int,int> > &sy_path, std::map<int,int> &sy_map);
    std::vector<int> GenerateSTsUniqueV(RouterDB::Net &temp_net);
    void CopySTs(RouterDB::Net &temp_net, RouterDB::Net &sy_temp_net, std::map<int,int> &temp_map, std::map<int,int> &sy_temp_map);
    void MirrorSymSTs(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set);
    std::map<int,int> GenerateSymMap(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, std::vector<int> terminals, bool H, int center);
    int PrimeSetGenerate(std::vector<std::vector<int> > &connectedTiles, std::vector<std::vector<int> > &sy_connectedTiles, std::map<int,int> &net_map, std::map<int,int> &sy_net_map);
    void Update_terminals(RouterDB::Net &temp_net);
    void transformCenter(bool H, int &center, GlobalGrid &grid);
    void SymNet(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set);
    int SymNetTerminal_PrimeSet(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, RouterDB::Net &temp_net, RouterDB::Net &sym_net, bool H, int center);
    int CopyPath(std::vector<std::pair<int,int> > &path, std::map<int,int> &temp_map, std::vector<std::pair<int,int> > &sy_path);
    void AssignContact(RouterDB::contact &RouterDB_contact, PnRDB::contact &PnRDB_contact);
    void AssignMetal(RouterDB::terminal &temp_Terminal, int horizontal_index, int vertical_index, int times);
    void Determine_Terminal_Center(int horizontal_index, int vertical_index, int times);
    void PlaceTerminal();
    //void getPhsical_metal_via(int i, int j);


    //void NetToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index);
    //void NetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::Net& net);
    //void NetToNodeBlockPins(PnRDB::hierNode& HierNode, RouterDB::Net& net);
    //void BlockInterMetalToNodeInterMetal(PnRDB::hierNode& HierNode);
    void ReturnHierNode(PnRDB::hierNode& HierNode);
    //void ConvertToContactPnRDB_Placed_Origin(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
    //void ConvertToContactPnRDB_Placed_Placed(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
    //void ConvertToViaPnRDB_Placed_Origin(PnRDB::Via& temp_via, RouterDB::Via& router_via);
    //void ConvertToViaPnRDB_Placed_Placed(PnRDB::Via& temp_via, RouterDB::Via& router_via);
    //void TerminalToNodeTerminal(PnRDB::hierNode& HierNode);
    
};

#endif
