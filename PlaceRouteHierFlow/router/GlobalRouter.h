#ifndef GLOBALROUTER_H_
#define GLOBALROUTER_H_

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
#include <cctype>
#ifdef WINDOWS
#include <Windows.h> // getcwd
#else
#include <unistd.h> // getcwd
#endif
#include <map>
#include <set>
#include <utility>//std::pair, make_pair
#include "Grid.h"
#include "Graph.h"
#include "RawRouter.h"
#include "Rdatatype.h"
#include "../PnRDB/datatype.h"
#include "spdlog/spdlog.h"

class GlobalRouter : public RawRouter {
 
  friend class Grid;
  friend class DetailRouter;
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
      int segIter;
      int STiter;
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
    int NumOfVar;
    int SlackCounter;
    // wbxu: 20190708 the following codes are to enable ILP to choose candidates
    //lprec *lp;//Data structure for lp_solve
    // wbxu-end
    std::vector<std::vector<RouterDB::SegPiece> > MetalPieces, ViaPieces;
    std::vector<valInfo> ValArray;
    std::vector<slackInfo>  SlackArray;

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
    void AddConnectedContactToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index);
    void AddConnectedContactFunc(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index, RouterDB::NType stype, int siter, int siter2, int smetal, int sx, int sy, int mIdx);

  public:
    GlobalRouter();
    GlobalRouter(PnRDB::hierNode& node, PnRDB::Drc_info& drcData, int Lmetal, int Hmetal, const std::string &bianryDIR); //initial Nets & Blocks with node data, also LL, UR
//    void UpdateLLURSD(int i, int j);// Update Source and Dest based on j-th segment of i-th net; Also LL_graph UR_graph
//    void listSegments(); //mutlipin to two pin based on stiner tree
//    void GetShorestPath(Graph& graph);//return the shortest path to Nets
//    void LP_solver();
//    // added by wbxu
    long int get_number(string str);
    void placeTerminals(); // reuse original function: placeTerminals
    void listSegments(const std::string &binaryDIR); // reuse original function
    //std::vector<RouterDB::point> GetMaxMinSrcDest(std::vector<RouterDB::SinkData>& source, std::vector<RouterDB::SinkData>& dest);
    void getData(PnRDB::hierNode& node, int Lmetal, int Hmetal);
    void getDRCdata(PnRDB::Drc_info& drcData);
    int ILPSolveRouting();
    void CreateMetalViaPieces();
    void ViaSpacingCheck(std::set<std::pair<int,int>, IntPairComp >& checked);
    void MetalSpacingCheck(std::set<std::pair<int,int>, IntPairComp >& checked);
    void ViaSpacingCheckFunc(std::set<std::pair<int,int>, IntPairComp >& checked, int val, int Midx, int ALLx, int ALLy, int AURx, int AURy, int h, int i, int j);
    void MetalSpacingCheckFunc(std::set<std::pair<int,int>, IntPairComp >& checked, int val, int Midx, int ALLx, int ALLy, int AURx, int AURy, int h, int i, int j);
    void UpdateCandidate(std::vector<std::vector<RouterDB::Metal> >& phsical_path, int i, int j);
    void GetPhsical_Metal_Via(int i, int j);
//    void getPhsical_metal_via(int i, int j);
    void NetToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index);
    void NetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::Net& net);
    void NetToNodeBlockPins(PnRDB::hierNode& HierNode, RouterDB::Net& net);
    void BlockInterMetalToNodeInterMetal(PnRDB::hierNode& HierNode);
    void ReturnHierNode(PnRDB::hierNode& HierNode);
    void ConvertToContactPnRDB_Placed_Origin(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
    void ConvertToContactPnRDB_Placed_Placed(PnRDB::contact& pnr_contact,RouterDB::contact& router_contact);
    void ConvertToViaPnRDB_Placed_Origin(PnRDB::Via& temp_via, RouterDB::Via& router_via);
    void ConvertToViaPnRDB_Placed_Placed(PnRDB::Via& temp_via, RouterDB::Via& router_via);
    void TerminalToNodeTerminal(PnRDB::hierNode& HierNode);
    
};

#endif
