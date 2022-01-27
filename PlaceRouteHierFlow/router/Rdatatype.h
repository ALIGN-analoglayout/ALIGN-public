#ifndef RDATATYPE_H_
#define RDATATYPE_H_

#include <limits.h>

#include <string>
#include <vector>
//#include <iostream>
//#include <utility>
//#include "../PnRDB/datatype.h"
// using std::pair;
// using std::cout;
// using std::endl;
// using std::vector;
// using std::string;
// using std::map;

namespace RouterDB {
struct box;
struct point;
struct vertex;
struct ViaModel;
struct Via;
struct Metal;
struct Candidate;
struct SinkData;
struct Segment;
struct connectNode;
struct Net;
struct Block;
struct Pin;
struct CritNet_S;
struct SymmNet_S;
struct ShieldNet_S;
struct MatchBlock_S;
struct Constraint;
struct contact;
struct R_const;
struct C_const;
struct terminal;
struct pointXYComp;
struct SegPiece;
struct SegOrder;
struct SegOrderComp;
struct SinkDataComp;
struct SinkData2Comp;
struct PowerGrid;
struct PowerNet;

enum NType { BLOCK, TERMINAL };
enum Omark { N, S, W, E, FN, FS, FW, FE };
enum SType { CMM, CVM, CVV, PMM, PVM, PVV, IMM, IVM, IVV };

struct point {
  int x = 0;
  int y = 0;
  point() : x(0), y(0) {}
  point(int ix, int iy) : x(ix), y(iy) {}
};  // structure of integer coordinate

struct contact {
  int metal = -1;
  point originLL, originUR;
  point placedLL, placedUR;
  point originCenter;
  point placedCenter;
};  // structure of contact

struct tileEdge {
  int next;
  int capacity;
};

struct tile {
  int x = -1;
  int y = -1;
  int width;
  int height;
  std::vector<int> metal;
  std::vector<int> origin_metal;
  int tileLayer = -1;
  int index = -1;
  int Yidx = -1;
  int Xidx = -1;
  std::vector<tileEdge> north, south, east, west, down, up;
  // int power; // i is vdd, 0 is gnd;
};

struct vertex {
  int x = -1;
  int y = -1;
  int metal = -1;
  int Cost = INT_MAX;
  // int Cost = -1;
  bool active = false;
  bool via_active_down = true;
  bool via_active_up = true;
  int parent = -1;           // -1 mean source
  int trace_back_node = -1;  // -1 mean source, and will changes for parallel routing
  int index = -1;
  std::vector<int> gridmetal;
  bool expand = 0;  // expand to right (east) for vertical node? expand to up (north) for heriental node?
  // bool offgrid;
  std::vector<int> north;
  std::vector<int> south;
  std::vector<int> east;
  std::vector<int> west;
  int down = -1;
  int up = -1;
  int power;  // i is vdd, 0 is gnd;
  int graph_index = -1;
};

struct ViaModel {
  std::string name;
  int ViaIdx, LowerIdx, UpperIdx;
  std::vector<point> ViaRect, LowerRect, UpperRect;
};

struct Via {
  int model_index;
  point position;
  contact UpperMetalRect, LowerMetalRect, ViaRect;
  // string  ViaName;
  // int ViaLeftXLoc;
  // int ViaRightXLoc;
  // int ViaLowerYLoc;
  // int ViaUpperYLoc;
};

/* currently unused
struct via_point{
  int vIdx;
  point position;
};
*/

struct Metal {
  int MetalIdx;
  std::vector<point> LinePoint;
  int width;
  contact MetalRect;
  // string MetalName;
  // bool EncMetalFlag;
  // int MetalStartLeftXLoc;
  // int MetalStartLowerYLoc;
  // int MetalEndRightXLoc;
  // int MetalEndUpperYLoc;
};

struct Candidate {
  std::string CandiName;
  // int   CandiLength;
  int TotMetalWeightByLength;
  int CandiBend;
  std::vector<Metal> metals;
  std::vector<Via> vias;
  point start, end;
  int startMetal, endMetal;
  int TotMetalWeightByCa;
  int valIdx;
  bool chosen = false;
};

struct SteinerTree {
  std::vector<std::pair<int, int> > path;  // index of edges in graph
  int valIdx;
  int sym_val_Idx = -1;
};

// struct Node{
//  int x,y;
//};

struct PowerGrid {
  std::string name;
  std::vector<Metal> metals;
  std::vector<Via> vias;
  std::vector<Metal> merged_metals;
  bool power = 1;  // 1 is vdd, 0 is gnd
};

struct PowerNet {
  // 1 get netName, power, Shilding, pins from node
  std::string netName;  // vdd? gnd?
  bool power = 1;       // 1 is vdd, 0 is gnd
  // std::vector<Segment> seg;
  bool shielding = false;  // shielding constraint
  std::vector<Pin> pins;
  std::vector<Metal> path_metal;
  std::vector<Via> path_via;
  std::vector<int> extend_label;
  bool DoNotRoute=false;
};

struct SinkData {
  std::vector<point> coord;  // 1@original pin:LL,UR; terminal: center; 2@grided pin/terminal: grids
  int metalIdx;
  // int iterNet;
  // vector<int> ver_idx;
};

struct DetailPoint {
  int x;
  int y;
  int iterNet = -1;
};

struct connectNode {
  NType type;  // 1: blockPin; 2. Terminal
  int iter;    // 1: #blockPin; 2. #Terminal
  int iter2;   // 1: #block
};

struct Segment {
  std::vector<SinkData> sourceList, destList;  // for each contact
  std::vector<SinkData> sourceGrid, destGrid;  // for detail router connection
  connectNode sourceType;
  connectNode destType;
  // bool sourceGridScale, destGridScale; // true for wide grid, false for regular grid
  // Node source;//No use
  // Node dest;//No use
  // string source_metal;//No use
  // string dest_metal;//No use
  // string src_name;//No use
  // string dest_name;//No use
  std::vector<Candidate> candis;
  int chosenCand = -1;
};

struct Net {
  std::string netName;
  int degree;
  bool isTerminal = false;
  int terminal_idx = -1;
  // vector<string> pinName;//No use
  // vector<string> blockName;//No use
  int numSeg;
  std::vector<Segment> seg;
  // vector<Segment> grid_seg;
  // vector<string> segName;
  bool shielding = false;      // shielding constraint
  bool sink2Terminal = false;  // if connected to terminal , duplicate?
  int symCounterpart = -1;     // symmetry const
  int global_sym = -1;
  int global_center = -1;
  bool sym_H;                          // if 1 H, else V
  int center;                          // symmetry center;
  int iter2SNetLsit = -1;              // iterator to the list of symmetry nets
  std::vector<connectNode> connected;  // list of connected components
  std::string priority = "";           // critical net constraint
  std::vector<Metal> path_metal;
  std::vector<int> extend_label;
  std::vector<Via> path_via;
  std::vector<SteinerTree> STs;
  std::vector<std::pair<int, int> > global_path;  // index of tiles, representing start point & end point of tiles
  std::vector<int> terminals;
  std::vector<std::vector<int> > connectedTile;
  std::vector<R_const> R_constraints;
  std::vector<C_const> C_constraints;
  int STindex = 0;
  int multi_connection = 1;
  bool DoNotRoute=false;
  // void display();
};

struct Block {
  std::string blockName, blockMaster;
  // int blockIdx;
  int numTerminals;
  point originLL, originUR;
  point placedLL, placedUR;
  // int LL_x, LL_y;
  // int UL_x, UL_y;
  // int UR_x, UR_y;
  // int LR_x, LR_y;
  int height;
  int width;
  int area;
  Omark orient;
  bool isLeaf;
  // bool capacitorFlag;
  // int LL_x_placed, LL_y_placed;
  // int LR_x_placed, LR_y_placed;
  // int UL_x_placed, UL_y_placed;
  // int UR_x_placed, UR_y_placed;
  // int length_placed, width_placed;
  // vector<string> pinName;
  std::vector<Pin> pins;
  std::vector<contact> InternalMetal;
  std::vector<Via> InternalVia;  // added 121918
  std::string gdsfile;
};

struct Pin {
  std::string pinName;
  std::vector<contact> pinContacts;
  std::vector<Via> pinVias;
  int netIter;
};

// struct Layer{
//  int layerNum;
//  vector<Pin> pins;
//  double layerMetalWidth;
//  int layerDataType;
//};
//
// struct InternalPath{
//  int layerNum;
//  int PathDataType;
//  double PathWidth;
//  double ori_x, ori_y;
//  vector<double> PathLength;
//  vector<string> PathDirect;
//};

struct CritNet_S {
  std::string NetName;
  std::string degree;
};

struct SymmNet_S {
  std::string NetName;
  std::string BlockName;
  std::string PinName;
};

struct ShieldNet_S {
  std::string NetName;
};

struct MatchBlock_S {
  std::string BlockName1;
  std::string BlockName2;
};

struct Constraint {
  std::vector<CritNet_S> CritNet;
  std::vector<SymmNet_S> SymmNet;
  std::vector<ShieldNet_S> ShieldNet;
  std::vector<MatchBlock_S> MatchBlock;
};

struct R_const {
  std::vector<std::pair<int, int> > start_pin;  // pair.first blocks id pair.second pin id
  std::vector<std::pair<int, int> > end_pin;    // if pair.frist blocks id = -1 then it's terminal
  std::vector<double> R;
};

struct C_const {
  std::vector<std::pair<int, int> > start_pin;  // pair.first blocks id pair.second pin id
  std::vector<std::pair<int, int> > end_pin;    // if pair.frist blocks id = -1 then it's terminal
  std::vector<double> C;
};

// struct bbox {
//  vector<point> polygon; // list of coordinates of polygon
//  point LL,LR,UL,UR;
//}; // structure of boundary box, assum rectangle

struct terminal {
  std::string name = "";
  std::string type = "";  // add by yg //////////////////////////////////////
  int netIter = -1;
  std::vector<contact> termContacts;
};

struct pointXYComp {
  bool operator()(const point& lhs, const point& rhs) const {
    if (lhs.x == rhs.x) {
      return lhs.y < rhs.y;
    } else {
      return lhs.x < rhs.x;
    }
  }
};

struct pointYXComp {
  bool operator()(const point& lhs, const point& rhs) const {
    if (lhs.y == rhs.y) {
      return lhs.x < rhs.x;
    } else {
      return lhs.y < rhs.y;
    }
  }
};

struct pointSetComp {
  bool operator()(const std::pair<int, RouterDB::point>& lhs, const std::pair<int, RouterDB::point>& rhs) const {
    if (lhs.first == rhs.first) {
      if (lhs.second.x == rhs.second.x) {
        return lhs.second.y < rhs.second.y;
      } else {
        return lhs.second.x < rhs.second.x;
      }
    } else {
      return lhs.first < rhs.first;
    }
  }
};

struct pointSetComp2 {
  bool operator()(const std::pair<int, RouterDB::point>& lhs, const std::pair<int, RouterDB::point>& rhs) const {
    if (lhs.second.y == rhs.second.y) {
      return lhs.second.x < rhs.second.x;
    } else {
      return lhs.second.y < rhs.second.y;
    }
  }
};

struct tileComp {
  bool operator()(const tile& lhs, const tile& rhs) const {
    if (lhs.x == rhs.x) {
      if (lhs.y == rhs.y) {
        if (lhs.index == rhs.index) {
          return lhs.metal[0] < rhs.metal[0];
        } else {
          return lhs.index < rhs.index;
        }
      } else {
        return lhs.y < rhs.y;
      }

    } else {
      return lhs.x < rhs.x;
    }
  }
};

struct SinkDataComp {
  bool operator()(const SinkData& lhs, const SinkData& rhs) const {
    if (lhs.coord[0].x == rhs.coord[0].x) {
      if (lhs.coord[0].y == rhs.coord[0].y) {
        if (lhs.metalIdx == rhs.metalIdx) {
          if (lhs.coord.size() > 1 && lhs.coord.size() > 1) {
            if (lhs.coord[1].x == rhs.coord[1].x) {
              return lhs.coord[1].y < rhs.coord[1].y;
            } else {
              return lhs.coord[1].x < rhs.coord[1].x;
            }
          } else
            return lhs.coord[0].x < rhs.coord[0].x;
        } else {
          return lhs.metalIdx < rhs.metalIdx;
        }
      } else {
        return lhs.coord[0].y < rhs.coord[0].y;
      }
    } else {
      return lhs.coord[0].x < rhs.coord[0].x;
    }
  }
};

struct SinkData2Comp {
  bool operator()(const SinkData& lhs, const SinkData& rhs) const {
    if (lhs.coord[0].y == rhs.coord[0].y) {
      if (lhs.coord[0].x == rhs.coord[0].x) {
        return lhs.metalIdx < rhs.metalIdx;
      } else {
        return lhs.coord[0].x < rhs.coord[0].x;
      }
    } else {
      return lhs.coord[0].y < rhs.coord[0].y;
    }
  }
};

struct ViaComp {
  bool operator()(const Via& lhs, const Via& rhs) const {
    if (lhs.model_index == rhs.model_index) {
      if (lhs.position.x == rhs.position.x) {
        return lhs.position.y < rhs.position.y;
      } else {
        return lhs.position.x < rhs.position.x;
      }
    } else {
      return lhs.model_index < rhs.model_index;
    }
  }
};

struct MetalComp {
  bool operator()(const Metal& lmetal, const Metal& rmetal) const {
    if (lmetal.MetalIdx == rmetal.MetalIdx) {
      if (lmetal.LinePoint[0].x == rmetal.LinePoint[0].x) {
        if (lmetal.LinePoint[0].y == lmetal.LinePoint[0].y) {
          if (lmetal.LinePoint[1].x == rmetal.LinePoint[1].x) {
            return lmetal.LinePoint[1].y < rmetal.LinePoint[1].y;
          } else {
            return lmetal.LinePoint[1].x < rmetal.LinePoint[1].x;
          }
        } else {
          return lmetal.LinePoint[0].y < rmetal.LinePoint[0].y;
        }
      } else {
        return lmetal.LinePoint[0].x < rmetal.LinePoint[0].x;
      }
    } else {
      return lmetal.MetalIdx < rmetal.MetalIdx;
    }
  }
};
struct pairComp {
  bool operator()(const std::pair<int, int>& lhs, const std::pair<int, int>& rhs) const {
    if (lhs.first == rhs.first) {
      return lhs.second < rhs.second;
    } else {
      return lhs.first < rhs.first;
    }
  }
};

struct SegPiece {
  SType type;         // SType {CMM, CVM, CVV, PMM, PVM, PVV, IMM, IVM, IVV}
  int layerIdx = -1;  // Depends on type
  int LLx, LLy, URx, URy;
  //  CMM, CVM, CVV, PMM, PVM, PVV, IMM, IVM, IVV}
  int aiter = -1;  //  net  net  net  blk  blk  blk  inm  inv  inv
  int biter = -1;  //  seg  seg  seg  pin  pin  pin  cont via  via
  int citer = -1;  //  cand cand cand cont via  via
  int diter = -1;  //  met  via  via
  int valIdx = -1;
};

struct SegOrder {
  int index;  // index to vector of SegPiece
  int val;
};

struct SegOrderComp {
  bool operator()(const SegOrder& lhs, const SegOrder& rhs) const { return lhs.val < rhs.val; }
};

struct box {
  point LL, UR;
};
}  // namespace RouterDB
#endif
