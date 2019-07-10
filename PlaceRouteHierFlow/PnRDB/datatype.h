#ifndef DATATYPE_H_
#define DATATYPE_H_

#include <vector>
#include <string>
#include <map>
#include <utility>
using std::vector;
using std::string;
using std::map;
using std::pair;

namespace PnRDB {

struct point;
struct connectNode;
struct net;
struct bbox;
struct pin;
struct contact;
struct block;
struct terminal;
struct hierNode;
struct SymmBlock;
struct SymmNet;
struct Preplace;
struct Alignment;
struct AlignBlock;
struct Abument;
struct MatchBlock;
struct lefMacro;
struct blockComplex;
struct CCCap;
struct SymmPairBlock;
struct Metal;
struct ViaModel;
struct Via;
struct PowerGrid;
struct PowerNet;
struct PortPos;

/// Part 1: declaration of enum types
enum NType {Block, Terminal};
enum Omark {N, S, W, E, FN, FS, FW, FE};
enum Smark {H, V};
enum Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};

/// Part 2: declaration of sturctures for placer and router
struct point {
  int x=0;
  int y=0;
}; // structure of integer coordinate

struct bbox {
  vector<point> polygon; // list of coordinates of polygon
  point LL,LR,UL,UR;
}; // structure of boundary box, assum rectangle

struct contact {
  string metal="";
  bbox originBox;
  bbox placedBox;
  point originCenter;
  point placedCenter;
}; // structure of contact

struct connectNode {
  NType type; // 1: blockPin; 2. Terminal
  int iter; // 1: #blockPin; 2. #Terminal
  int iter2; // 1: #block
}; // structure of connected component of nets

struct net {
  string name="";
  bool shielding=false; // shielding constraint
  bool sink2Terminal=false; // if connected to terminal
  int degree=0;
  int symCounterpart=-1; // symmetry const
  int iter2SNetLsit=-1; // iterator to the list of symmetry nets
  vector<connectNode> connected; // list of connected components
  string priority=""; // critical net constraint
  vector<contact> segments; // segment inform needs to be updated after routing
  vector<contact> interVias;////TEMPORARY!!!+Jinhyun
  vector<Metal> path_metal;
  vector<Via> path_via;
  vector<contact> connectedContact; // for writing global route results
  Smark axis_dir=V; // H: horizontal symmetry axis; V: veritcal symmetry axis
  int axis_coor=-1; //y coordinate: horizontal symmetry axis; x coordinate: vertical symmetry axis
}; // structure of nets

struct Metal{
  int MetalIdx;
  vector<point> LinePoint;
  int width;
  contact MetalRect;
};

struct pin {
  string name="";
  string type; // Input, Output, Inout
  string use; //SIGNAL, POWER
  int netIter=-1;
  vector<contact> pinContacts;
// 2019-2-27 Updates for VIA model
  vector<Via> pinVias;
}; // structure of block pin

// 2019-2-27 Updates for VIA model
struct Via{
  int model_index;
  point originpos, placedpos;
  contact UpperMetalRect, LowerMetalRect, ViaRect;
};

struct block {
  // Basic information
  string name="";
  string master="";
  string lefmaster="";
  string type="";
  int width=0;
  int height=0;
  bool isLeaf=true;
  bbox originBox;
  point originCenter;
  string gdsFile="";
  // Placement information
  Omark orient;
  bbox placedBox;
  point placedCenter;
  // Symmetry constraint
  //int SBidx;
  //int counterpart;
  // Block pin
  vector<pin> blockPins;
  vector<contact> interMetals;
  vector<Via> interVias;
  vector<pin> dummy_power_pin; //power pins below to this block, but needs updated hierachy
}; // structure of block

struct terminal {
  string name="";
  string type=""; //add by yg //////////////////////////////////////
  int netIter=-1;
  vector<contact> termContacts; // only used for exchange of placed coordinates in top-level
}; // structure of terminal

struct blockComplex {
  std::vector<block> instance;
  int selectedInstance=-1;
  int child=-1;
  int instNum=0;
};

struct PowerGrid{
  vector<Metal> metals;
  vector<Via> vias;
  bool power = 1;//1 is vdd, 0 is gnd;
};

struct PowerNet {
  string name="";
  bool power = 1; // 1 is vdd, 0 is gnd
  //bool shielding=false; // shielding constraint
  //bool sink2Terminal=false; // if connected to terminal
  //int degree=0;
  //int symCounterpart=-1; // symmetry const
  //int iter2SNetLsit=-1; // iterator to the list of symmetry nets
  //vector<connectNode> connected; // list of connected components
  vector<pin> Pins; //power pins
  vector<connectNode> connected;
  vector<connectNode> dummy_connected;
  //string priority=""; // critical net constraint
  //vector<contact> segments; // segment inform needs to be updated after routing
  //vector<contact> interVias;////TEMPORARY!!!+Jinhyun
  vector<Metal> path_metal;
  vector<Via> path_via;
}; // structure of nets

struct layoutAS {
  int width=0;
  int height=0;
  string gdsFile="";
  vector<blockComplex> Blocks;
  vector<net> Nets;
  vector<terminal> Terminals;
  //vector<pin> blockPins;
  //vector<contact> interMetals;
  //vector<Via> interVias;
};

struct hierNode {
  bool isCompleted=false;
  bool isTop=false;
  int width=0;
  int height=0;
  string name="";
  string gdsFile="";
  vector<int> parent;
  vector<blockComplex> Blocks;
  vector<net> Nets;
  vector<terminal> Terminals;

//added by yg for power net part
  PowerGrid Vdd;
  PowerGrid Gnd;
  vector<PowerNet> PowerNets;
//added by yg

  //Updated
  vector<pin> blockPins;
  vector<contact> interMetals;
  vector<Via> interVias;

  vector<layoutAS> PnRAS;

  // Member variables for constratins
  vector<SymmNet> SNets;
  vector<SymmPairBlock> SPBlocks;
  //vector<SymmBlock> SBlocks;
  vector<Preplace> Preplace_blocks;
  vector<Alignment> Alignment_blocks;
  vector<AlignBlock> Align_blocks;
  vector<Abument> Abument_blocks;
  vector<MatchBlock> Match_blocks;
  vector<CCCap> CC_Caps;
  vector<PortPos> Port_Location;
  int bias_Hgraph=92;
  int bias_Vgraph=92;

}; // structure of vertex in heirarchical tree



/// Part 3: declaration of structures for constraint data

struct SymmNet {
  net net1, net2;
  int iter1, iter2; // iterator to the list of real nets
};

//struct SymmBlock {
//  vector< pair<int,int> > sympair;
//  vector< pair<int,Smark> > selfsym;
//  int dnode;
//};

struct SymmPairBlock {
  vector< pair<int,int> > sympair;
  vector< pair<int,Smark> > selfsym;
};

struct Preplace {
  int blockid1;
  int blockid2;
  string conner;
  int distance;
  int horizon; // 1 is h, 0 is v.
};

struct Alignment {
  int blockid1;
  int blockid2;
  int distance;
  int horizon; // 1 is h, 0 is v.
};

struct Abument {
  int blockid1;
  int blockid2;
  int distance;
  int horizon; // 1 is h, 0 is v.
};

struct MatchBlock {
  int blockid1;
  int blockid2;
  //int distance;
  //int horizon; // 1 is h, 0 is v.
};

struct AlignBlock {
  std::vector<int> blocks;
  int horizon; // 1 is h, 0 is v.
};

struct PortPos {
  int tid;
  Bmark pos;
};

struct CCCap {
  vector<int> size;
  string CCCap_name;
  string Unit_capacitor;
  bool cap_ratio = 0;
  int cap_r = -1;
  int cap_s = -1;
};

/// Part 4: declaration of structures for LEF data
struct lefMacro {
  int width=0, height=0;
  string name="";
  vector<pin> macroPins;
  vector<contact> interMetals;
  string master="";
};

/// PArt 5: declaration of structures for design rule data
struct designRule {
  map<string, int> MinWidth;
  map<string, int> MaxSpace;
  map<string, int> EnMax;
  map<string, int> TrkSpacing;
  map<string, int> grid_unit_x, grid_unit_y;
};

/// PArt 6: uniform DRC rule
struct ViaModel {
  string name;
  int ViaIdx, LowerIdx, UpperIdx;
  std::vector<point> ViaRect, LowerRect, UpperRect;
};

struct metal_info {
  string name;
  int layerNo;
  int width;  //from minwidth MinWidth["M1"]
  int dist_ss;//side to side distance  from SpaceNumTem found the minimim one SpaceNumTem["M1"]
  int direct;//direction, 1 is H, 0 is V  added it by your self
  int grid_unit_x;
  int grid_unit_y;
  int minL;
  int maxL;
  int dist_ee;
};

struct via_info {
  string name;
  int layerNo;
  int lower_metal_index;
  int upper_metal_index;
  int width;  //drData.MinWidth["V6"], X direction width
  int width_y; // Y direction width
  int cover_l;//the length that the via should be coverage   EnMax["V4M5"] EnMax["V4M4"]
  int cover_l_P;
  int cover_u;
  int cover_u_P;
  int dist_ss; //via spacing, X direction spacing
  int dist_ss_y; // Y direction spacing
};

struct Drc_info {
  int MaxLayer; //index
  map<string, int> Metalmap, Viamap;
  vector<metal_info> Metal_info;
  vector<via_info> Via_info;
  vector<int> metal_weight;
  vector<ViaModel> Via_model;
  vector<string> MaskID_Metal;
  vector<string> MaskID_Via;
};

}

#endif
