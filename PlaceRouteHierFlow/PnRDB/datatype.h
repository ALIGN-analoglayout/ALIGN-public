#ifndef DATATYPE_H_
#define DATATYPE_H_

#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "limits.h"
//#include "../router/Rdatatype.h"
using std::map;
using std::pair;
using std::set;
using std::string;
using std::vector;

//#define PERFORMANCE_DRIVEN
//#define analytical_placer
//#define min_displacement
//#define quadratic_placement
#define ilp
//#define hard_symmetry

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
struct R_const;
struct LinearConst;
struct Multi_LinearConst;
struct C_const;
struct SymmPairBlock;
struct Metal;
struct ViaModel;
struct Via;
struct PowerGrid;
struct PowerNet;
struct PortPos;
struct Router_report;
struct routing_net;
struct Boundary;
struct LinearConst;
struct Multi_LinearConst;
struct Multi_connection;
struct GuardRing;
struct Guardring_Const;
struct guardring_info;

/// Part 1: declaration of enum types
enum NType { Block, Terminal };
enum Omark { N, S, W, E, FN, FS, FW, FE };
enum Smark { H, V };
enum Bmark { TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT };
enum TransformType { Forward, Backward };

/// Part 2: declaration of sturctures for placer and router
struct point {
  int x = 0;
  int y = 0;

  point() : x(0), y(0) {}
  point(int ix, int iy) : x(ix), y(iy) {}

  point operator+(const point& other) const { return point(x + other.x, y + other.y); }
  point operator-(const point& other) const { return point(x - other.x, y - other.y); }
  point& operator+=(const point& other) {
    x += other.x;
    y += other.y;
    return *this;
  }
  point& operator-=(const point& other) {
    x -= other.x;
    y -= other.y;
    return *this;
  }
  point& operator=(const point& other) {
    x = other.x;
    y = other.y;
    return *this;
  }

  bool operator==(const point& other) const { return x == other.x and y == other.y; }
  point scale(const int scx, const int scy) const { return point(x * scx, y * scy); }
  // DAK: We may want to remove these modifying operators:
  //  Danger: they always gets invoked first (over const version) unless object is const
  point& scale(const int scx, const int scy) {
    x *= scx;
    y *= scy;
    return *this;
  }
  // Same as scale
  point int_scale_up(const int scx, const int scy) const { return point(x * scx, y * scy); }
  point& int_scale_up(const int scx, const int scy) {
    x *= scx;
    y *= scy;
    return *this;
  }
  // Scale by a vector
  point scale(const point& sc) const { return point(x * sc.x, y * sc.y); }
  point& scale(const point& sc) {
    x *= sc.x;
    y *= sc.y;
    return *this;
  }
  // Divide versions
  point int_scale_down(const int scx, const int scy) const { return point(x / scx, y / scy); }
  point& int_scale_down(const int scx, const int scy) {
    x /= scx;
    y /= scy;
    return *this;
  }

  //  point operator * (const double sc) const { return scale(sc, sc); }
  point operator*(const int sc) const { return scale(sc, sc); }
  point& operator*=(const int sc) { return scale(sc, sc); }
  //  point& operator *= (const double sc) { return scale(sc, sc); }
  point operator/(const double sc) const { return int_scale_down(sc, sc); }
  point& operator/=(const double sc) { return int_scale_down(sc, sc); }

};  // structure of integer coordinate

struct bbox {
  point LL, UR;

  bbox() : LL(), UR() {}
  bbox(int llx, int lly, int urx, int ury) : LL(llx, lly), UR(urx, ury) {}
  bbox(const PnRDB::bbox& other) : LL(other.LL), UR(other.UR) {}
  bbox(const PnRDB::point& ill, const PnRDB::point& iur) : LL(ill), UR(iur) {}

  // Construct a box representing a dimension
  bbox(const PnRDB::point& dim) : LL(0, 0), UR(dim) {}

  int width() const { return UR.x - LL.x; }
  int height() const { return UR.y - LL.y; }
  point center() const { return point((LL.x + UR.x) / 2, (LL.y + UR.y) / 2); }
  bbox shift(const PnRDB::point& p) const { return bbox(LL + p, UR + p); }
  bbox& shift(const PnRDB::point& p) {
    LL += p;
    UR += p;
    return *this;
  }
  bbox operator+(const PnRDB::point& p) const { return shift(p); }
  bbox& operator+=(const PnRDB::point& p) { return shift(p); }
  bbox scale(const int scx, const int scy) const { return bbox(LL * scx, UR * scy); }
  bbox& scale(const int scx, const int scy) {
    LL *= scx;
    UR *= scy;
    return *this;
  }
  /* bbox scale (const double scx, const double scy) const { return bbox (LL * scx, UR * scy); } */
  /* bbox& scale (const double scx, const double scy) { LL *= scx; UR *= scy; return *this; } */
  //  bbox operator * (const double sc) const { return scale(sc, sc); }
  //  bbox& operator *= (const int sc) { return scale(sc, sc); }
  bbox operator*(const int sc) const { return scale(sc, sc); }
  bbox& operator*=(const double sc) { return scale(sc, sc); }

  bbox int_scale_up(const int scx, const int scy) const { return bbox(LL * scx, UR * scy); }
  bbox& int_scale_up(const int scx, const int scy) {
    LL *= scx;
    UR *= scy;
    return *this;
  }
  bbox int_scale_dn(const int scx, const int scy) const { return bbox(LL / scx, UR / scy); }
  bbox& int_scale_dn(const int scx, const int scy) {
    LL /= scx;
    UR /= scy;
    return *this;
  }
  bbox operator/(const int sc) const { return int_scale_dn(sc, sc); }
  bbox& operator/(const int sc) { return int_scale_dn(sc, sc); }

  bbox bloat(int bx, int by) const { return bbox(LL.x - bx, LL.y - by, UR.x + bx, UR.y + by); }

  bool intersectP(const PnRDB::bbox& other) const { return ((LL.x <= other.UR.x) && (other.LL.x <= UR.x) && (LL.y <= other.UR.y) && (other.LL.y <= UR.y)); }
  bbox intersectBox(const PnRDB::bbox& other) const {
    bbox out;
    out.LL.x = (LL.x > other.LL.x) ? LL.x : other.LL.x;
    if ((LL.x > other.UR.x) || (other.LL.x > UR.x)) out.LL.x = -1;
    out.LL.y = (LL.y > other.LL.y) ? LL.y : other.LL.y;
    if ((LL.y > other.UR.y) || (other.LL.y > UR.y)) out.LL.y = -1;
    //
    out.UR.x = (UR.x < other.UR.x) ? UR.x : other.UR.x;
    if ((LL.x > other.UR.x) || (other.LL.x > UR.x)) out.UR.x = -1;
    out.UR.y = (UR.y < other.UR.y) ? UR.y : other.UR.y;
    if ((LL.y > other.UR.y) || (other.LL.y > UR.y)) out.UR.y = -1;
    return out;
  }
  bool containsP(const PnRDB::bbox& other) const { return ((LL.x <= other.LL.x) && (other.UR.x <= UR.x) && (LL.y <= other.LL.y) && (other.UR.y <= UR.y)); }
  bbox unionBox(const PnRDB::bbox& other) const {
    bbox rt;
    rt.LL.x = (LL.x < other.LL.x ? LL.x : other.LL.x);
    rt.LL.y = (LL.y < other.LL.y ? LL.y : other.LL.y);
    rt.UR.x = (UR.x > other.UR.x ? UR.x : other.UR.x);
    rt.UR.y = (UR.y > other.UR.y ? UR.y : other.UR.y);
    return rt;
  }

};  // structure of boundary box, assum rectangle

struct contact {
  string metal = "";
  bbox originBox;
  bbox placedBox;
  point originCenter;
  point placedCenter;
  contact() : metal(""), originBox(), placedBox(), originCenter(), placedCenter() {}
  contact(const PnRDB::contact& other)
      : metal(other.metal), originBox(other.originBox), placedBox(other.placedBox), originCenter(other.originCenter), placedCenter(other.placedCenter) {}

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
  int tileLayer = -1;
  int index = -1;
  int Yidx = -1;
  int Xidx = -1;
  std::vector<tileEdge> north, south, east, west, down, up;
  // int power; // i is vdd, 0 is gnd;
};

struct connectNode {
  NType type;  // 1: blockPin; 2. Terminal
  int iter;    // 1: #blockPin; 2. #Terminal
  int iter2;   // 1: #block
  double alpha = 1;
};  // structure of connected component of nets

struct globalContact {
  contact conTact;
  int metalIdx;
};

struct net {
  string name = "";
  bool shielding = false;      // shielding constraint
  bool sink2Terminal = false;  // if connected to terminal
  int degree = 0;
  int symCounterpart = -1;        // symmetry const
  int iter2SNetLsit = -1;         // iterator to the list of symmetry nets
  vector<connectNode> connected;  // list of connected components
  string priority = "";           // critical net constraint
  vector<contact> segments;       // segment inform needs to be updated after routing
  vector<contact> interVias;      ////TEMPORARY!!!+Jinhyun
  vector<Metal> path_metal;
  vector<std::pair<int, int>> GcellGlobalRouterPath;
  vector<Via> path_via;
  vector<globalContact> connectedContact;  // for writing global route results
  Smark axis_dir = V;                      // H: horizontal symmetry axis; V: veritcal symmetry axis
  int axis_coor = -1;                      // y coordinate: horizontal symmetry axis; x coordinate: vertical symmetry axis
  vector<std::vector<int>> connectedTile;
  double upperBound = INT_MAX;
  double lowerBound = INT_MIN;
  int multi_connection = 1;
  float weight = 1.0;
};  // structure of nets

struct Metal {
  int MetalIdx;
  vector<point> LinePoint;
  int width;
  contact MetalRect;
};

struct pin {
  string name = "";
  string type;  // Input, Output, Inout
  string use;   // SIGNAL, POWER
  int netIter = -1;
  vector<contact> pinContacts;
  // 2019-2-27 Updates for VIA model
  vector<Via> pinVias;
};  // structure of block pin

// 2019-2-27 Updates for VIA model
struct Via {
  int model_index;
  point originpos, placedpos;
  contact UpperMetalRect, LowerMetalRect, ViaRect;
};

struct PowerNet {
  string name = "";
  bool power = 0;  // 1 is vdd, 0 is gnd
  // bool shielding=false; // shielding constraint
  // bool sink2Terminal=false; // if connected to terminal
  // int degree=0;
  // int symCounterpart=-1; // symmetry const
  // int iter2SNetLsit=-1; // iterator to the list of symmetry nets
  // vector<connectNode> connected; // list of connected components
  vector<pin> Pins;  // power pins
  vector<connectNode> connected;
  vector<connectNode> dummy_connected;
  // string priority=""; // critical net constraint
  // vector<contact> segments; // segment inform needs to be updated after routing
  // vector<contact> interVias;////TEMPORARY!!!+Jinhyun
  vector<Metal> path_metal;
  vector<Via> path_via;
};  // structure of nets

struct block {
  // Basic information
  string name = "";
  string master = "";
  string lefmaster = "";
  string type = "";
  int width = 0;
  int height = 0;
  bool isLeaf = true;
  bool isRead = true;
  bbox originBox;
  point originCenter;
  string gdsFile = "";
  // Placement information
  Omark orient;
  bbox placedBox;
  point placedCenter;
  // Symmetry constraint
  // int SBidx;
  // int counterpart;
  // Block pin
  vector<PowerNet> PowerNets;
  vector<pin> blockPins;
  vector<contact> interMetals;
  vector<Via> interVias;
  vector<pin> dummy_power_pin;  // power pins below to this block, but needs updated hierachy
  vector<GuardRing> GuardRings;
  int HPWL_extend_wo_terminal = 0;
};  // structure of block

struct terminal {
  string name = "";
  string type = "";  // add by yg //////////////////////////////////////
  int netIter = -1;
  vector<contact> termContacts;  // only used for exchange of placed coordinates in top-level
};                               // structure of terminal

struct blockComplex {
  std::vector<block> instance;
  int selectedInstance = -1;
  int child = -1;
  int instNum = 0;
};

struct PowerGrid {
  std::string name;
  vector<Metal> metals;
  vector<Via> vias;
  bool power = 1;  // 1 is vdd, 0 is gnd
};

struct layoutAS {
  int width = 0;
  int height = 0;
  int HPWL = -1, HPWL_extend = -1;
  double HPWL_norm = -1;
  double area_norm = -1;
  double constraint_penalty = -1;
  double cost = -1;
  string gdsFile = "";
  vector<blockComplex> Blocks;
  vector<net> Nets;
  vector<terminal> Terminals;
  point LL;
  point UR;
  vector<PowerNet> PowerNets;
  vector<GuardRing> GuardRings;
  // vector<pin> blockPins;
  // vector<contact> interMetals;
  // vector<Via> interVias;
};

struct GuardRing {
  std::string mastername = "";
  string gdsFile = "guard_ring.gds";
  point LL;
  point UR;
  point center;
  vector<pin> blockPins;
  vector<contact> interMetals;
  vector<Via> interVias;
};

struct hierNode {
  bool isCompleted = false;
  bool isTop = false;
  bool isIntelGcellGlobalRouter = false;
  bool isFirstILP = false;  // donghao add
  int width = 0;
  int height = 0;
  point LL;                 // hiernode absolute LL in topnode coordinate
  point UR;                 // hiernode absolute UR in topnode coordinate
  PnRDB::Omark abs_orient;  // hiernode absolute orient in topnode coordinate
  int n_copy = 0;           // number of hiernodes of the same type used in the whole design
  int numPlacement = 0;
  string name = "";
  string concrete_name = "";
  string gdsFile = "";
  vector<int> parent;
  vector<blockComplex> Blocks;
  map<string, int> Block_name_map;  // map from block name to block index
  vector<tile> tiles_total;
  vector<net> Nets;
  vector<terminal> Terminals;

  // added by yg for power net part
  PowerGrid Vdd;
  PowerGrid Gnd;
  vector<PowerNet> PowerNets;
  // added by yg
  vector<GuardRing> GuardRings;

  // Updated
  vector<pin> blockPins;        // need
  vector<contact> interMetals;  // need
  vector<Via> interVias;        // need

  vector<layoutAS> PnRAS;

  // Member variables for constratins
  vector<SymmNet> SNets;
  vector<SymmPairBlock> SPBlocks;
  // vector<SymmBlock> SBlocks;
  vector<Preplace> Preplace_blocks;
  vector<Alignment> Alignment_blocks;
  vector<AlignBlock> Align_blocks;  // align constrainst
  vector<Abument> Abument_blocks;
  vector<MatchBlock> Match_blocks;
  vector<CCCap> CC_Caps;
  vector<R_const> R_Constraints;
  vector<C_const> C_Constraints;
  vector<PortPos> Port_Location;
  vector<Guardring_Const> Guardring_Consts;
  vector<LinearConst> L_Constraints;
  vector<Multi_LinearConst> ML_Constraints;
  vector<pair<vector<int>, Smark>> Ordering_Constraints;
  vector<pair<vector<int>, Smark>> Abut_Constraints;
  vector<set<int>> Same_Template_Constraints;
  int bias_Hgraph = 0;
  int bias_Vgraph = 0;
  double Aspect_Ratio_weight = 1000;
  double Aspect_Ratio[2] = {0, 100};
  double placement_box[2] = {-1, -1};
  vector<Router_report> router_report;
  vector<Multi_connection> Multi_connections;
  int placement_id = 0;
  int HPWL = -1, HPWL_extend = -1, HPWL_extend_wo_terminal = -1;
  double area_norm = -1;
  double HPWL_norm = -1;
  double constraint_penalty = -1;
  double cost = -1;
  std::string compact_style = "left";
};  // structure of vertex in heirarchical tree

/// Part 3: declaration of structures for constraint data

struct SymmNet {
  net net1, net2;
  int iter1, iter2;  // iterator to the list of real nets
  Smark axis_dir = PnRDB::V;
};

// struct SymmBlock {
//  vector< pair<int,int> > sympair;
//  vector< pair<int,Smark> > selfsym;
//  int dnode;
//};

struct SymmPairBlock {
  vector<pair<int, int>> sympair;
  vector<pair<int, Smark>> selfsym;
  Smark axis_dir = PnRDB::V;
};

struct Preplace {
  int blockid1;
  int blockid2;
  string conner;
  int distance;
  int horizon;  // 1 is h, 0 is v.
};

struct Alignment {
  int blockid1;
  int blockid2;
  int distance;
  int horizon;  // 1 is h, 0 is v.
};

struct Abument {
  int blockid1;
  int blockid2;
  int distance;
  int horizon;  // 1 is h, 0 is v.
};

struct MatchBlock {
  int blockid1;
  int blockid2;
  // int distance;
  // int horizon; // 1 is h, 0 is v.
};

struct AlignBlock {
  std::vector<int> blocks;  // LL.x/LL.y equal
  int horizon;              // 1 is h, 0 is v.
  int line;                 // 0 is left or bottom, 1 is center, 2 is right or top
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
  bool dummy_flag = 1;
};

struct Guardring_Const {
  string block_name;
  string guard_ring_primitives;
  string global_pin;
};

struct R_const {
  string net_name;
  // vector<string> start_pin;
  // vector<string> end_pin;
  std::vector<std::pair<int, int>> start_pin;  // pair.first blocks id pair.second pin id
  std::vector<std::pair<int, int>> end_pin;    // if pair.frist blocks id = -1 then it's terminal
  vector<double> R;
};

struct LinearConst {
  string net_name;
  // vector<string> start_pin;
  // vector<string> end_pin;
  std::vector<std::pair<int, int>> pins;  // pair.first blocks id pair.second pin id
  std::vector<double> alpha;
  double upperBound;
  double lowerBound;
};

struct Multi_LinearConst {
  std::vector<LinearConst> Multi_linearConst;
  double upperBound;
  double lowerBound;
};

struct C_const {
  string net_name;
  // vector<string> start_pin;
  // vector<string> end_pin;
  std::vector<std::pair<int, int>> start_pin;  // pair.first blocks id pair.second pin id
  std::vector<std::pair<int, int>> end_pin;    // if pair.frist blocks id = -1 then it's terminal
  vector<double> C;
};

struct Multi_connection {
  string net_name;
  int multi_number = 1;
};

/// Part 4: declaration of structures for LEF data
struct lefMacro {
  int width = 0, height = 0;
  string name = "";
  vector<pin> macroPins;
  vector<contact> interMetals;
  vector<Via> interVias;
  string master = "";
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
  int ViaIdx, LowerIdx, UpperIdx;                    // lower metal idx and upper metal idx
  std::vector<point> ViaRect, LowerRect, UpperRect;  // LL and UR of Via, center is (0,0), LowerRect and UpperRect are Rects considering enclosure
  double R;
};

struct GdsDatatype {
  int Draw = 0;
  int Pin = 0;
  int Label = 0;
  int Blockage = 0;
};

struct metal_info {
  string name;
  int layerNo;
  int width;    // from minwidth MinWidth["M1"]
  int dist_ss;  // side to side distance  from SpaceNumTem found the minimim one SpaceNumTem["M1"]
  int direct;   // direction, 1 is H, 0 is V  added it by your self
  int grid_unit_x;
  int grid_unit_y;
  int minL;
  int maxL;
  int dist_ee;
  double unit_R;
  double unit_C;
  double unit_CC;
  GdsDatatype gds_datatype;
};

struct via_info {
  string name;
  int layerNo;
  int lower_metal_index;
  int upper_metal_index;
  int width;    // drData.MinWidth["V6"], X direction width
  int width_y;  // Y direction width
  int cover_l;  // the length that the via should be coverage   EnMax["V4M5"] EnMax["V4M4"]
  int cover_l_P;
  int cover_u;
  int cover_u_P;
  int dist_ss;    // via spacing, X direction spacing
  int dist_ss_y;  // Y direction spacing
  double R;
  GdsDatatype gds_datatype;
};

struct Boundary {
  string name = "Boundary";
  int layerNo = 0;
  GdsDatatype gds_datatype;
};

struct guardring_info {
  string name;
  int xspace;  // x dimension minimal space
  int yspace;  // y dimension minimal space
  GdsDatatype gds_datatype;
  string path;
};

struct design_info {
  int Hspace = 0, Vspace = 0;  // global Hspace and Vspace in placement
  int signal_routing_metal_l;
  int signal_routing_metal_u;
  int power_grid_metal_l;
  int power_grid_metal_u;
  int power_routing_metal_l;
  int power_routing_metal_u;
  int h_skip_factor;
  int v_skip_factor;
  std::string compact_style = "left";
};

struct Drc_info {
  int MaxLayer;                       // index
  map<string, int> Metalmap, Viamap;  // map from metal/via's name(M1, M2, V1...) to metal/via's index in the below vectors
  vector<metal_info> Metal_info;      // metal info read from layers.json
  vector<via_info> Via_info;          // via info read from layers.json
  vector<int> metal_weight;           // initially all set to 1 in ReadDesignRuleJson.cpp
  vector<ViaModel> Via_model;
  vector<string> MaskID_Metal;  // str type LayerNo of each Layer
  vector<string> MaskID_Via;
  Boundary top_boundary;
  guardring_info Guardring_info;  // guardring info read from layers.json
  design_info Design_info;        // design ingo from layer.json
};

struct routing_net {
  string net_name;
  vector<string> pin_name;
  vector<int> pin_access;
};

struct Router_report {
  string node_name;
  vector<routing_net> routed_net;
};

}  // namespace PnRDB

#endif
