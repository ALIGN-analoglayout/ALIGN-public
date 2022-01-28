#ifndef CAPPLACER_h_
#define CAPPLACER_h_

#include <limits.h>
#include <math.h>
#include <stdlib.h>

#include <algorithm>
#include <bitset>
#include <cctype>
#include <cmath>
#include <cstdlib>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>
#ifdef WINDOWS
#include <Windows.h>  // getcwd
#else
#include <unistd.h>  // getcwd
#endif
#include <fstream>
#include <iostream>
#include <sstream>

#include "../PnRDB/datatype.h"

extern "C" {
#include <stdio.h>
}

using std::cerr;
using std::cout;
using std::endl;
using std::iostream;
using std::make_pair;
using std::ofstream;
using std::pair;
using std::string;
using std::vector;

struct point {
  int x = 0;
  int y = 0;
};  // structure of integer coordinate

struct bbox {
  vector<point> polygon;  // list of coordinates of polygon
  point LL, LR, UL, UR;
};

struct contact {
  string metal = "";
  bbox originBox;
  bbox placedBox;
  point originCenter;
  point placedCenter;
};

struct terminal {
  string name = "";
  string type = "";  // add by yg //////////////////////////////////////
  int netIter = -1;
  vector<contact> termContacts;
};

class Pin {
  public:
  string pinName;
  vector<contact> pinContacts;
  int netIter;
};

class Placer_Router_Cap {
  private:
  PnRDB::block CheckOutBlock;
  int offset_x;
  int offset_y;
  PnRDB::point offset;
  struct cap {
    double index_x;
    double index_y;
    PnRDB::point pos;
    int net_index;
    int access;
    // int line_accessed;
  };

  vector<int> metal_width;
  vector<int> metal_direct;  // 1 is h, 0 is v
  vector<int> metal_distance_ss;
  PnRDB::point shifting;
  PnRDB::point min_dis;
  ;
  vector<cap> Caps;
  PnRDB::point unit_cap_dim;
  PnRDB::point span_dist;

  vector<pair<int, int> > cap_pair_sequence;
  vector<pair<int, int> > net_sequence;
  vector<int> num_router_net_v;
  vector<int> num_router_net_h;
  struct connection_set {
    vector<int> cap_index;
  };
  struct net {
    string name = "";
    vector<int> cap_index;
    vector<PnRDB::point> start_connection_pos;
    vector<PnRDB::point> end_connection_pos;
    vector<int> Is_pin;  // 0 not pin, 1 pin
    vector<string> metal;
    vector<PnRDB::point> via_pos;
    vector<string> via_metal;
    vector<connection_set> Set;
    vector<connection_set> router_line_v;
    vector<connection_set> router_line_h;
    vector<connection_set> half_router_line_v;
    vector<connection_set> half_router_line_h;
    vector<int> routable_line_v;
    vector<int> routable_line_h;
    vector<int> line_v;
    vector<int> line_h;
  };
  vector<net> Nets_pos;
  vector<net> Nets_neg;

  Placer_Router_Cap();                          // no default constructor
  Placer_Router_Cap(const Placer_Router_Cap&);  // no copy constructor

  void GetPhysicalInfo_merged_net(vector<net>& n_array, vector<int>& trails, const PnRDB::Drc_info& drc_info, const string& H_metal, const string& V_metal,
                                  const string& HV_via_metal, int HV_via_metal_index, int grid_offset, int sign);

  void GetPhysicalInfo_common_net(vector<net>& n_array, vector<int>& trails, const PnRDB::Drc_info& drc_info, const string& H_metal, const string& V_metal,
                                  const string& HV_via_metal, int HV_via_metal_index, int grid_offset, int sign);

  public:
  void Placer_Router_Cap_clean();
  void Placer_Router_Cap_function(vector<int>& ki, vector<pair<string, string> >& cap_pin, const string& fpath, const string& unit_capacitor,
                                  const string& final_gds, bool cap_ratio, int cap_r, int cap_s, const PnRDB::Drc_info& drc_info,
                                  const map<string, PnRDB::lefMacro>& lefData, bool dummy_flag, const string& opath);
  Placer_Router_Cap(const string& opath, const string& fpath, PnRDB::hierNode& current_node, PnRDB::Drc_info& drc_info,
                    const map<string, PnRDB::lefMacro>& lefData, bool aspect_ratio, int num_aspect);

  void initial_net_pair_sequence(vector<int>& ki, vector<pair<string, string> >& cap_pin);
  void perturbation_pair_sequence();
  void Placer_Cap(vector<int>& ki);
  void Router_Cap(vector<int>& ki, vector<pair<string, string> >& cap_pin, bool dummy_flag, bool cap_ratio, int cap_r, int cap_s);
  void PrintPlacer_Router_Cap(string outfile);
  void GetPhysicalInfo_router(const string& H_metal, int H_metal_index, const string& V_metal, int V_metal_index, const PnRDB::Drc_info& drc_info);
  void cal_offset(const PnRDB::Drc_info& drc_info, int H_metal, int V_metal, int HV_via_index);
  PnRDB::bbox fillPathBBox(const PnRDB::point& start, const PnRDB::point& end, int width);
  /* void fillPathBoundingBox (int *x, int* y, */
  /* 			      const pair<double,double> &start, */
  /* 			      const pair<double,double> &end, */
  /* 			      double width); */
  void ExtractData(const string& fpath, const string& unit_capacitor, const string& final_gds, const PnRDB::lefMacro& uc, const PnRDB::Drc_info& drc_info,
                   int H_metal, int V_metal, int HV_via_metal_index, const string& opath);
  void WriteGDSJSON(const string& fpath, const string& unit_capacitor, const string& final_gds, const PnRDB::Drc_info& drc_info, const string& opath);

  void WriteViewerJSON(const string& fpath, const string& unit_capacitor, const string& final_gds, const PnRDB::Drc_info& drc_info, const string& opath);

  PnRDB::block CheckoutData(void) { return CheckOutBlock; };
  void found_neighbor(int j, net& pos, connection_set& temp_set);
  void Common_centroid_capacitor_aspect_ratio(const string& opath, const string& fpath, PnRDB::hierNode& current_node, PnRDB::Drc_info& drc_info,
                                              const map<string, PnRDB::lefMacro>& lefData, bool aspect_ratio, int num_aspect);
  void addVia(net& temp_net, pair<double, double>& coord, const PnRDB::Drc_info& drc_info, const string& HV_via_metal, int HV_via_metal_index, int isPin);
  void addVia(net& temp_net, PnRDB::point& pt, const PnRDB::Drc_info& drc_info, const string& HV_via_metal, int HV_via_metal_index, int isPin);
  void addVia_extend_metal(net& temp_net, PnRDB::point& coord_pos, const PnRDB::Drc_info& drc_info, const string& HV_via_metal, int HV_via_metal_index, int isPin);

  void WriteLef(const PnRDB::block& temp_block, const string& file, const string& opath);
  void check_grid(const net& n) const;
};

#endif
