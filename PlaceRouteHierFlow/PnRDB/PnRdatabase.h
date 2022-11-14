#ifndef PNRDATABASE_H_
#define PNRDATABASE_H_

#include <limits.h>
#include <stdlib.h>

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <ctime>
#include <fstream>  // std::ifstream
#include <iostream>
#include <map>
#include <queue>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>  // pair, make_pair
#include <vector>
#ifdef WINDOWS
#include <Windows.h>  // getcwd
#else
#include <unistd.h>  // getcwd
#endif
#include <nlohmann/json.hpp>
#include <set>

#include "Lexer.h"
#include "datatype.h"
#include "readfile.h"
#include "spdlog/spdlog.h"

using std::cerr;
using std::cout;
using std::deque;
using std::endl;
using std::ifstream;
using std::istream;
using std::map;
using std::max_element;
using std::ostream;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::unordered_map;
using std::vector;

using namespace nlohmann;
class PnRdatabase;

class PnRdatabase {
  private:
  int maxNode;
  int unitScale;

  public:
  map<string, vector<PnRDB::lefMacro>> lefData;  // map from Macro name to Macro Instance
  map<string, vector<string>> gdsData2;          // map from gds name to multiple gds file (abstract to multiple concrete)
  private:
  PnRDB::designRule drData;

  void UpdateHierNodeParent(int nodeID);                            // update parent node of current node
  void TraverseDFS(deque<int> &Q, vector<string> &color, int idx);  // DFS subfunc to traverse hierarchical tree

  public:
  // Not implemented
  PnRdatabase(const PnRdatabase &other);             // copy constructor
  PnRdatabase &operator=(const PnRdatabase &other);  // copy assignment function

  public:
  int topidx;
  bool use_external_placement_info = false;
  PnRDB::Drc_info DRC_info;
  vector<PnRDB::hierNode> hierTree;  // each module in verilog file is a node
  int ScaleFactor = 1;

  // default constructor
  inline PnRdatabase() {
    unitScale = 2000;
    maxNode = 0;
  };
  // destructor
  ~PnRdatabase();

  int get_unitScale() const { return unitScale; }
  int get_maxNode() const { return maxNode; }

  void ReadPDKJSON(string drfile);
  void semantic0(const string &topcell);
  void semantic1(const vector<tuple<string, string, string>> &global_signals);
  void semantic2();

  deque<int> TraverseHierTree();  // traverse hierarchical tree in topological order

  PnRDB::hierNode CheckoutHierNode(int nodeID, int sel = -1);            // check out data of specific hierarchical node
  void AppendToHierTree(const PnRDB::hierNode &updatedNode);             // append node to end of hierTree
  void CheckinHierNode(int nodeID, const PnRDB::hierNode &updatedNode);  // check out data of specific hierarchical node
  std::vector<int> UsedInstancesIdx(int nodeID);                         // indices of used instances of a hiernode
  void CheckinChildnodetoBlock(PnRDB::hierNode &parent, int blockID, const PnRDB::hierNode &updatedNode, PnRDB::Omark ort);
  void updatePowerPins(PnRDB::pin &temp_pin);

  // these functions are used to transform internal info of nodes
  void TransformNode(PnRDB::hierNode &updatedNode, PnRDB::point translate, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformTerminal(PnRDB::terminal &terminal, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformTerminals(std::vector<PnRDB::terminal> &terminals, PnRDB::point translate, int width, int height, PnRDB::Omark ort,
                          PnRDB::TransformType tranform_type);
  void TransformBlockComplex(PnRDB::blockComplex &bc, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformBlockComplexs(std::vector<PnRDB::blockComplex> &bcs, PnRDB::point translate, int width, int height, PnRDB::Omark ort,
                              PnRDB::TransformType tranform_type);
  void TransformBlock(PnRDB::block &block, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformBlocks(std::vector<PnRDB::block> &blocks, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformPoint(PnRDB::point &point, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformPoints(std::vector<PnRDB::point> &points, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformBbox(PnRDB::bbox &bbox, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformContact(PnRDB::contact &contact, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformContacts(std::vector<PnRDB::contact> &contacts, PnRDB::point translate, int width, int height, PnRDB::Omark ort,
                         PnRDB::TransformType tranform_type);
  void TransformVia(PnRDB::Via &via, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformVias(std::vector<PnRDB::Via> &vias, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformGuardring(PnRDB::GuardRing &guardring, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformGuardrings(std::vector<PnRDB::GuardRing> &guardrings, PnRDB::point translate, int width, int height, PnRDB::Omark ort,
                           PnRDB::TransformType tranform_type);
  void TransformPin(PnRDB::pin &pin, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformPins(std::vector<PnRDB::pin> &pins, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformMetal(PnRDB::Metal &metal, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformMetals(std::vector<PnRDB::Metal> &metals, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformNet(PnRDB::net &net, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformNets(std::vector<PnRDB::net> &nets, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
  void TransformBlockPinsOriginToPlaced(std::vector<PnRDB::pin> &blockPins, PnRDB::point translate, int width, int height, PnRDB::Omark ort);
  void TransformIntermetalsOriginToPlaced(std::vector<PnRDB::contact> &interMetals, PnRDB::point translate, int width, int height, PnRDB::Omark ort);
  void TransformInterviasOriginToPlaced(std::vector<PnRDB::Via> &interVias, PnRDB::point translate, int width, int height, PnRDB::Omark ort);
  PnRDB::Omark RelOrt2AbsOrt(PnRDB::Omark current_node_ort, PnRDB::Omark childnode_ort);
  void ExtractPinsToPowerPins(PnRDB::hierNode &updatedNode);

  void _ReadLEF(istream &fin, const string &leffile);  // read building block data from LEF stream
  bool ReadLEF(const string &leffile);                 // read building block data from LEF file
  bool ReadLEFFromString(const string &lefString);
  void PrintLEFData();  // print LEF data for debugging
  map<string, vector<PnRDB::lefMacro>> checkoutlef() { return lefData; };
  void ReadConstraint_Json(PnRDB::hierNode &node, const string &jsonStr);
  void ReadPrimitiveOffsetPitch(vector<PnRDB::lefMacro> &primitive, const string &jsonStr);
  bool MergeLEFMapData(PnRDB::hierNode &node);
  void PrintHierTree();

  PnRDB::designRule getDesignRule() const { return drData; }
  PnRDB::Drc_info getDrc_info() const { return DRC_info; }

  // Interface for detail router II - wbxu
  void PrintDesignRuleData();
  string WriteJSON(PnRDB::hierNode &node, bool includeBlock, bool includeNet, bool includePowerNet, bool includePowerGrid, const string &gdsName,
                   const PnRDB::Drc_info &drc_info, const string &opath);
  void WriteJSON_Routability_Analysis(PnRDB::hierNode &node, const string &opath, PnRDB::Drc_info &drc_info);
  void PrintHierNode(PnRDB::hierNode &node);
  void PrintContact(PnRDB::contact &cont);
  void PrintVia(PnRDB::Via &v);
  void PrintMetal(PnRDB::Metal &m);
  void PrintBlock(PnRDB::blockComplex &bc);
  void PrintNet(PnRDB::net &n);
  void PrintTerminal(PnRDB::terminal &t);
  void PrintBlockPin(PnRDB::pin &p);
  void PrintSymmNet(PnRDB::SymmNet &t);
  void AddingPowerPins(PnRDB::hierNode &node);
  void Extract_RemovePowerPins(PnRDB::hierNode &node);
  map<string, PnRDB::lefMacro> checkoutSingleLEF();
  json WriteGcellGlobalRouteFile(const PnRDB::hierNode &node, const string &rofile, const string &opath, const int MetalIdx, const string net_name,
                                 const int width, const int first_tile_idx, const int last_tile_idx, std::vector<int> &tile_idxs, const int MetalDirection,
                                 const int net_id) const;
  void WriteGcellGlobalRoute(const PnRDB::hierNode &node, const string &rofile, const string &opath) const;
  void WriteLef(const PnRDB::hierNode &node, const string &file, const string &opath) const;
  void Write_Router_Report(PnRDB::hierNode &node, const string &opath);
  void Write_Power_Mesh_Conf(std::string outputfile);
  void Write_Current_Workload(PnRDB::hierNode &node, double total_current, int current_number, std::string outputfile);
  PnRDB::Metal Find_Top_Middle_Metal(PnRDB::hierNode &node, const PnRDB::Drc_info &drc_info, int index);
};

#endif
