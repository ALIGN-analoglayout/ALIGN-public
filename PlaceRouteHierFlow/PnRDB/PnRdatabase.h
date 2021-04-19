#ifndef PNRDATABASE_H_
#define PNRDATABASE_H_

#include <ctime>
#include <map>
#include <unordered_map>
#include <vector>
#include <tuple>
#include <queue>
#include <string>
#include <limits.h>
#include <cstdlib>
#include <cctype>
#include <iostream>
#include <fstream> // std::ifstream
#include <stdlib.h>
#include <utility> // pair, make_pair
#include <algorithm>
#include <sstream>
#ifdef WINDOWS
#include <Windows.h> // getcwd
#else
#include <unistd.h> // getcwd
#endif
#include <set>
#include "datatype.h"
#include "readfile.h"
#include <nlohmann/json.hpp>
#include "Lexer.h"
#include "spdlog/spdlog.h"

using std::map;
using std::unordered_map;
using std::vector;
using std::deque;
using std::string;
using std::cout;
using std::endl;
using std::pair;
using std::tuple;
using std::cerr;
using std::ifstream;
using std::istream;
using std::ostream;
using std::max_element;

using namespace nlohmann;
class PnRdatabase;

class ReadVerilogHelper {
    PnRDB::hierNode temp_node;
    vector<tuple<string,string,string> > global_signals;
    PnRdatabase& db;

public:

    PnRdatabase& get_db() {
      return db;
    }

    const vector<tuple<string,string,string> >& get_global_signals() const {
      return global_signals;
    }

    ReadVerilogHelper( PnRdatabase& db_in) : db(db_in) {}

    void parse_module( Lexer& l, bool celldefine_mode=false);

    void parse_top( istream& fin);

    void gen_terminal_map( unordered_map<string,int>& terminal_map);

    int process_connection( int iter, const string& net_name,
			    unordered_map<string,int>& net_map);
};


class PnRdatabase
{
  private:
    int maxNode;
    int unitScale;
    map<string, vector<PnRDB::lefMacro> > lefData, _lefDataWoTap;  //map from Macro name to Macro Instance
  public:
    map<string, string> gdsData; //map from gds name to gds file
    map<string, string> _gdsDataWoTap; //map from gds name to gds file
  private:
    PnRDB::designRule drData;

    void UpdateHierNodeParent(int nodeID); // update parent node of current node
    void TraverseDFS(deque<int>& Q, vector<string>& color, int idx); // DFS subfunc to traverse hierarchical tree 

 public: 
    // Not implemented
    PnRdatabase(const PnRdatabase& other); // copy constructor
    PnRdatabase& operator= (const PnRdatabase& other); // copy assignment function

  public:
    int topidx;
    PnRDB::Drc_info DRC_info;
    vector<PnRDB::hierNode> hierTree;  //each module in verilog file is a node

    // default constructor
    inline PnRdatabase() {unitScale=2000;maxNode=0;};
    // destructor
    ~PnRdatabase();

    int get_unitScale() const { return unitScale; }
    int get_maxNode() const { return maxNode; }

    void ReadPDKJSON(string drfile);
    void semantic0( const string& topcell);
    void semantic1( const vector<tuple<string,string,string> >& global_signals);
    void semantic2();

    deque<int> TraverseHierTree(); // traverse hierarchical tree in topological order

    PnRDB::hierNode CheckoutHierNode(int nodeID, int sel = -1); // check out data of specific hierarchical node
    std::vector<PnRDB::hierNode> CheckoutHierNodeVec(int nodeID);//checkout nodeVec, which consists of different placement
    void AppendToHierTree( const PnRDB::hierNode& updatedNode); // append node to end of hierTree
    void CheckinHierNode(int nodeID, const PnRDB::hierNode& updatedNode); // check out data of specific hierarchical node
    void CheckinChildnodetoBlock(PnRDB::hierNode &parent, int blockID, const PnRDB::hierNode &updatedNode);
    void updatePowerPins(PnRDB::pin &temp_pin);

    //these functions are used to transform internal info of nodes
    void TransformNode(PnRDB::hierNode& updatedNode, PnRDB::point translate, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformTerminal(PnRDB::terminal &terminal, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformTerminals(std::vector<PnRDB::terminal> &terminals, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformBlockComplex(PnRDB::blockComplex &bc, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformBlockComplexs(std::vector<PnRDB::blockComplex> &bcs, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformBlock(PnRDB::block &block, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformBlocks(std::vector<PnRDB::block> &blocks, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformPoint(PnRDB::point &point, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformPoints(std::vector<PnRDB::point> &points, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformBbox(PnRDB::bbox &bbox, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformBboxs(std::vector<PnRDB::bbox> &bboxs, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformContact(PnRDB::contact &contact, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformContacts(std::vector<PnRDB::contact> &contacts, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformVia(PnRDB::Via &via, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformVias(std::vector<PnRDB::Via> &vias, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformGuardring(PnRDB::GuardRing &guardring, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformGuardrings(std::vector<PnRDB::GuardRing> &guardrings, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformPin(PnRDB::pin &pin, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformPins(std::vector<PnRDB::pin> &pins, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformMetal(PnRDB::Metal &metal, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformMetals(std::vector<PnRDB::Metal> &metals, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformNet(PnRDB::net &net, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TransformNets(std::vector<PnRDB::net> &nets, PnRDB::point translate, int width, int height, PnRDB::Omark ort, PnRDB::TransformType tranform_type);
    void TranslateNode(PnRDB::hierNode& updatedNode, PnRDB::point translate);
    void TransformBlockPinsOriginToPlaced(std::vector<PnRDB::pin> &blockPins, PnRDB::point translate, int width, int height, PnRDB::Omark ort);
    void TransformIntermetalsOriginToPlaced(std::vector<PnRDB::contact> &interMetals, PnRDB::point translate, int width, int height, PnRDB::Omark ort);
    void TransformInterviasOriginToPlaced(std::vector<PnRDB::Via>& interVias, PnRDB::point translate, int width, int height, PnRDB::Omark ort);
    PnRDB::Omark RelOrt2AbsOrt(PnRDB::Omark current_node_ort, PnRDB::Omark childnode_ort);
    void ExtractPinsToPowerPins(PnRDB::hierNode &updatedNode);

    vector<tuple<string,string,string> > ReadVerilog(const string &fpath, const string &vname, const string &topcell);

    bool ReadLEF(const string& leffile, bool wtap = true); // read building block data from LEF file
    void PrintLEFData();          // print LEF data for debugging
    map<string, vector<PnRDB::lefMacro>> checkoutlef() { return lefData; };
    void ReadConstraint_Json(PnRDB::hierNode &node, const string& jsonStr);
    bool MergeLEFMapData(PnRDB::hierNode &node);
    void PrintHierTree();

    PnRDB::designRule getDesignRule() const { return drData; }
    PnRDB::Drc_info getDrc_info() const { return DRC_info; }

    // Interface for detail router II - wbxu
    void WritePlaceRoute(PnRDB::hierNode &node, string pofile, string rofile);
    void PrintDesignRuleData();
    void ReadDBJSON(PnRDB::hierNode &node, const string &filename) const;
    void WriteDBJSON(const PnRDB::hierNode &node, const string &filename) const;
    string WriteJSON(PnRDB::hierNode &node, bool includeBlock, bool includeNet, bool includePowerNet, bool includePowerGrid, const string &gdsName, const PnRDB::Drc_info &drc_info, const string &opath);
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
    json WriteGcellGlobalRouteFile(const PnRDB::hierNode &node, const string &rofile, const string &opath,
                                   const int MetalIdx, const string net_name, const int width,
                                   const int first_tile_idx, const int last_tile_idx,
                                   std::vector<int> &tile_idxs, const int MetalDirection, const int net_id) const;
    void WriteGlobalRoute(const PnRDB::hierNode &node, const string &rofile, const string &opath) const;
    void WriteGcellGlobalRoute(const PnRDB::hierNode &node, const string &rofile, const string &opath) const;
    void WriteLef(const PnRDB::hierNode &node, const string &file, const string &opath) const;
    void Write_Router_Report(PnRDB::hierNode &node, const string &opath);
    void Write_Power_Mesh_Conf(std::string outputfile);
    void Write_Current_Workload(PnRDB::hierNode &node, double total_current, int current_number, std::string outputfile);
    void WriteGcellDetailRoute(const PnRDB::hierNode& node, const string& rofile, const string& opath) const;
    
};

#endif
