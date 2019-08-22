#ifndef PNRDATABASE_H_
#define PNRDATABASE_H_

#include <ctime>
#include <map>
#include <unordered_map>
#include <vector>
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
#include <unistd.h>
#include <set>
#include "datatype.h"
#include "readfile.h"
#include <nlohmann/json.hpp>
#include "Lexer.h"

using std::map;
using std::unordered_map;
using std::vector;
using std::queue;
using std::string;
using std::cout;
using std::endl;
using std::pair;
using std::cerr;
using std::ifstream;
using std::istream;
using std::ostream;
using std::max_element;

class PnRdatabase;

class ReadVerilogHelper {


    PnRDB::blockComplex temp_blockComplex,clear_blockComplex;

    PnRDB::hierNode temp_node,clear_node;
    PnRDB::hierNode Supply_node;

    PnRdatabase& db;

public:

    PnRdatabase& get_db() const {
      return db;
    }

    ReadVerilogHelper( PnRdatabase& db_in) : db(db_in) {
      // Why do we add one to begin with?
	clear_blockComplex.instance.resize(1);
	temp_blockComplex = clear_blockComplex;
    }

    void operator()(istream& fin, const string& fpath, const string& topcell);

    void parse_module( Lexer& l, bool celldefine_mode=false);

    void parse_top( istream& fin);

    void gen_terminal_map( unordered_map<string,int>& terminal_map);

    int process_connection( int iter, const string& net_name,
			    unordered_map<string,int>& net_map);
    void semantic( const string& fpath, const string& topcell);
};


class PnRdatabase
{
  private:
    int maxNode;
    int unitScale;
    map<string, std::vector<PnRDB::lefMacro> > lefData;
    map<string, string> gdsData;
    PnRDB::designRule drData;

    void UpdateHierNodeParent(int nodeID); // update parent node of current node
    void TraverseDFS(queue<int>& Q, vector<string>& color, int idx); // DFS subfunc to traverse hierarchical tree 

    bool ReadPDKJSON(std::string drfile);

    // Not implemented
    PnRdatabase(const PnRdatabase& other); // copy constructor
    PnRdatabase& operator= (const PnRdatabase& other); // copy assignment function

  public:
    int topidx;
    PnRDB::Drc_info DRC_info;
    vector<PnRDB::hierNode> hierTree;

    // default constructor
    inline PnRdatabase() {unitScale=2000;maxNode=0;};
    // constructor with augments
    PnRdatabase(string path, string topcell, string vname, string lefname, string mapname, string drname);
    // destructor
    ~PnRdatabase() {}

    int get_unitScale() const { return unitScale; }
    int get_maxNode() const { return maxNode; }

    long int get_number(string str);

    queue<int> TraverseHierTree(); // traverse hierarchical tree in topological order
    PnRDB::hierNode CheckoutHierNode(int nodeID); // check out data of specific hierarchical node
    void CheckinHierNode(int nodeID, const PnRDB::hierNode& updatedNode); // check out data of specific hierarchical node
    void updatePowerPins(PnRDB::pin& temp_pin);
   
    void ReadVerilog(istream& inps, const string& fpath, const string& topcell);
    bool ReadVerilog(const string& fpath, const string& vname, const string& topcell);

    bool ReadLEF(string leffile); // read building block data from LEF file
    void PrintLEFData();  // print LEF data for debugging
    map<string, std::vector<PnRDB::lefMacro> > checkoutlef(){return lefData;};
    bool ReadConstraint(PnRDB::hierNode& node, string fpath, string suffix);
    bool MergeLEFMapData(PnRDB::hierNode& node);
    void PrintHierTree();
    bool ReadMap(string fpath, string mapname); // read gds data from map file
    bool ReadDesignRule(string drfile); //  read design rule data from design rule file
    bool HardDesignRule(); // hard-code design rules

    PnRDB::designRule getDesignRule() const { return drData;}
    PnRDB::Drc_info getDrc_info() const {return DRC_info;}

    bool ReadDesignRule_metal(string metal_name, vector<string>& jason_file, int& index, string &def, PnRDB::metal_info& temp_metal_info);
    bool ReadDesignRule_via(string via_name, vector<string>& jason_file, int& index, string &def, PnRDB::via_info& temp_via_info);
    bool ReadDesignRule_jason(string drfile);

    // Interface for detail router II - wbxu
    void WritePlaceRoute(PnRDB::hierNode& node, string pofile, string rofile);
    void PrintDesignRuleData();
    std::string WriteJSON (PnRDB::hierNode& node, bool includeBlock, bool includeNet, bool includePowerNet, bool includePowerGrid, std::string gdsName, PnRDB::Drc_info& drc_info, string opath);
    void PrintHierNode(PnRDB::hierNode& node);
    void PrintContact(PnRDB::contact& cont);
    void PrintVia(PnRDB::Via& v);
    void PrintMetal(PnRDB::Metal& m);
    void PrintBlock(PnRDB::blockComplex& bc);
    void PrintNet(PnRDB::net& n);
    void PrintTerminal(PnRDB::terminal& t);
    void PrintBlockPin(PnRDB::pin& p);
    void PrintSymmNet(PnRDB::SymmNet& t);
    void AddingPowerPins(PnRDB::hierNode &node);
    void Extract_RemovePowerPins(PnRDB::hierNode &node);
    std::map<string, PnRDB::lefMacro> checkoutSingleLEF();
    void WriteGlobalRoute(PnRDB::hierNode& node, string rofile, string opath);
    bool WriteLef(PnRDB::hierNode &node, string file, string opath);
    
};

#endif
