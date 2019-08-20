#ifndef PNRDATABASE_H_
#define PNRDATABASE_H_

#include <ctime>
#include <map>
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

using std::map;
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

enum class TokenType { EndOfFile=0, EndOfLine=1, STRING=2, Undefined=3, COMMA=',', LPAREN='(', RPAREN=')',
    SEMICOLON=';', PERIOD='.'};

/*
override ostream& operator<<( ostream& os, const TokenType& tt) {
    string str;
    if        ( tt == TokenType::EndOfFile) {
      str = "EndOfFile";
    } else if ( tt == TokenType::EndOfLine) {
      str = "EndOfLine";
    } else if ( tt == TokenType::STRING) {
      str = "STRING";
    } else {
      str = "' '";
      str[1] = static_cast<char>( tt);
    }

    os << str;
    return os;
}
*/

class Token {
public:
  TokenType tt;
  string value;
  friend ostream& operator<<( ostream& os, const Token& t) {
    os << "(" << static_cast<int>(t.tt) << "," << t.value << ")";
    return os;
  }
};


class Lexer {
    istream& s; 

    string line;
    int cursor;
    int line_num;

public:
    Token last_token;
    Token current_token;
    
    Lexer( istream& sin) : s(sin) {
      line_num = 0;
      current_token.tt = TokenType::EndOfLine;
      get_token();
    }
    
    void get_token() {
      last_token = current_token;

      if ( last_token.tt == TokenType::EndOfFile) {
	return;
      }

      current_token.value = "";
      while ( last_token.tt == TokenType::EndOfLine) {
	if ( s.peek() == EOF) {
	  current_token.tt = TokenType::EndOfFile;
	  return;
	}

	getline( s, line);
	cursor = 0;
	++line_num;

	// Check for beginning of the line comment
	if ( line.size() >= 2 && line[0] == '/' && line[1] == '/') {
	} else {
	  break;
	}
      }
	
      // Eat white space
      while ( cursor < line.size() && isspace( line[cursor])) {
	++cursor;
      }

      if ( cursor >= line.size()) {
	current_token.tt = TokenType::EndOfLine;
	return;
      }

      if ( line[cursor] == '(') {
	current_token.tt = TokenType::LPAREN;
	current_token.value.push_back( line[cursor]);
	++cursor;
      }	else if ( line[cursor] == ')') {
	current_token.tt = TokenType::RPAREN;
	current_token.value.push_back( line[cursor]);
	++cursor;
      }	else if ( line[cursor] == '.') {
	current_token.tt = TokenType::PERIOD;
	current_token.value.push_back( line[cursor]);
	++cursor;
      }	else if ( line[cursor] == ',') {
	current_token.tt = TokenType::COMMA;
	current_token.value.push_back( line[cursor]);
	++cursor;
      }	else if ( line[cursor] == ';') {
	current_token.tt = TokenType::SEMICOLON;
	current_token.value.push_back( line[cursor]);
	++cursor;
      } else if ( isalpha( line[cursor]) || line[cursor] == '_') {
	current_token.tt = TokenType::STRING;
	current_token.value.push_back( line[cursor]);
	++cursor;
	while ( cursor < line.size() &&
		(isalnum( line[cursor]) || line[cursor] == '_')) {
	  current_token.value.push_back( line[cursor]);
	  ++cursor;
	}
      } else {
	current_token.tt = TokenType::Undefined;
	current_token.value.push_back( line[cursor]);
	++cursor;
      }

    }

    bool have( TokenType tt) {
      if ( current_token.tt == tt) {
	get_token();
	return 1;
      } else {
	return 0;
      }
    }

    void mustbe( TokenType tt) {
      if ( !have( tt)) {
	std::ostringstream os;
	os << "Expected token type " << static_cast<int>(tt) << " got " << static_cast<int>(current_token.tt) << endl;
	error( os.str());
      }
    }

    bool have_keyword( const string& k) {
      if ( current_token.tt == TokenType::STRING &&
	   current_token.value == k) {
	get_token();
	return 1;
      } else {
	return 0;
      }
    }

    void mustbe_keyword( const string& k) {
      if ( !have_keyword( k)) {
	std::ostringstream os;
	os << "Expected keyword " << k << " got " << current_token;
	error( os.str());
      }
    }

    void error( const string& k) {
      cout << "Syntax error at line " << line_num << " position " << cursor << ": " << k << endl;
      assert( false);
    }

};


class ReadVerilogHelper {
public:
    string verilog_string;
    size_t found;
    vector<string> temp;
    PnRDB::blockComplex temp_blockComplex,clear_blockComplex;
    PnRDB::PowerNet temp_PowerNet, clear_PowerNet;
    PnRDB::terminal temp_terminal,clear_terminal;
    string temp_name;
    PnRDB::pin temp_pin;
    PnRDB::hierNode temp_node,clear_node;
    PnRDB::hierNode Supply_node;

    PnRdatabase& db;

    int p_temp;
    int *p;

    int in_module;
    int lock;
    int specify;

    ReadVerilogHelper( PnRdatabase& db_in) : db(db_in) {
	temp_blockComplex.instance.resize(1);
	clear_blockComplex.instance.resize(1);
	p_temp=0;
	in_module = 0;
	lock = 0;
	specify = 0;
	p=&p_temp;
    }

    void operator()(istream& fin, const string& fpath, const string& topcell);

    void per_line( const string& fpath);

    bool parse_io( const string& direction);
    bool parse_supply( const string& supply);

    void finish( const string& topcell);
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
