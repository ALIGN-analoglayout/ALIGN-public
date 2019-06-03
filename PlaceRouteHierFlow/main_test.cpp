#include <string>
#include <iostream>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/router.h"

using std::string;
using std::cout;
using std::endl;

double ConstGraph::LAMBDA=1000;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=100;
double ConstGraph::SIGMA=1000;

int main(int argc, char** argv ){
  string lfile=argv[2];
  string fpath=argv[1];
  string vfile=argv[3];
  string mfile=argv[4];
  string dfile=argv[5];
  string topcell=argv[6];
  //string lfile="sc.lef";
  //string fpath="./testcase_latest2";
  //string vfile="sc_block.v";
  //string mfile="sc.map";
  //string dfile="drcRules_calibre_asap7_Rule_Deck.rul";
  //string topcell="switched_capacitor_filter";
  //cout<<lfile<<endl<<fpath<<endl<<vfile<<endl<<mfile<<endl<<topcell<<endl;
  // Following codes try to get the path of binary codes
  string binary_directory;
  binary_directory = argv[0];
  cout <<"argv[0]: "<<binary_directory <<endl;
  int beginIdx = binary_directory.rfind('/');//find the last slash
  string str_lastOne = binary_directory.substr(beginIdx+1);
  cout <<"string after last slash: "<<str_lastOne <<endl;
  binary_directory = binary_directory.erase(beginIdx+1);
  cout <<"binary_directory: "<< binary_directory <<endl;

  PnRdatabase DB(fpath, topcell, vfile, lfile, mfile, dfile); // construction of database
  PnRDB::hierNode current_node=DB.CheckoutHierNode(0); // check out a hierarchical node from database

  // Placement
  Placer curr_plc(current_node); // do placement and update data in current node

  // Routing
  PnRDB::designRule design_rule=DB.getDesignRule(); 
  Router curr_route(current_node, design_rule, binary_directory);
  
    // Update node
  DB.CheckinHierNode(0, current_node);

  //top node
  PnRDB::hierNode current_node1=DB.CheckoutHierNode(1);
  Placer curr_plc1(current_node1);
  Router curr_route1(current_node1, design_rule, binary_directory);
 
  return 0;
}
