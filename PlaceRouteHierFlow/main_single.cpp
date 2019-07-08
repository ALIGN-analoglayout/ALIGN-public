#include <string>
#include <iostream>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/Router.h"
#include "./cap_placer/capplacer.h"
//#include "./cap_placer/Capdatatype.h"

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
  ////string fpath="./switched_cap_filter_hierarchical_2018_12_06";
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
  //PnRDB::designRule design_rule=DB.getDesignRule(); 
  PnRDB::Drc_info drcInfo=DB.getDrc_info();
  map<string, PnRDB::lefMacro> lefData = DB.checkoutSingleLEF();
  queue<int> Q=DB.TraverseHierTree(); // traverse hierarchical tree in topological order

  while (!Q.empty())
  {
    int idx=Q.front();
    cout<<"Main-Info: start to work on node "<<idx<<endl;
    PnRDB::hierNode current_node=DB.CheckoutHierNode(idx);
    DB.PrintHierNode(current_node);

    DB.AddingPowerPins(current_node);

    Placer_Router_Cap PRC(fpath, current_node, drcInfo, lefData, 0, 1, 3); //dummy, aspect ratio, number of aspect retio

    std::cout<<"Checkpoint : before place"<<std::endl;
    DB.PrintHierNode(current_node);
    // Placement
    Placer curr_plc(current_node); // do placement and update data in current node

    DB.Extract_RemovePowerPins(current_node);

    std::cout<<"Checkpoint : before route"<<std::endl;
    DB.PrintHierNode(current_node);
    //    DB.WriteGDS(current_node, true, false, false, false, current_node.name+"_PL", drcInfo); //block net powernet powergrid
    DB.WriteJSON (current_node, true, false, false, false, current_node.name+"_PL", drcInfo); //block net powernet powergrid

    Router curr_route;

    // Global Routing

    curr_route.RouteWork(0, current_node, drcInfo, 1, 6, binary_directory);
    std::cout<<"Checkpoint : after global route"<<std::endl;
    DB.PrintHierNode(current_node);

    //    DB.WriteGDS(current_node, true, true, false, false, current_node.name+"_GR", drcInfo);
    DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_GR", drcInfo);

    // Detail Routing
    std::cout<<"Checkpoint : detail route"<<std::endl;
    curr_route.RouteWork(1, current_node, drcInfo, 1, 6, binary_directory);
    std::cout<<"Checkpoint : after detail route"<<std::endl;
    DB.PrintHierNode(current_node);

    //    DB.WriteGDS(current_node, true, true, false, false, current_node.name+"_DR", drcInfo);
    DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_DR", drcInfo);

    if(current_node.isTop){
      std::cout<<"Checkpoint : Starting Power Grid Creation"<<std::endl;
      curr_route.RouteWork(2, current_node, drcInfo, 5, 6, binary_directory);
      std::cout<<"Checkpoint : End Power Grid Creation"<<std::endl;

      //      DB.WriteGDS(current_node, true, true, false, true, current_node.name+"_PG", drcInfo);
      DB.WriteJSON (current_node, true, true, false, true, current_node.name+"_PG", drcInfo);
      
      std::cout<<"Checkpoint : Starting Power Routing"<<std::endl;
      curr_route.RouteWork(3, current_node, drcInfo, 1, 6, binary_directory);
      std::cout<<"Checkpoint : End Power Grid Routing"<<std::endl;

      //      DB.WriteGDS(current_node, true, false, true, true, current_node.name+"_PR", drcInfo);
      DB.WriteJSON (current_node, true, false, true, true, current_node.name+"_PR", drcInfo);
      
      }
  
    //    DB.WriteGDS(current_node, true, true, true, true, current_node.name, drcInfo);
    DB.WriteJSON (current_node, true, true, true, true, current_node.name, drcInfo);
    //std::cout<<"Check point : before checkin\n";
    //DB.PrintHierNode(current_node);
    // Update node
    DB.CheckinHierNode(idx, current_node);
    //return 0;
    
    Q.pop();
    cout<<"Main-Info: complete node "<<idx<<endl;
  }

  return 0;
}
