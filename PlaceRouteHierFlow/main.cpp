#include <string>
#include <iostream>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/Router.h"
#include "./cap_placer/capplacer.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <sstream>

using std::string;
using std::cout;
using std::endl;

double ConstGraph::LAMBDA=1000;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=100;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=1500;

static void save_state( const PnRdatabase& DB, const PnRDB::hierNode& current_node, int lidx,
			const string& opath, const string& tag, const string& ltag, bool skip)
{
  if ( skip) return;

  string ofn;
  if ( lidx >= 0) {
    ofn = opath+current_node.name + "_" + std::to_string(lidx) + tag + ".db.json";
  } else {
    ofn = opath+current_node.name + tag + ".db.json";
  }
  DB.WriteDBJSON(current_node,ofn);
  std::cout << ltag << std::endl;
}

static void route_single_variant( PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::hierNode& current_node, int lidx, const string& opath, const string& binary_directory, bool skip_saving_state, bool adr_mode)
{
  std::cout<<"Checkpoint: work on layout "<<lidx<<std::endl;
  DB.Extract_RemovePowerPins(current_node);

  std::cout<<"Checkpoint : before route"<<std::endl;
  DB.PrintHierNode(current_node);

  DB.WriteJSON (current_node, true, false, false, false, current_node.name+"_PL_"+std::to_string(lidx), drcInfo, opath); //block net powernet powergrid

  Router curr_route;

  bool NEW_GLOBAL_ROUTER = 1;

  if ( NEW_GLOBAL_ROUTER) {
    // Gcell Global Routing
    save_state( DB, current_node, lidx, opath, ".pre_gr", "Starting Gcell Global Routing", skip_saving_state);
    int global_router_mode = 4;
    if ( adr_mode) {
      global_router_mode = 6;
    }
    curr_route.RouteWork(global_router_mode, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    save_state( DB, current_node, lidx, opath, ".post_gr", "Ending Gcell Global Routing", skip_saving_state);

    std::cout << "***WriteGcellGlobalRoute Debugging***" << std::endl;
    DB.WriteGcellGlobalRoute(current_node, current_node.name+"_GcellGlobalRoute_"+std::to_string(lidx)+".json", opath);
    std::cout << "***End WriteGcellGlobalRoute Debugging***" << std::endl;

    save_state( DB, current_node, lidx, opath, ".pre_dr", "Starting Gcell Detail Routing", skip_saving_state);
    curr_route.RouteWork(5, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    save_state( DB, current_node, lidx, opath, ".post_dr", "Ending Gcell Detail Routing", skip_saving_state);
  } else {
    // Global Routing (old version)
    save_state( DB, current_node, lidx, opath, ".pre_gr", "Checkpoint : global route", skip_saving_state);
    curr_route.RouteWork(0, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    save_state( DB, current_node, lidx, opath, ".post_gr", "Checkpoint : after global route", skip_saving_state);

    DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_GR_"+std::to_string(lidx), drcInfo, opath);
    // The following line is used to write global route results for Intel router (only for old version)
    DB.WriteGlobalRoute(current_node, current_node.name+"_GlobalRoute_"+std::to_string(lidx)+".json", opath);

    // Detail Routing
    save_state( DB, current_node, lidx, opath, ".pre_dr", "Checkpoint : detail route", skip_saving_state);
    curr_route.RouteWork(1, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    save_state( DB, current_node, lidx, opath, ".post_dr", "Checkpoint : after detail route", skip_saving_state);
  }

  DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_DR_"+std::to_string(lidx), drcInfo, opath);
  //DB.WriteJSON_Routability_Analysis (current_node, opath);

  if(current_node.isTop){
    save_state( DB, current_node, lidx, opath, ".pre_pg", "Checkpoint : Starting Power Grid Creation", skip_saving_state);
    curr_route.RouteWork(2, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 5, 6, binary_directory);
    save_state( DB, current_node, lidx, opath, ".post_pg", "Checkpoint : End Power Grid Creation", skip_saving_state);

    DB.WriteJSON (current_node, true, true, false, true, current_node.name+"_PG_"+std::to_string(lidx), drcInfo, opath);
        
    std::cout<<"Checkpoint : Starting Power Routing"<<std::endl;
    save_state( DB, current_node, lidx, opath, ".pre_pr", "Checkpoint : Starting Power Routing", skip_saving_state);
    curr_route.RouteWork(3, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    save_state( DB, current_node, lidx, opath, ".post_pr", "Checkpoint : End Power Routing", skip_saving_state);

    DB.WriteJSON (current_node, true, false, true, true, current_node.name+"_PR_"+std::to_string(lidx), drcInfo, opath);
        
  }

  DB.WriteJSON (current_node, true, true, true, true, current_node.name+"_"+std::to_string(lidx), drcInfo, opath);
  std::cout<<"Check point : before checkin\n";
  DB.PrintHierNode(current_node);
      
  save_state( DB, current_node, lidx, opath, "", "Final result", skip_saving_state);

  DB.WriteLef(current_node, current_node.name+"_"+std::to_string(lidx)+".lef", opath);

  /*
  std::ostringstream oss;
  oss << "gen_viewer_json.py"
      << " -b " << current_node.name
      << " -v " << lidx
      << " -d " << opath
      << " -o " << opath;
  string cmd(oss.str());

  int rc = system( cmd.c_str());
  std::cout << "System call to: \"" << cmd << "\" returned " << rc << std::endl;
  
  PnRDB::hierNode current_node2;

  DB.ReadDBJSON( current_node2,ofn);
  DB.WriteDBJSON( current_node2,ofn+"2");
  */

}


int main(int argc, char** argv ){

  //
  // Enable or disable state saving in json at intermediate points
  // Currently adds 4 seconds to a 29 second baseline for the switched_capacitor_filter
  // And generates 69MB in files
  bool skip_saving_state = getenv( "PNRDB_SAVE_STATE") == NULL;
  bool adr_mode = getenv( "PNRDB_ADR_MODE") != NULL;

  string opath="./Results/";
  string fpath=argv[1];
  string lfile=argv[2];
  string vfile=argv[3];
  string mfile=argv[4];
  string dfile=argv[5];
  string topcell=argv[6];
  int numLayout=std::stoi(argv[7]);
  int effort=std::stoi(argv[8]);
  if(fpath.back()=='/') {fpath.erase(fpath.end()-1);}
  if(opath.back()!='/') {opath+="/";}

  // Following codes try to get the path of binary codes
  string binary_directory = argv[0];
  cout <<"argv[0]: "<<binary_directory <<endl;
  int beginIdx = binary_directory.rfind('/');//find the last slash
  string str_lastOne = binary_directory.substr(beginIdx+1);
  cout <<"string after last slash: "<<str_lastOne <<endl;
  binary_directory = binary_directory.erase(beginIdx+1);
  cout <<"binary_directory: "<< binary_directory <<endl;

  mkdir(opath.c_str(), 0777);

  PnRdatabase DB(fpath, topcell, vfile, lfile, mfile, dfile); // construction of database
  PnRDB::Drc_info drcInfo=DB.getDrc_info();
  map<string, PnRDB::lefMacro> lefData = DB.checkoutSingleLEF();
  queue<int> Q=DB.TraverseHierTree(); // traverse hierarchical tree in topological order

  while (!Q.empty())
  {
    int idx=Q.front();
    cout<<"Main-Info: start to work on node "<<idx<<endl;
    PnRDB::hierNode current_node=DB.CheckoutHierNode(idx);
    DB.PrintHierNode(current_node);

    
    save_state( DB, current_node, -1, opath, ".pre_prc", "Placer_Router_Cap", skip_saving_state);
    DB.AddingPowerPins(current_node);
    Placer_Router_Cap PRC(opath, fpath, current_node, drcInfo, lefData, 1, 6); //dummy, aspect ratio, number of aspect retio
    save_state( DB, current_node, -1, opath, ".post_prc", "Placer_Router_Cap", skip_saving_state);

    std::cout<<"Checkpoint : before place"<<std::endl;
    DB.PrintHierNode(current_node);

    save_state( DB, current_node, -1, opath, ".pre_pl", "Before Placement", skip_saving_state);
    
    // Placement
    std::vector<PnRDB::hierNode> nodeVec(numLayout, current_node);
    Placer curr_plc(nodeVec, opath, effort, const_cast<PnRDB::Drc_info&>(drcInfo)); // do placement and update data in current node

    for(unsigned int lidx=0; lidx<nodeVec.size(); ++lidx) {
      save_state( DB, nodeVec[lidx], lidx, opath, ".post_pl", "End Placement", skip_saving_state);
    }

    std::cout<<"Checkpoint: generated "<<nodeVec.size()<<" placements\n";
    for(unsigned int lidx=0; lidx<nodeVec.size(); ++lidx) {
      route_single_variant( DB, drcInfo, nodeVec[lidx], lidx, opath, binary_directory, skip_saving_state, adr_mode);
    }

    for(unsigned int lidx=0; lidx<nodeVec.size(); ++lidx) {
      DB.CheckinHierNode(idx, nodeVec[lidx]);
    }

    Q.pop();
    cout<<"Main-Info: complete node "<<idx<<endl;
  }

  return 0;
}
