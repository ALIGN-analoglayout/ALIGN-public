#include <string>
#include <iostream>
#include <iomanip>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/Router.h"
#include "./cap_placer/capplacer.h"
#include "./MNA/MNASimulation.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <sstream>
#include <thread>

#include "spdlog/spdlog.h"

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

  int copy_number = current_node.n_copy;

  string ofn;
  if ( lidx >= 0) {
    if ( current_node.isTop) {
      ofn = opath+current_node.name + "_" + std::to_string(lidx) + tag + ".db.json";
    } else {
      ofn = opath+current_node.name + "_" + std::to_string(copy_number) + "_" + std::to_string(lidx) + tag + ".db.json";
    }
  } else {
    ofn = opath+current_node.name + tag + ".db.json";
  }
  DB.WriteDBJSON(current_node,ofn);
  std::cout << ltag << std::endl;
}

static void route_single_variant( PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::hierNode& current_node, int lidx, const string& opath, const string& binary_directory, bool skip_saving_state, bool adr_mode)
{
  //std::cout<<"Checkpoint: work on layout "<<lidx<<std::endl;
  //DB.Extract_RemovePowerPins(current_node);

  std::cout<<"Checkpoint : before route"<<std::endl;
  DB.PrintHierNode(current_node);

  //DB.WriteJSON (current_node, true, false, false, false, current_node.name+"_PL_"+std::to_string(lidx), drcInfo, opath); //block net powernet powergrid

  Router curr_route;

  bool NEW_GLOBAL_ROUTER = 1;
  int h_skip_factor = 5;
  int v_skip_factor = 5;

  int signal_routing_metal_l = 0;
  int signal_routing_metal_u = 8;

  if ( NEW_GLOBAL_ROUTER) {
    // Gcell Global Routing

    int global_router_mode = 4;
    if ( adr_mode) {
      global_router_mode = 6;
    }
    curr_route.RouteWork(global_router_mode, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor);

    std::cout << "***WriteGcellGlobalRoute Debugging***" << std::endl;
    if (current_node.isTop) {
      DB.WriteGcellGlobalRoute(current_node, current_node.name + "_GcellGlobalRoute_" + std::to_string(lidx) + ".json", opath);
    } else {
      PnRDB::hierNode current_node_copy = current_node;
      DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, PnRDB::TransformType::Backward);
      DB.WriteGcellGlobalRoute(
          current_node_copy,
          current_node_copy.name + "_GcellGlobalRoute_" + std::to_string(current_node_copy.n_copy) + "_" + std::to_string(lidx) + ".json",
          opath);
    }
    std::cout << "***End WriteGcellGlobalRoute Debugging***" << std::endl;

    curr_route.RouteWork(5, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor);

  } else {
    // Global Routing (old version)

    curr_route.RouteWork(0, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor);

    DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_GR_"+std::to_string(lidx), drcInfo, opath);
    // The following line is used to write global route results for Intel router (only for old version)
    DB.WriteGlobalRoute(current_node, current_node.name+"_GlobalRoute_"+std::to_string(lidx)+".json", opath);

    // Detail Routing
    curr_route.RouteWork(1, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor);
  }

  if (current_node.isTop) {
    DB.WriteJSON(current_node, true, true, false, false, current_node.name + "_DR_" + std::to_string(lidx), drcInfo, opath);
  } else {
    PnRDB::hierNode current_node_copy = current_node;
    DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, PnRDB::TransformType::Backward);
    DB.WriteJSON(current_node_copy, true, true, false, false,
                 current_node_copy.name + "_DR_" + std::to_string(current_node_copy.n_copy) + "_" + std::to_string(lidx), drcInfo, opath);
    current_node.gdsFile = current_node_copy.gdsFile;
  }
  // DB.WriteJSON_Routability_Analysis (current_node, opath, const_cast<PnRDB::Drc_info&>(drcInfo));

  //double worst=0;
  //double th = 0.1;
  //bool Power_mesh_optimize = 0;

  if(current_node.isTop){

/*  DC Power Grid Simulation
 *
 * SMB: this code is broken because rate has been replaced by h_skip_factor and v_skip_factor (1 over the rate and different for h and v wires

    while(Power_mesh_optimize and worst < th and rate<1){

      curr_route.RouteWork(2, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 5, 6, binary_directory, rate);
    
      std::cout<<"Start MNA "<<std::endl;
      MNASimulation Test_MNA(current_node, const_cast<PnRDB::Drc_info&>(drcInfo));
   
      worst = Test_MNA.Return_Worst_Voltage();
      std::cout<<"worst voltage is "<< worst << std::endl;
      std::cout<<"End MNA "<<std::endl;
      Test_MNA.Clear_Power_Grid(current_node.Vdd);
      Test_MNA.Clear_Power_Grid(current_node.Gnd);      
      rate = rate + 0.1;
       
    }
*/

    int power_grid_metal_l = 5;
    int power_grid_metal_u = 6;
    int power_routing_metal_l = 0;
    int power_routing_metal_u = 6;

    curr_route.RouteWork(2, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), power_grid_metal_l, power_grid_metal_u, binary_directory, h_skip_factor, v_skip_factor);

    DB.WriteJSON(current_node, true, true, false, true, current_node.name + "_PG_" + std::to_string(lidx), drcInfo, opath);

    std::cout<<"Checkpoint : Starting Power Routing"<<std::endl;
    curr_route.RouteWork(3, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), power_routing_metal_l, power_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor);
    
    DB.WriteJSON(current_node, true, false, true, true, current_node.name + "_PR_" + std::to_string(lidx), drcInfo, opath);
    
    DB.Write_Router_Report(current_node, opath);
  }

  // transform current_node into current_node coordinate
  if (current_node.isTop) {
    DB.WriteJSON(current_node, true, true, true, true, current_node.name + "_" + std::to_string(lidx), drcInfo, opath);
    DB.WriteLef(current_node, current_node.name + "_" + std::to_string(lidx) + ".lef", opath);
    save_state( DB, current_node, lidx, opath, "", "Final result", skip_saving_state);
    DB.PrintHierNode(current_node);
  } else {
    PnRDB::hierNode current_node_copy = current_node;
    DB.TransformNode(current_node_copy, current_node_copy.LL, current_node_copy.abs_orient, PnRDB::TransformType::Backward);
    DB.WriteJSON(current_node_copy, true, true, true, true,
                 current_node_copy.name + "_" + std::to_string(current_node_copy.n_copy) + "_" + std::to_string(lidx), drcInfo, opath);
    current_node.gdsFile = current_node_copy.gdsFile;
    DB.WriteLef(current_node_copy,
                current_node_copy.name + "_" + std::to_string(current_node_copy.n_copy) + "_" + std::to_string(lidx) + ".lef", opath);

    save_state( DB, current_node_copy, lidx, opath, "", "Final result", skip_saving_state);
    DB.PrintHierNode(current_node_copy);
  }


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

void static route_top_down(PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::bbox bounding_box, PnRDB::Omark current_node_ort,
                           int idx, int& new_currentnode_idx, int lidx, const string& opath, const string& binary_directory,
                           bool skip_saving_state, bool adr_mode) {

  /*
  recursively DFS hiertree
  Inputs:
    current_node_ort: absolute orientation of current_node
    idx: index of current_node type
    new_currentnode_idx: index of current_node copy in hiertree, after routing
    lidx: number of layouts, now is one.
  */
  //Q: current top down flow works when lidx = 1. Yaguang -- 3/17/2020
  //Q: Conflict here when lidx != 1. childnode only stores last update in bottom-up (maybe 2), while the selected block might be 1. When doing top-down, mismatch happens. Yaguang -- 3/17/2020
  //Q: solution should be refresh the content of childnode by childnode.PnRAS[current_node.Blocks.selectedInstance]. Yaguang -- 3/17/2020
  //Q: power routing does not change, still do power routing when it comes to top level. Yaguang -- 3/17/2020
  //Q: Power routing dose not work when lidx != 1. Need double check? Yaguang -- 3/17/2020
  // 1.copy current_node from hiertree[idx]
  PnRDB::hierNode current_node = DB.hierTree[idx];
  DB.hierTree[idx].n_copy += 1;
  string current_node_name = current_node.name;
  current_node.LL = bounding_box.LL;
  current_node.UR = bounding_box.UR;
  current_node.abs_orient = current_node_ort;
  // 2.transform (translate and rotate) all points and rects of current_node into topnode coordinate;
  DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, PnRDB::TransformType::Forward);
  for (unsigned int bit = 0; bit < current_node.Blocks.size(); bit++) {
    auto& blk = current_node.Blocks[bit];
    int child_idx = blk.child;
    if (child_idx == -1) continue;
    auto& inst = blk.instance[blk.selectedInstance];
    // calculate childnode's orientation in topnode
    PnRDB::Omark childnode_orient = DB.RelOrt2AbsOrt(current_node_ort, inst.orient);
    string child_node_name = DB.hierTree[child_idx].name;
    // 3.childnode.LL and UR, absolute bouding box in topnode coordinate
    PnRDB::bbox childnode_box( inst.placedBox.LL, inst.placedBox.UR);
    // 4.complete all children of current_node recursively
    int new_childnode_idx = 0;
    for (unsigned int lidx = 0; lidx < DB.hierTree[child_idx].numPlacement; lidx++) {
      route_top_down(DB, drcInfo, childnode_box, childnode_orient, child_idx, new_childnode_idx, lidx, opath, binary_directory,
                     skip_saving_state, adr_mode);
    }
    // 6.update current_node.blocks[i].intermetal/via/blockpin, absolute position and rect
    DB.CheckinChildnodetoBlock(current_node, bit, DB.hierTree[new_childnode_idx]);  // check in childnode into block
    
    // 7.current_node.Blocks[bit].child links to childnode
    current_node.Blocks[bit].child = new_childnode_idx;
  }
  DB.ExtractPinsToPowerPins(current_node);
  route_single_variant(DB, drcInfo, current_node, lidx, opath, binary_directory, skip_saving_state, adr_mode);

  // 8.transform (translate and rotate) current_node into current_node coordinate
  // undo transform current_node.LL and current_node_ort
  DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, PnRDB::TransformType::Backward);

  // 9.pushback current_node into hiertree, update current_node copy's index
  // update hiertree[blocks.*.child].parent = new_currentnode_idx
  DB.hierTree.push_back(current_node);
  new_currentnode_idx = DB.hierTree.size() - 1;
  for (unsigned int bit = 0; bit < current_node.Blocks.size(); bit++) {
    auto& blk = current_node.Blocks[bit];
    if (blk.child == -1) continue;
    DB.hierTree[blk.child].parent[0] = new_currentnode_idx;
  }
  return;
}

int main(int argc, char** argv ){

  spdlog::set_level(spdlog::level::warn);
  spdlog::info("Welcome to spdlog!");

  //
  // Enable or disable state saving in json at intermediate points
  // Currently adds 4 seconds to a 29 second baseline for the switched_capacitor_filter
  // And generates 69MB in files
  bool skip_saving_state = getenv( "PNRDB_SAVE_STATE") == NULL;
  bool adr_mode = getenv( "PNRDB_ADR_MODE") != NULL;
  bool disable_io = getenv( "PNRDB_disable_io") != NULL;; //turn off window outputs
  bool multi_thread = getenv( "PNRDB_multi_thread") != NULL;;  // run multi layouts in multi threads
  //bool disable_io = false; //turn off window outputs
  //bool multi_thread = false;  // run multi layouts in multi threads

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


  if ( !skip_saving_state) {
    queue<int> Q=DB.TraverseHierTree(); // traverse hierarchical tree in topological order
    json jsonStrAry = json::array();
    std::ofstream jsonStream;
    jsonStream.open( opath + "__hierTree.json");
    while (!Q.empty()) {
      jsonStrAry.push_back( DB.CheckoutHierNode(Q.front()).name);
      Q.pop();
    }
    jsonStream << std::setw(4) << jsonStrAry;
    jsonStream.close();
  }

  queue<int> Q = DB.TraverseHierTree();  // traverse hierarchical tree in topological order
  std::vector<int> TraverseOrder;        // save traverse order, same as Q
  int Q_size = Q.size();
  for (int i = 0; i < Q_size; i++) {  // copy Q to TraverseOrder
    TraverseOrder.push_back(Q.front());
    Q.pop();
    Q.push(TraverseOrder.back());
  }

  for (int i = 0; i < Q_size;i++)
  {
    int idx=TraverseOrder[i];
    cout<<"Main-Info: start to work on node "<<idx<<endl;
    if(disable_io)std::cout.setstate(std::ios_base::failbit);
    PnRDB::hierNode current_node=DB.CheckoutHierNode(idx);
    DB.PrintHierNode(current_node);

    
    DB.AddingPowerPins(current_node);
    Placer_Router_Cap PRC(opath, fpath, current_node, drcInfo, lefData, 1, 6); //dummy, aspect ratio, number of aspect retio

    std::cout<<"Checkpoint : before place"<<std::endl;
    DB.PrintHierNode(current_node);

    
    // Placement
    std::vector<PnRDB::hierNode> nodeVec(numLayout, current_node);
    Placer curr_plc(nodeVec, opath, effort, const_cast<PnRDB::Drc_info&>(drcInfo)); // do placement and update data in current node

    std::cout<<"Checkpoint: generated "<<nodeVec.size()<<" placements\n";
    for(unsigned int lidx=0; lidx<nodeVec.size(); ++lidx) {
      //std::cout<<"Checkpoint: work on layout "<<lidx<<std::endl;
      DB.Extract_RemovePowerPins(nodeVec[lidx]);
      DB.CheckinHierNode(idx, nodeVec[lidx]);
    }
    DB.hierTree[idx].numPlacement = nodeVec.size();

    //TreeVec[idx] = nodeVec;
    //Q.pop();
    if(disable_io)std::cout.clear();
    cout<<"Main-Info: complete node "<<idx<<endl;
  }

  if(disable_io)std::cout.setstate(std::ios_base::failbit);
  int new_topnode_idx = 0;
  for (unsigned int lidx = 0; lidx < DB.hierTree[Q.back()].numPlacement; lidx++) {
    route_top_down(
        DB, drcInfo,
        PnRDB::bbox(PnRDB::point(0, 0), PnRDB::point(DB.hierTree[Q.back()].PnRAS[0].width, DB.hierTree[Q.back()].PnRAS[0].height)),
        PnRDB::N, Q.back(), new_topnode_idx, lidx, opath, binary_directory, skip_saving_state, adr_mode);
  }
  if(disable_io)std::cout.clear();

  return 0;
}
