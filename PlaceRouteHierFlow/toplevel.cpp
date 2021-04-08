#include "toplevel.h"

#include <string>
#include <iostream>
#include <iomanip>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/PlacerIfc.h"
#include "./cap_placer/CapPlacerIfc.h"
#include "./guard_ring/GuardRingIfc.h"

// Need to eventuall replace with similar Ifc, but not until we remove the helper functions: route_single_variant and route top_down
#include "./MNA/MNASimulation.h"
#include "./router/Router.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <sstream>
#include <thread>

using std::string;
using std::cout;
using std::endl;

void save_state( const PnRdatabase& DB, const PnRDB::hierNode& current_node, int lidx,
			const string& opath, const string& tag, const string& ltag, bool skip)
{
  auto logger = spdlog::default_logger()->clone("save_state");

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
  logger->info("{0} to {1}", ltag, ofn);
}

void route_single_variant( PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::hierNode& current_node, int lidx, const string& opath, const string& binary_directory, bool skip_saving_state, bool adr_mode)
{

  auto logger = spdlog::default_logger()->clone("route_single_variant");

  //std::cout<<"Checkpoint: work on layout "<<lidx<<std::endl;
  //DB.Extract_RemovePowerPins(current_node);
  string dummy_file;
  //std::cout<<"Checkpoint : before route"<<std::endl;
  DB.PrintHierNode(current_node);

  //DB.WriteJSON (current_node, true, false, false, false, current_node.name+"_PL_"+std::to_string(lidx), drcInfo, opath); //block net powernet powergrid

  Router curr_route;

  bool NEW_GLOBAL_ROUTER = 1;
  int h_skip_factor = 5;
  int v_skip_factor = 5;

  int signal_routing_metal_l = drcInfo.Design_info.signal_routing_metal_l;
  int signal_routing_metal_u = drcInfo.Design_info.signal_routing_metal_u;

  if ( NEW_GLOBAL_ROUTER) {
    // Gcell Global Routing

    int global_router_mode = 4;
    if ( adr_mode) {
      global_router_mode = 6;
    }
    curr_route.RouteWork(global_router_mode, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor,dummy_file);

    logger->debug( "***WriteGcellGlobalRoute Debugging***");
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
    logger->debug("***End WriteGcellGlobalRoute Debugging***" );

    curr_route.RouteWork(5, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor,dummy_file);
    DB.WriteGcellDetailRoute(current_node, current_node.name+"_DetailRoute_"+std::to_string(lidx)+".json", opath);

  } else {
    // Global Routing (old version)

    curr_route.RouteWork(0, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor,dummy_file);

    DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_GR_"+std::to_string(lidx), drcInfo, opath);
    // The following line is used to write global route results for Intel router (only for old version)
    DB.WriteGlobalRoute(current_node, current_node.name+"_GlobalRoute_"+std::to_string(lidx)+".json", opath);

    // Detail Routing
    curr_route.RouteWork(1, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), signal_routing_metal_l, signal_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor,dummy_file);
    DB.WriteGcellDetailRoute(current_node, current_node.name+"_DetailRoute_"+std::to_string(lidx)+".json", opath);
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

    int power_grid_metal_l = drcInfo.Design_info.power_grid_metal_l;
    int power_grid_metal_u = drcInfo.Design_info.power_grid_metal_u;
    int power_routing_metal_l = drcInfo.Design_info.power_routing_metal_l;
    int power_routing_metal_u = drcInfo.Design_info.power_routing_metal_u;
 
    bool PDN_mode = false;
    //DC Power Grid Simulation
    if(PDN_mode){
      bool dataset_generation = false;
      string current_file = "InputCurrent_initial.txt";
      string power_mesh_conffile = "Power_Grid_Conf.txt";
      if(dataset_generation){
        double total_current = 0.036;
        int current_number = 20;
        DB.Write_Current_Workload(current_node, total_current, current_number, current_file);
        DB.Write_Power_Mesh_Conf(power_mesh_conffile);
      }
      power_grid_metal_l = 2;
      power_grid_metal_u = 11;
      curr_route.RouteWork(7, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), power_grid_metal_l, power_grid_metal_u, binary_directory, h_skip_factor, v_skip_factor, power_mesh_conffile);
      logger->debug("Start MNA ");
      string output_file_IR = "IR_drop.txt";
      string output_file_EM = "EM.txt";
      MNASimulation Test_MNA(current_node, const_cast<PnRDB::Drc_info&>(drcInfo), current_file, output_file_IR, output_file_EM);
      double worst = Test_MNA.Return_Worst_Voltage();
      logger->debug("worst voltage is {0} ", worst);
      logger->debug("End MNA ");
      Test_MNA.Clear_Power_Grid(current_node.Vdd);
      Test_MNA.Clear_Power_Grid(current_node.Gnd);
      return;
    }
              
    
    curr_route.RouteWork(2, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), power_grid_metal_l, power_grid_metal_u, binary_directory, h_skip_factor, v_skip_factor,dummy_file);

    DB.WriteJSON(current_node, true, true, false, true, current_node.name + "_PG_" + std::to_string(lidx), drcInfo, opath);

    logger->debug("Checkpoint : Starting Power Routing");
    curr_route.RouteWork(3, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), power_routing_metal_l, power_routing_metal_u, binary_directory, h_skip_factor, v_skip_factor,dummy_file);
    
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

int route_top_down(PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::bbox bounding_box, PnRDB::Omark current_node_ort,
                           int idx, int lidx, const string& opath, const string& binary_directory,
                           bool skip_saving_state, bool adr_mode) {

  auto logger = spdlog::default_logger()->clone("route_top_down");

  /*
  recursively DFS hiertree
  Inputs:
    current_node_ort: absolute orientation of current_node
    idx: index of current_node type
    lidx: number of layouts, now is one.
  Outputs: 
    new_currentnode_idx: index of current_node copy in hiertree, after routing
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
    for (int lidx = 0; lidx < DB.hierTree[child_idx].numPlacement; lidx++) {
      new_childnode_idx = route_top_down(DB, drcInfo, childnode_box, childnode_orient, child_idx, lidx, opath, binary_directory,
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
  if (!current_node.isTop) {
    // Don't seem to be doing this for the top cell in route_single...
    DB.TransformNode(current_node, current_node.LL, current_node.abs_orient, PnRDB::TransformType::Backward);
  }

  // 9.pushback current_node into hiertree, update current_node copy's index
  // update hiertree[blocks.*.child].parent = new_currentnode_idx
  DB.hierTree.push_back(current_node);
  int new_currentnode_idx = DB.hierTree.size() - 1;

  for (unsigned int bit = 0; bit < current_node.Blocks.size(); bit++) {
    auto& blk = current_node.Blocks[bit];
    if (blk.child == -1) continue;
    assert( DB.hierTree[blk.child].parent.size() > 0);
    DB.hierTree[blk.child].parent[0] = new_currentnode_idx;
  }

  return new_currentnode_idx;
}

std::unique_ptr<PnRdatabase> toplevel( const std::vector<std::string>& argv) {
  
  auto logger = spdlog::default_logger()->clone("toplevel");

  //
  // Enable or disable state saving in json at intermediate points
  // Currently adds 4 seconds to a 29 second baseline for the switched_capacitor_filter
  // And generates 69MB in files
  bool skip_saving_state = getenv( "PNRDB_SAVE_STATE") == NULL;
  bool adr_mode = getenv( "PNRDB_ADR_MODE") != NULL;
  //bool multi_thread = getenv( "PNRDB_multi_thread") != NULL;;  // run multi layouts in multi threads
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
  //spdlog::set_level(spdlog::level::debug);

  // Following codes try to get the path of binary codes
  string binary_directory = argv[0];
  logger->info("argv[0]: {0}",binary_directory);
  int beginIdx = binary_directory.rfind('/');//find the last slash
  string str_lastOne = binary_directory.substr(beginIdx+1);
  logger->info("string after last slash: {0}",str_lastOne);
  binary_directory = binary_directory.erase(beginIdx+1);
  logger->info("binary_directory: {0}", binary_directory);

  mkdir(opath.c_str(), 0777);
  std::unique_ptr<PnRdatabase> DB_ptr(new PnRdatabase(fpath, topcell, vfile, lfile, mfile, dfile)); // construction of database
  PnRdatabase& DB = *DB_ptr;
  PnRDB::Drc_info drcInfo=DB.getDrc_info();
  map<string, PnRDB::lefMacro> lefData = DB.checkoutSingleLEF();

  deque<int> TraverseOrder = DB.TraverseHierTree();  // traverse hierarchical tree in topological order

  if ( !skip_saving_state) {
    json jsonStrAry = json::array();
    std::ofstream jsonStream;
    jsonStream.open( opath + "__hierTree.json");
    for ( auto ptr = TraverseOrder.begin(); ptr != TraverseOrder.end(); ++ptr) {
      jsonStrAry.push_back( DB.CheckoutHierNode(*ptr).name);      
    }
    jsonStream << std::setw(4) << jsonStrAry;
    jsonStream.close();
  }

  for (unsigned int i = 0; i < TraverseOrder.size(); i++)
  {
    int idx=TraverseOrder[i];
    logger->info("Main-Info: start to work on node {0}",idx);
    PnRDB::hierNode current_node=DB.CheckoutHierNode(idx);
    DB.PrintHierNode(current_node);
    logger->info("Start placement: {0}",current_node.name);
    
    
    DB.AddingPowerPins(current_node);
    Placer_Router_Cap_Ifc PRC(opath, fpath, current_node, drcInfo, lefData, 1, 6); //dummy, aspect ratio, number of aspect retio

    logger->debug("Checkpoint : before place");
    DB.PrintHierNode(current_node);

    // Placement
    PlacerIfc curr_plc(current_node, numLayout, opath, effort, const_cast<PnRDB::Drc_info&>(drcInfo)); // do placement and update data in current node
    std::vector<PnRDB::hierNode>& nodeVec(curr_plc.get());

    logger->debug("Checkpoint: generated {0} palcements",nodeVec.size());
    //insert guard ring
    for(unsigned int lidx=0; lidx<nodeVec.size(); ++lidx) {
      if (nodeVec[lidx].Guardring_Consts.size()>0){
      //if (1){
        GuardRingIfc current_guard_ring(nodeVec[lidx], lefData, drcInfo);
      }
      DB.PrintHierNode(nodeVec[lidx]);
      DB.WriteJSON(nodeVec[lidx], true, false, false, false, nodeVec[lidx].name + "_PL_" + std::to_string(lidx), drcInfo, opath);
    }

    for(unsigned int lidx=0; lidx<nodeVec.size(); ++lidx) {
      logger->debug("Checkpoint: extract power pins work on layout {0} ",lidx);
      DB.Extract_RemovePowerPins(nodeVec[lidx]);
      logger->debug("Checkpoint: checkin node work on layout {0}",lidx);
      DB.CheckinHierNode(idx, nodeVec[lidx]);
      logger->debug("Checkpoint: work on layout {0}",lidx);
    }
    DB.hierTree[idx].numPlacement = nodeVec.size();
    logger->info("Main-Info: complete node {0}",idx);
  }

  //int new_topnode_idx = 0;
  for (int lidx = 0; lidx < DB.hierTree[TraverseOrder.back()].numPlacement; lidx++) {
    auto &ct = DB.hierTree[TraverseOrder.back()];
    PnRDB::bbox bb( PnRDB::point(0, 0), PnRDB::point(ct.PnRAS[0].width, ct.PnRAS[0].height));
    route_top_down(
        DB, drcInfo,
	bb, PnRDB::N,
	TraverseOrder.back(), lidx, opath, binary_directory, skip_saving_state, adr_mode);
  }

  return DB_ptr;
}
