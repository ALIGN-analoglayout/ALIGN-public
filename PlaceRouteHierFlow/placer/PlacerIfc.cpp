
#include "../PnRDB/datatype.h"
#include "PlacerIfc.h"
#include "Placer.h"
#include "../EA_placer/placement.h"
#include <chrono>

double ConstGraph::LAMBDA=1.;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=0.1;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=0.05;
double ConstGraph::PI=0.05;
double ConstGraph::PII=1;

PlacerIfc::PlacerIfc(PnRDB::hierNode& currentNode, int numLayout, string opath, int effort, PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper, bool select_in_ILP = false, int ilp_solver = 0) : _nodeVec( numLayout, currentNode) {
  ConstGraph::LAMBDA = hyper.LAMBDA;
  if (hyper.use_analytical_placer) {
    /*
     * From PR text
     * I don't know what these values should be:
     *      dummy_init_weight, dummy_init_rate, placement_id
     */
    Placement EA_placer;
    double dummy_init_weight = 1.0;
    double dummy_init_rate = 0.01;
    int placement_id = 0;
    EA_placer.set_dummy_net_weight(dummy_init_weight, dummy_init_rate, dummy_init_weight);
    EA_placer.place(currentNode);

    currentNode.placement_id = placement_id;
    _nodeVec.clear();
    _nodeVec.push_back(currentNode);

    Placer curr_plc1(_nodeVec, opath, effort, drcInfo, hyper, select_in_ILP);

    currentNode = getNode(0);

    EA_placer.restore_MS(currentNode);

    currentNode.placement_id = placement_id;
    _nodeVec.clear();
    _nodeVec.push_back(currentNode);

    Placer curr_plc(_nodeVec, opath, effort, drcInfo, hyper, select_in_ILP);

    currentNode = getNode(0);

    EA_placer.break_merged_cc(currentNode);

    currentNode.placement_id = placement_id;
    _nodeVec.clear();
    _nodeVec.push_back(currentNode);

  } else {
    auto logger = spdlog::default_logger()->clone("placer.PlacerIfc.PlacerIfc");
    auto placer_begin = std::chrono::high_resolution_clock::now();
    Placer curr_plc(_nodeVec, opath, effort, drcInfo, hyper, select_in_ILP, ilp_solver);
    auto placer_end = std::chrono::high_resolution_clock::now();
    logger->debug("Block {0} placement runtime : {1}", _nodeVec.back().name, std::chrono::duration_cast<std::chrono::nanoseconds>(placer_end - placer_begin).count());
  }
}
