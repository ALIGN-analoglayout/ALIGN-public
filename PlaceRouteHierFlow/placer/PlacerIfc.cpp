
#include "../PnRDB/datatype.h"
#include "PlacerIfc.h"
#include "Placer.h"
#include "Pdatatype.h"
#include "../EA_placer/placement.h"
#include <chrono>

double Pdatatype::LAMBDA=1.;
double Pdatatype::GAMAR=30;
double Pdatatype::BETA=0.5;
double Pdatatype::SIGMA=1000;
double Pdatatype::PHI=0.05;
double Pdatatype::PI=0.05;
double Pdatatype::PII=1;

PlacerIfc::PlacerIfc(PnRDB::hierNode& currentNode, int numLayout, string opath, int effort, PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper) : _nodeVec( numLayout, currentNode) {
  Pdatatype::LAMBDA = hyper.LAMBDA;
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

    Placer curr_plc1(_nodeVec, opath, effort, drcInfo, hyper);

    currentNode = getNode(0);

    EA_placer.restore_MS(currentNode);

    currentNode.placement_id = placement_id;
    _nodeVec.clear();
    _nodeVec.push_back(currentNode);

    Placer curr_plc(_nodeVec, opath, effort, drcInfo, hyper);

    currentNode = getNode(0);

    EA_placer.break_merged_cc(currentNode);

    currentNode.placement_id = placement_id;
    _nodeVec.clear();
    _nodeVec.push_back(currentNode);

  } else {
    auto logger = spdlog::default_logger()->clone("placer.PlacerIfc.PlacerIfc");
    auto placer_begin = std::chrono::high_resolution_clock::now();
    Placer curr_plc(_nodeVec, opath, effort, drcInfo, hyper);
    auto placer_end = std::chrono::high_resolution_clock::now();
    logger->debug("Block {0} placement runtime : {1}", _nodeVec.back().name, std::chrono::duration_cast<std::chrono::nanoseconds>(placer_end - placer_begin).count());
  }
}
