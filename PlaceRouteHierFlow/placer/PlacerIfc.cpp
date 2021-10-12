
#include "../PnRDB/datatype.h"
#include "PlacerIfc.h"
#include "Placer.h"
#include "../EA_placer/placement.h"

double ConstGraph::LAMBDA=1.;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=0.1;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=0.05;
double ConstGraph::PI=0.05;
double ConstGraph::PII=1;

PlacerIfc::PlacerIfc(PnRDB::hierNode& currentNode, int numLayout, string opath, int effort, PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper, bool select_in_ILP = false) : _nodeVec( numLayout, currentNode) {
  ConstGraph::LAMBDA = hyper.LAMBDA;
  if (hyper.use_analytical_placer) {

/*
 * From PR text
 * I don't know what these values should be:
 *      dummy_init_weight, dummy_init_rate, placement_id
 *
    clock_t start, end;
    start = clock();
    // EA placer
    if(disable_io)std::cout.setstate(std::ios_base::failbit);
    Placement EA_placer;
    EA_placer.set_dummy_net_weight(dummy_init_weight,dummy_init_rate,dummy_init_weight);
    EA_placer.place(current_node);
    //EA_placer.place_ut(current_node);
    if(disable_io)std::cout.clear();
    current_node.placement_id = placement_id;
    PlacerIfc curr_plc1(current_node, numLayout, opath, effort, const_cast<PnRDB::Drc_info&>(drcInfo));  // do placement and update data in current node
    current_node = curr_plc1.getNode(0);
    // AFTER FIRST ILP, RUN THE FOLLOWING LINE
    if(disable_io)std::cout.setstate(std::ios_base::failbit);
    EA_placer.restore_MS(current_node);
    // Do the ILP again
    if(disable_io)std::cout.clear();
    current_node.placement_id = placement_id;
    PlacerIfc curr_plc(current_node, numLayout, opath, effort, const_cast<PnRDB::Drc_info&>(drcInfo)); // do placement and update data in current node
    current_node = curr_plc.getNode(0);
    if(disable_io)std::cout.setstate(std::ios_base::failbit);
    EA_placer.break_merged_cc(current_node);
    if(disable_io)std::cout.clear();
    end = clock();
    logger->info("Placement runtime: {0} s", (double)(end - start) / CLOCKS_PER_SEC);
    // return 0;
    // Placement
    std::vector<PnRDB::hierNode> nodeVec={current_node};
    logger->debug("Checkpoint: generated {0} placements", nodeVec.size());
*/

    Placement EA_placer;
    EA_placer.place(currentNode);
    double dummy_init_weight = 1.0;
    double dummy_init_rate   = 0.01;
    EA_placer.set_dummy_net_weight(dummy_init_weight,dummy_init_rate,dummy_init_weight);

  } else {
    Placer curr_plc(_nodeVec,opath,effort,drcInfo,hyper, select_in_ILP);
  }
}
