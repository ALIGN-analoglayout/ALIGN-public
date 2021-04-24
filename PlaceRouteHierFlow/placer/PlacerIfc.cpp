
#include "../PnRDB/datatype.h"
#include "PlacerIfc.h"
#include "Placer.h"

double ConstGraph::LAMBDA=1000;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=100;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=1500;
double ConstGraph::PI=1500;
double ConstGraph::PII=1500;

PlacerIfc::PlacerIfc(PnRDB::hierNode& currentNode, int numLayout, string opath, int effort, PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper) : _nodeVec( numLayout, currentNode) {
  Placer curr_plc(_nodeVec,opath,effort,drcInfo,hyper);
}
