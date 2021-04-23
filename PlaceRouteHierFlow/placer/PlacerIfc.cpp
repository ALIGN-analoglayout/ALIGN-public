
#include "../PnRDB/datatype.h"
#include "PlacerIfc.h"
#include "Placer.h"

double ConstGraph::LAMBDA=1.;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=0.1;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=0.05;
double ConstGraph::PI=0.05;
double ConstGraph::PII=1;

PlacerIfc::PlacerIfc(PnRDB::hierNode& currentNode, int numLayout, string opath, int effort, PnRDB::Drc_info& drcInfo) : _nodeVec( numLayout, currentNode) {
  Placer curr_plc(_nodeVec,opath,effort,drcInfo);
}
