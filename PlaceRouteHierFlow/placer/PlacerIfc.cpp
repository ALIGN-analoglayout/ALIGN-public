
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

PlacerIfc::PlacerIfc(PnRDB::hierNode& node, string opath, int effort, PnRDB::Drc_info& drcInfo) {
  _ptr = new Placer(node,opath,effort,drcInfo);
}

PlacerIfc::PlacerIfc(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo) {
  _ptr = new Placer(nodeVec,opath,effort,drcInfo);
}

PlacerIfc::~PlacerIfc() {
  delete _ptr;
}
