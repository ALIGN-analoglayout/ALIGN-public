#ifndef PLACERIFC_H_
#define PLACERIFC_H_

#include "PlacerHyperparameters.h"

class Placer;

class PlacerIfc {
  private:
  std::vector<PnRDB::hierNode> _nodeVec;

  public:
  PlacerIfc(PnRDB::hierNode& currentNode, int numLayout, string opath, int effort, PnRDB::Drc_info& drcInfo, const PlacerHyperparameters& hyper,
            bool select_in_ILP);
  std::vector<PnRDB::hierNode>& get() { return _nodeVec; }
  int getNodeVecSize() const { return _nodeVec.size(); }
  PnRDB::hierNode& getNode(int idx) { return _nodeVec.at(idx); }
};

#endif
