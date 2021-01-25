#ifndef PLACERIFC_H_
#define PLACERIFC_H_

class Placer;

class PlacerIfc {
  private:
    std::vector<PnRDB::hierNode> _nodeVec;
  public:
    PlacerIfc(PnRDB::hierNode& currentNode, int numLayout, string opath, int effort, PnRDB::Drc_info& drcInfo);
    std::vector<PnRDB::hierNode>& get() { return _nodeVec; }
    PnRDB::hierNode& getNode( int idx) { return _nodeVec.at(idx); }
};

#endif
