#ifndef PLACERIFC_H_
#define PLACERIFC_H_

class Placer;

class PlacerIfc {
  private:
    Placer* _ptr;
  public:
    PlacerIfc(PnRDB::hierNode& node, string opath, int effort, PnRDB::Drc_info& drcInfo);
    PlacerIfc(std::vector<PnRDB::hierNode>& nodeVec, string opath, int effort, PnRDB::Drc_info& drcInfo);
    ~PlacerIfc();
    Placer* get() { return _ptr;}; 
};

#endif
