#ifndef GuardRingIfc_H_
#define GuardRingIfc_H_

#include "../PnRDB/datatype.h"

class GuardRing;

class GuardRingIfc {
  private:
  GuardRing* _ptr;

  public:
  GuardRingIfc(PnRDB::hierNode& node, const map<string, PnRDB::lefMacro>& lefData, const PnRDB::Drc_info& drc_info, const string& fpath);
  ~GuardRingIfc();
  GuardRing* get() const { return _ptr; }
};

#endif
