#include "GuardRingIfc.h"

#include "../PnRDB/datatype.h"
#include "GuardRing.h"

GuardRingIfc::GuardRingIfc(PnRDB::hierNode& node, const map<string, PnRDB::lefMacro>& lefData, const PnRDB::Drc_info& drc_info, const string& fpath) {
  _ptr = new GuardRing(node, lefData, drc_info, fpath);
}

GuardRingIfc::~GuardRingIfc() { delete _ptr; }
