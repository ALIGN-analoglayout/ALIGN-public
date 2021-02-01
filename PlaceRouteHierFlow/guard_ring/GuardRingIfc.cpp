#include "../PnRDB/datatype.h"
#include "GuardRingIfc.h"
#include "GuardRing.h"

GuardRingIfc::GuardRingIfc(PnRDB::hierNode &node, const map<string, PnRDB::lefMacro>& lefData, const PnRDB::Drc_info& drc_info) {
  _ptr = new GuardRing(node, lefData, drc_info);
}

GuardRingIfc::~GuardRingIfc() {
  delete _ptr;
}
