
#include "../PnRDB/datatype.h"
#include "CapPlacerIfc.h"
#include "capplacer.h"

Placer_Router_Cap_Ifc::Placer_Router_Cap_Ifc(const string& opath, const string& fpath, PnRDB::hierNode & current_node, PnRDB::Drc_info &drc_info, const map<string, PnRDB::lefMacro> &lefData, bool aspect_ratio, int num_aspect) {
  _ptr = new Placer_Router_Cap(opath,fpath,current_node,drc_info,lefData,aspect_ratio,num_aspect);
}

Placer_Router_Cap_Ifc::~Placer_Router_Cap_Ifc() {
  delete _ptr;
}
