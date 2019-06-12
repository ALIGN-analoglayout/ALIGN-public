#include "GlobalGrid.h"

GlobalGrid(PnRDB::Drc_info& drc_info, int URx, int URy, int Lmetal, int Hmetal, int tileLayerNo) {
  this->lowest_metal=Lmetal;
  this->highest_metal=Hmetal;
  for(int i=this->lowest_metal; i<=this->highest_metal; i+=tileLayerNo) {
  }
}
