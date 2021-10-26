#include "GuardRing.h"

int main(){
  PnRDB::hierNode testnode;
  testnode.LL.x = 0;
  testnode.LL.y = 0;
  testnode.UR.x = 10;
  testnode.UR.y = 10;

  GuardRing test(0,0,2,2,testnode);
  return 0;

};