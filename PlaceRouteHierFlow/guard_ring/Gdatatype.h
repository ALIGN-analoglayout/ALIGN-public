#ifndef GDATATYPE_H_
#define GDATATYPE_H_

#include <vector>
#include <limits.h>
#include <string>

namespace GuardRingDB {

struct point;
struct length;

struct point {
  int x=0;
  int y=0;
}; 

struct length {
  int xs=0;
  int ys=0;
}

} // namespace GuardRingDB
#endif

