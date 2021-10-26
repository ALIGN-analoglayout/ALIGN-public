#ifndef GDATATYPE_H_
#define GDATATYPE_H_

#include <vector>
#include <limits.h>
#include <string>

namespace GuardRingDB {

struct point;
struct dimension;

struct point {
  int x=0;
  int y=0;
}; 

struct dimension {
  int width=0;    //x-axis
  int height=0;   //y-axis
};

} // namespace GuardRingDB
#endif

