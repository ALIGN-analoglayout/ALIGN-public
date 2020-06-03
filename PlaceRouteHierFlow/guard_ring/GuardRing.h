#ifndef GuardRing_H_
#define GuardRing_H_

#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <assert.h>
#include <sstream>
#include <set>
#include <cmath>
#include <algorithm>
#include <limits.h>
#include <bitset>
#include <cstdlib> // system
#include <iterator>
#include <cctype>
#include <unistd.h> // getcwd
#include <map>
#include <set>
#include <utility>//std::pair, make_pair
#include "Gdatatype.h"
#include "../PnRDB/datatype.h"

class GuardRing {

  private:
    GuardRingDB::point temp_point;
  
  public:
    GuardRing();
    GuardRing(PnRDB::hierNode &node);

};

#endif

