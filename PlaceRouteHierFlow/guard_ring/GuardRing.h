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
    GuardRingDB::point wcell_ll;
    GuardRingDB::length wcell_size;
    GuardRingDB::length pcell_size;
    vector<GuardRingDB::point> stored_point;
  
  public:
    Pcell_info(int xs, int ys);
    Wcell_info(PnRDB::hierNode &node);
    GuardRing();

};

#endif

