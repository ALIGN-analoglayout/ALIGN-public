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
#include <stdlib.h>
#include "Gdatatype.h"
#include "../PnRDB/datatype.h"

class GuardRing {

  private:
    GuardRingDB::point temp_point;
    GuardRingDB::point wcell_ll;
    GuardRingDB::point wcell_ur;
    GuardRingDB::dimension wcell_size;
    GuardRingDB::dimension pcell_size;
    vector<GuardRingDB::point> stored_point_ll;
    vector<GuardRingDB::point> stored_point_ur;
  
  public:
    void Pcell_info(int pcell_width, int pcell_length);
    void Wcell_info(PnRDB::hierNode &node);
    GuardRing(int Minimal_x, int Minimal_y, PnRDB::hierNode &node);
    void gnuplot();
};

#endif

