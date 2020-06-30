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
    GuardRingDB::point shift;
  
  public:
    void Pcell_info(int pcell_width, int pcell_height);
    void Wcell_info(PnRDB::hierNode &node);
    GuardRing(int Minimal_x, int Minimal_y, int pcell_width, int pcell_height, PnRDB::hierNode &node);
    PnRDB::hierNode returnhierNode(PnRDB::hierNode &node);
    void gnuplot();
    void movepoint(PnRDB::point &point);
    void movebbox (PnRDB::bbox &bbox);
    void movecontact(PnRDB::contact &contact);
    void moveblock(PnRDB::block &block);
    void moveterminal(PnRDB::terminal &terminal);
    void movenet(PnRDB::net &net);
    void movemetal(PnRDB::Metal &metal);
    void movevia(PnRDB::Via &via);
    void movepin(PnRDB::pin &pin);
    void movepowernet(PnRDB::PowerNet &powernet);
    void moveveccontact(std::vector<PnRDB::contact> &contactvector);
    void movevecvia(std::vector<PnRDB::Via> &vecvia);
    void movevecpin(std::vector<PnRDB::pin> &vecpin);
    void movevecpowernet(std::vector<PnRDB::PowerNet> &vecpowernet);
    void movevecmetal(std::vector<PnRDB::Metal> &vecmetal);
    void movevecblockcomplex(std::vector<PnRDB::blockComplex> &vecbc);
    
};

#endif

