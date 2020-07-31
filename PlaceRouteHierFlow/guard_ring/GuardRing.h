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
    GuardRingDB::dimension offset;
    GuardRingDB::dimension minimal_PC;
    GuardRingDB::dimension minimal;
    vector<GuardRingDB::point> stored_point_ll;
    vector<GuardRingDB::point> stored_point_ur;
    GuardRingDB::point shift;
    PnRDB::GuardRing temp_gr;
  
  public:
    void Pcell_info(const map<string, PnRDB::lefMacro>& lefData);
    void Wcell_info(PnRDB::hierNode &node);
    void DRC_Read(const PnRDB::Drc_info& drc_info);
    GuardRing(PnRDB::hierNode &node, const map<string, PnRDB::lefMacro>& lefData, const PnRDB::Drc_info& drc_info);
    void storegrhierNode(PnRDB::hierNode &node);
    PnRDB::hierNode movehierNode(PnRDB::hierNode &node);
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

