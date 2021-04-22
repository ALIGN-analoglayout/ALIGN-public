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
#ifdef WINDOWS
#include <Windows.h> // getcwd
#else
#include <unistd.h> // getcwd
#endif
#include <map>
#include <set>
#include <utility>//std::pair, make_pair
#include <stdlib.h>
#include "Gdatatype.h"
#include "../PnRDB/datatype.h"
#include "spdlog/spdlog.h"

class GuardRing {

  private:
    string pcellpinmetal;                       //primitive cell pin metal layer
    GuardRingDB::point temp_point;              //temporary point to save guard ring primitive cell
    GuardRingDB::point wcell_ll;                //wrapped cell lower left coordinate
    GuardRingDB::point wcell_ur;                //wrapped cell upper right coordinate
    GuardRingDB::dimension wcell_size;          //wrapped cell dimension in width and height
    GuardRingDB::dimension pcell_metal_size;    //metal layer in guard ring primitive cell dimension in width and height
    GuardRingDB::dimension pcell_size;          //guard ring primitive cell dimension in width and height
    GuardRingDB::dimension offset;              //offset(lower left coordinate) between Metal layer and FEOL layer of guard ring primitive cell 
    GuardRingDB::dimension minimal_PC;          //offset(upper right coordinate) between Metal layer and FEOL layer of guard ring primitive cell 
    GuardRingDB::dimension minimal;             //minimal space between metal layer of guard ring primitive cell to the wrapped cell
    vector<GuardRingDB::point> stored_point_ll; //stored lower left coordinate of guard ring primitive cells
    vector<GuardRingDB::point> stored_point_ur; //stored upper right coordinate of guard ring primitive cells
    vector<GuardRingDB::point> stored_pin_ll; //stored lower left coordinate of pin of guard ring primitive cells
    vector<GuardRingDB::point> stored_pin_ur; //stored upper right coordinate of pin of guard ring primitive cells
    GuardRingDB::point shift;                   //shift vector to move wrapped cell
    PnRDB::GuardRing temp_gr;
    string path;
  
  public:
    void Pcell_info(const map<string, PnRDB::lefMacro>& lefData); //read from lef file and set guard ring primitive cell width and height information       
    void Wcell_info(PnRDB::hierNode &node); //read from hierarchy node and set wrapped cell lower left & upper right coordinate and width & height
    void DRC_Read(const PnRDB::Drc_info& drc_info); //read drc info to obtain minimal space requirement
    GuardRing(PnRDB::hierNode &node, const map<string, PnRDB::lefMacro>& lefData, const PnRDB::Drc_info& drc_info, const string& fpath); //main function
    void storegrhierNode(PnRDB::hierNode &node, const string& fpath); //return hierarchy node with guard ring information
    PnRDB::hierNode movehierNode(PnRDB::hierNode &node); //move hierarchy node to make sure lower left coordinate to (0,0)
    void gnuplot(); //gnuplot function for plotting hierarchical node
    //functions to move each element of node: Start
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
    //functions to move each element of node: End
    
};

#endif

