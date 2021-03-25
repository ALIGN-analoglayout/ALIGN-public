
#include <gtest/gtest.h>
#include <string>
#include <iostream>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/Router.h"
#include "./cap_placer/capplacer.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <sstream>

using std::string;
using std::cout;
using std::endl;

using namespace nlohmann;

TEST(PnRTest, True) {
  EXPECT_TRUE( 1);
};

namespace PnRDB {
  // Need to declare this (within the namespace); implementation in PnRDB/PnRDBJSON.cpp
  void to_json( json& j, const PnRDB::hierNode& hN);
};


static void generic_router_test( const string& topcell, const string& tag, int mode0, int mode1, int mode2)
{
  string dfile="FinFET_Mock_PDK_Abstraction.json";
  string binary_directory = "./";

  PnRdatabase DB("gold", topcell, "", "", "", dfile);

  PnRDB::Drc_info drc_info=DB.getDrc_info();

  PnRDB::hierNode current_node;
  DB.ReadDBJSON( current_node, "gold/" + topcell + "_0.pre_" + tag + ".db.json");

  EXPECT_EQ( current_node.name, topcell);

  int h_skip_factor = 5;
  int v_skip_factor = 5;

  Router curr_route;
  string dummyfile;
  curr_route.RouteWork( mode0, current_node, const_cast<PnRDB::Drc_info&>(drc_info), mode1, mode2, binary_directory, h_skip_factor, v_skip_factor, dummyfile);

  PnRDB::hierNode post_current_node;
  DB.ReadDBJSON( post_current_node, "gold/" + topcell + "_0.post_" + tag + ".db.json");

  EXPECT_EQ( json(current_node), json(post_current_node));
}

double ConstGraph::LAMBDA=1000;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=100;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=1500;
double ConstGraph::PI=1500;
double ConstGraph::PII=1500;

static void generic_placer_test( const string& topcell)
{
  string dfile="FinFET_Mock_PDK_Abstraction.json";
  string binary_directory = "./";
  string opath = "cand/";

  PnRdatabase DB("gold", topcell, "", "", "", dfile);
  PnRDB::Drc_info drc_info=DB.getDrc_info();
  PnRDB::hierNode current_node;
  DB.ReadDBJSON( current_node, "gold/" + topcell + ".pre_pl.db.json");

  EXPECT_EQ( current_node.name, topcell);

  std::vector<PnRDB::hierNode> nodeVec(1, current_node);
  Placer curr_plc( nodeVec, opath, 0, drc_info);

  PnRDB::hierNode post_current_node;
  DB.ReadDBJSON( post_current_node, "gold/" + topcell + "_0.post_pl.db.json");

  EXPECT_EQ( json( nodeVec[0]), json(post_current_node));
}


static void generic_placer_router_cap_test( const string& topcell) 
{
  string fpath = "gold";

  string dfile="layers.json";
  string binary_directory = "./";
  string opath = "./Results/";

  PnRdatabase DB("gold", topcell, "", "switched_capacitor_filter.lef", "", dfile);

  PnRDB::Drc_info drcInfo=DB.getDrc_info();
  map<string, PnRDB::lefMacro> lefData = DB.checkoutSingleLEF();

  PnRDB::hierNode current_node;
  DB.ReadDBJSON( current_node, "gold/" + topcell + ".pre_prc" + ".db.json");

  EXPECT_EQ( current_node.name, topcell);

  DB.AddingPowerPins(current_node);
  Placer_Router_Cap PRC(opath, fpath, current_node, drcInfo, lefData, 1, 6); //dummy, aspect ratio, number of aspect retio

  DB.WriteDBJSON( current_node, "cand/" + topcell + ".post_prc" + ".db.json");

  PnRDB::hierNode post_current_node;
  DB.ReadDBJSON( post_current_node, "gold/" + topcell + ".post_prc" + ".db.json");

  EXPECT_EQ( json( current_node), json(post_current_node));
};

/*
TEST(PnRTest, Placer_Router_Cap_telescopic_ota) {
  generic_placer_router_cap_test( "telescopic_ota");
}

TEST(PnRTest, Placer_Router_Cap_switched_capacitor_filter) {
  generic_placer_router_cap_test( "switched_capacitor_filter");
}


TEST(PnRTest, Placer_telescopic_ota) {
  generic_placer_test( "telescopic_ota");
};

TEST(PnRTest, Placer_switched_capacitor_filter) {
  generic_placer_test( "switched_capacitor_filter");
};

TEST(PnRTest, GlobalRouter_telescopic_ota) {
  generic_router_test( "telescopic_ota", "gr", 4, 1, 6);
};

TEST(PnRTest, DetailedRouter_telescopic_ota) {
  generic_router_test( "telescopic_ota", "dr", 5, 1, 6);
};

TEST(PnRTest, GlobalRouter_switched_capacitor_filter) {
  generic_router_test( "switched_capacitor_filter", "gr", 4, 1, 6);
};

TEST(PnRTest, DetailedRouter_switched_capacitor_filter) {
  generic_router_test( "switched_capacitor_filter", "dr", 5, 1, 6);
};
*/
