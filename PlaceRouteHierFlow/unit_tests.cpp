
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


static void generic_test( const string& topcell, const string& tag, int mode0, int mode1, int mode2)
{
  string dfile="FinFET_Mock_PDK_Abstraction.json";
  string binary_directory = "./";

  PnRdatabase DB("gold", topcell, "", "", "", dfile);

  PnRDB::Drc_info drc_info=DB.getDrc_info();

  PnRDB::hierNode current_node;
  DB.ReadDBJSON( current_node, "gold/" + topcell + "_0.pre_" + tag + ".db.json");

  EXPECT_EQ( current_node.name, topcell);

  Router curr_route;
  curr_route.RouteWork( mode0, current_node, const_cast<PnRDB::Drc_info&>(drc_info), mode1, mode2, binary_directory);

  PnRDB::hierNode post_current_node;
  DB.ReadDBJSON( post_current_node, "gold/" + topcell + "_0.post_" + tag + ".db.json");

  EXPECT_EQ( json(current_node), json(post_current_node));
}

TEST(PnRTest, GlobalRouter_telescopic_ota) {
  generic_test( "telescopic_ota", "gr", 4, 1, 6);
};

TEST(PnRTest, DetailedRouter_telescopic_ota) {
  generic_test( "telescopic_ota", "dr", 5, 1, 6);
};

TEST(PnRTest, GlobalRouter_switched_capacitor_combination) {
  generic_test( "switched_capacitor_combination", "gr", 4, 1, 6);
};

TEST(PnRTest, DetailedRouter_switched_capacitor_combination) {
  generic_test( "switched_capacitor_combination", "dr", 5, 1, 6);
};

TEST(PnRTest, GlobalRouter_switched_capacitor_filter) {
  generic_test( "switched_capacitor_filter", "gr", 4, 1, 6);
};

TEST(PnRTest, DetailedRouter_switched_capacitor_filter) {
  generic_test( "switched_capacitor_filter", "dr", 5, 1, 6);
};
