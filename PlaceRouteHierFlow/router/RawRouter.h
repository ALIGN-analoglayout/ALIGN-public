#ifndef RAWROUTER_H_
#define RAWROUTER_H_

#include <algorithm>  // std::set_intersection, std::sort
#include <iostream>
#include <set>
#include <string>
#include <vector>

#include "../PnRDB/datatype.h"
#include "Rdatatype.h"

class RawRouter {
  protected:
  std::vector<RouterDB::Net> Nets;
  std::vector<RouterDB::Block> Blocks;
  std::vector<RouterDB::terminal> Terminals;
  std::vector<RouterDB::PowerNet> PowerNets;
  bool terminal_routing;
  RouterDB::PowerGrid Vdd_grid;
  RouterDB::PowerGrid Gnd_grid;
  RouterDB::point LL;  // LL for entire node
  RouterDB::point UR;  // UR for entire node
  // RouterDB::point LL_graph; //LL for create graph
  // RouterDB::point UR_graph; //UR for create graph
  // std::vector<RouterDB::SinkData> Source; //what is the correct defination o    f Source and Dest?
  // std::vector<RouterDB::SinkData> Dest; //what is the correct defination of     Source and Dest?
  int path_number;  // number candidate path
  PnRDB::Drc_info drc_info;
  PnRDB::Drc_info cross_layer_drc_info;
  int lowest_metal, highest_metal;  // index of lowest metal & highest metal
  int grid_scale;                   // dynamic grid_scal
  bool isTop;
  int width, height;
  std::string topName;
  int layerNo;
  std::vector<int> Minlength_ViaLength_Diff;

  public:
  RawRouter();
  // void GetShorestPath(Graph& graph);//return the shortest path to Nets
  std::set<int> CheckOverlap(std::vector<RouterDB::SegPiece>& splist, int LLx, int LLy, int URx, int URy);
  void InsertPlistToSet_x(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, std::vector<std::vector<RouterDB::point>>& plist);
  std::vector<std::vector<RouterDB::point>> FindPlist(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, RouterDB::point LL, RouterDB::point UR);
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> FindsetPlist(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, RouterDB::point LL,
                                                                             RouterDB::point UR);
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> Plist2Set(std::vector<std::vector<RouterDB::point>>& plist);
  void InsertPlistToSet(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>>& Set, std::vector<std::vector<RouterDB::point>>& plist);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Findset(std::set<RouterDB::SinkData, RouterDB::SinkDataComp>& Set_x, RouterDB::point LL,
                                                               RouterDB::point UR);
  std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp> findviaset(std::set<std::pair<int, RouterDB::point>, RouterDB::pointSetComp>& Pset_via,
                                                                               RouterDB::point LL, RouterDB::point UR);
};
#endif
