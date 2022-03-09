#ifndef GRID_H_
#define GRID_H_

#include <climits>
#include <cmath>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include "../PnRDB/datatype.h"
#include "GlobalGrid.h"
#include "Rdatatype.h"

class Grid {
  friend class Graph;
  friend class A_star;
  friend class GlobalGrid;
  friend class GcellDetailRouter;
  friend class PowerRouter;

  private:
  std::unordered_map<int, int> total2graph;      // mapping from total to graph vertices
  std::unordered_map<int, int> graph2total;      // mapping from graph to total vertices
  std::vector<RouterDB::vertex> vertices_total;  // vertex total list
  std::vector<RouterDB::vertex> vertices_total_full_connected;
  std::vector<RouterDB::vertex> vertices_graph;  // vertex list for graph
  std::vector<int> Start_index_metal_vertices;   // starting index in list for each metal layer
  std::vector<int> End_index_metal_vertices;     // ending index in list for each metal layer, if end<start, there is no list for the metal layer
  std::vector<int> Source;                       // index. result from setSrcDest()
  std::vector<int> Dest;                         // index. result from setSrcDest()
  std::vector<int> SourceGraph;
  std::vector<int> DestGraph;
  std::vector<int> x_unit;       // grid pitch in X axis, only for metal layers with vertical routing track
  std::vector<int> y_unit;       // grid pitch in Y axis, only for metal layers with horizotal routing track
  std::vector<int> x_min;        // min length in X axis, only for metal layer with horizontal routing track
  std::vector<int> y_min;        // min length in Y axis, only for metal layers with vertical routing track
  std::vector<int> routeDirect;  // routing direction
  RouterDB::point LL;            // Lower-left point of working die
  RouterDB::point UR;            // Upper-right point of working die
  RouterDB::point GridLL;        // Lower-left point of actual grid
  RouterDB::point GridUR;        // Upper-right point of actual grid
  std::vector<std::map<RouterDB::point, int, RouterDB::pointXYComp>> vertices_total_map;  // improve runtime of up/down edges - [wbxu: 20190505]
  // RouterDB::point LL_graph; //LL for create graph
  // RouterDB:;point UR_graph; //UR for create graph
  // vector<RouterDB::SinkData> Source; //what is the correct defination of Source and Dest?
  // vector<RouterDB::SinkData> Dest; //what is the correct defination of Source and Dest?
  PnRDB::Drc_info drc_info;         // Design rule information from technology file
  int lowest_metal, highest_metal;  // lower/upper bounds of available metal layers
  int grid_scale;                   // scaling of grids, 1 for detail router, >1 for global router
  int layerNo;                      // max layer number in technology file
  public:
  Grid(){};
  Grid(const Grid &other);
  Grid &operator=(const Grid &other);
  Grid(PnRDB::Drc_info &drc_info, RouterDB::point ll, RouterDB::point ur, int Lmetal, int Hmetal, int grid_scale);
  void CreateGridData();
  Grid(std::vector<std::vector<RouterDB::SinkData>> &SinkList, std::vector<RouterDB::Metal> &glb_path, PnRDB::Drc_info &drc_info, RouterDB::point ll,
       RouterDB::point ur, int Lmetal, int Hmetal, int grid_scale, int offset);
  Grid(GlobalGrid &GG, std::vector<std::pair<int, int>> &ST, PnRDB::Drc_info &drc_info, RouterDB::point ll, RouterDB::point ur, int Lmetal, int Hmetal,
       int grid_scale);

  void ReduceGrid(std::vector<RouterDB::vertex> &old_vertices, std::vector<RouterDB::vertex> &new_vertices, std::map<int, int> &old2new,
                  std::map<int, int> &new2old, std::vector<int> &old_source, std::vector<int> &old_dest, std::vector<int> &new_source,
                  std::vector<int> &new_dest, std::vector<int> &new_start, std::vector<int> &new_end, int LLx, int LLy, int URx, int URy,
                  std::vector<std::map<RouterDB::point, int, RouterDB::pointXYComp>> &new_vertices_map);
  void CreateGridCoreFunc(int Lmetal, int Hmetal, bool VFlag, RouterDB::point AreaLL, RouterDB::point AreaUR,
                          std::vector<RouterDB::vertex> &fake_vertices_total, std::vector<int> &fake_Start_index_metal_vertices,
                          std::vector<int> &fake_End_index_metal_vertices,
                          std::vector<std::map<RouterDB::point, int, RouterDB::pointXYComp>> &fake_vertices_total_map);
  void GetGlobalRouteRange(int mdx, int pLLx, int pLLy, int pURx, int pURy, int offset, RouterDB::point &gLL, RouterDB::point &gUR, int Lmetal, int Hmetal);
  void CollectPointSet(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &Vset, std::vector<std::set<RouterDB::point, RouterDB::pointYXComp>> &Hset,
                       int mdx, int pLLx, int pLLy, int pURx, int pURy, int Lmetal, int Hmetal);

  int gcd(int a, int b);
  void InactiveGlobalInternalMetal(std::vector<RouterDB::Block> &Blocks);
  void ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point>> &plist, int mIdx, int LLx, int LLy, int URx, int URy);
  void PrepareGraphVertices(int LLx, int LLy, int URx, int URy);
  void ActivateSourceDest();
  void InactivateSourceDest();
  void CheckVerticesTotal();
  void CheckMaptotal2graph();
  void CheckVerticesGraph();
  inline RouterDB::point GetGridLL() { return this->GridLL; };
  inline RouterDB::point GetGridUR() { return this->GridUR; };
  // Grid(Grid& globalGrid, LL, UR);
  // Grid(GlobalRouter & global);
  // Grid(DetailRouter & detail);
  // Grid(PowerRouter & power);
  // void UpdateLLURSD_global(GlobalRouter & global);
  // void UpdateLLURSD_detail(DetailRouter & detail);
  // void UpdateLLURSD_power(PowerRouter & power);
  // void createGrid();

  // added by yg
  std::vector<RouterDB::contact> setSrcDest(std::vector<RouterDB::SinkData> &Vsource, std::vector<RouterDB::SinkData> &Vdest, int width, int height,
                                            std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp> &Smap);  // return source & dest
  std::vector<RouterDB::contact> setSrcDest_detail(std::vector<RouterDB::SinkData> &Vsource, std::vector<RouterDB::SinkData> &Vdest, int width, int height,
                                                   std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp> &Smap);  // return source & dest
  std::vector<int> Mapping_function_pin(RouterDB::SinkData &source);
  std::vector<int> Mapping_function_pin_detail(RouterDB::SinkData &source);
  std::vector<int> Mapping_function_terminal(RouterDB::SinkData &source, int temp_metalIdx, int direction);
  std::vector<int> Mapping_function_stiner(RouterDB::SinkData &source, int temp_metalIdx);
  std::vector<int> Map_from_seg2gridseg_pin(RouterDB::SinkData &sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                            int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3);
  std::vector<int> Map_from_seg2gridseg_pin_detail(RouterDB::SinkData &sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                                   int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3);
  std::vector<int> Map_from_seg2gridseg_terminal(RouterDB::SinkData &sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                                 int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3, int range, int direction);
  std::vector<int> Map_from_seg2gridseg_stiner(RouterDB::SinkData &sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                               int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3, int range);
  std::vector<RouterDB::point> GetMaxMinSrcDest();
  void InactivePlist(std::vector<std::vector<RouterDB::DetailPoint>> &plist);
  // void InactivePointlist(std::vector<std::vector<RouterDB::point> > &plist);
  void InactivePointlist(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &plist);
  void InactivePointlist_Power(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &plist);
  void ActivePointlist(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &plist);
  int Find_EndIndex(int start_index, int direction);
  bool Check_Common_Part(int &start_index1, int &end_index1, int &start_index2, int &end_index2, int direction, int pitches_dis);
  void Full_Connected_Vertex();
  void Check_Full_Connection_Grid();
  bool CheckExtendable(int i, int metal);
  void CreatePlistSingleContact(std::vector<std::vector<RouterDB::point>> &plist, RouterDB::contact &Contacts);
  void InactivePointlist_via(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> &plist, bool up);
  int GetVerticesCount() { return vertices_total.size(); };
  void SetViaInactiveBox(std::vector<std::vector<int>> path, std::vector<std::pair<int, RouterDB::box>> &via_vec);
  void print_source_dest();
  void CreateGridData_new();
  // void inactive_node_global();
  // void inacitve_node_detail();
  // active or inactive node?
};

#endif
