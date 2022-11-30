#ifndef A_STAR_H_
#define A_STAR_H_

#include <assert.h>
#include <limits.h>

#include <algorithm>
#include <climits>
#include <set>
#include <string>
#include <vector>

#include "../PnRDB/datatype.h"
#include "Grid.h"
#include "Rdatatype.h"

class A_star {
  // friend class Grid;
  // friend class GlobalRouter;
  // friend class DetailRouter;

  private:
  vector<int> source, dest;
  bool shielding = -1;
  std::vector<std::vector<int>> Path;
  std::vector<std::vector<int>> Extend_labels;
  int path_number;
  PnRDB::Drc_info drc_info;

  public:
  A_star(Grid &grid, bool shielding);
  bool FindFeasiblePath(Grid &grid, int pathNo, int left_up, int right_down);
  int Manhattan_distan(int sindex, Grid &grid);
  void initial_source(Grid &grid, std::set<std::pair<double, int>, RouterDB::pairCompDBL> &L_list, std::vector<int> &source);
  bool expand_node(std::vector<int> &direction, std::vector<int> &temp_node, Grid &grid);
  bool find_nodes_north(Grid &grid, int node, int number, std::vector<int> &temp_nodes);
  bool find_nodes_east(Grid &grid, int node, int number, std::vector<int> &temp_nodes);
  bool find_nodes_south(Grid &grid, int node, int number, std::vector<int> &temp_nodes);
  bool find_nodes_west(Grid &grid, int node, int number, std::vector<int> &temp_nodes);
  bool found_near_node(int current_node, Grid &grid, std::vector<int> &candidate_node);
  bool Check_Src_Dest(std::vector<int> &nodes, std::set<int> &src_dest);
  bool find_succsive_parallel_node(Grid &grid, int current_node, int left, int right, int mode, std::vector<int> &nodes, std::set<int> &src_index, int &cost);
  bool parallel_routing(Grid &grid, int current_node, int next_node, int left, int right, std::set<int> &source_index, std::set<int> &dest_index,
                        std::vector<std::vector<int>> &node_L_path, int &cost);
  bool L_shape_Connection(Grid &grid, std::vector<int> &start_points, std::vector<int> &end_points, std::vector<std::vector<int>> &node_L_path);
  bool L_shape_Connection_Check(Grid &grid, int start_points, int end_points, std::vector<int> &node_set);
  int find_next_node(Grid &grid, int current_node, int x, int y, int layer, int dummy_layer);
  bool Check_activa_via_active(Grid &grid, std::vector<int> &nodes);
  bool Extention_checks(Grid &grid, std::vector<int> &nodes, std::set<int> &source_index);
  bool Extention_check(Grid &grid, int current_node, std::set<int> &source_index);
  bool Extention_check_prime(Grid &grid, int current_node, int next_node, std::set<int> &source_index);
  std::vector<std::vector<int>> A_star_algorithm(Grid &grid, int left_up, int right_down);
  std::vector<std::vector<int>> Trace_Back_Paths(Grid &grid, int current_node, int left, int right, std::set<int> &src_index, std::set<int> &dest_index);
  std::vector<int> Trace_Back_Path_parent(Grid &grid, int current_node, std::set<int> &src_index);
  std::vector<int> Trace_Back_Path_trace_back_node(Grid &grid, int current_node, std::set<int> &src_index);
  std::vector<std::vector<RouterDB::Metal>> ConvertPathintoPhysical(Grid &grid);
  std::vector<int> CovertToShieldingNet(Grid &grid, std::vector<int> &temp_path);
  void refreshGrid(Grid &grid);
  bool CheckExendable_With_Certain_Length(int first_node_same_layer, int current_node, int length, int minL, Grid &grid);
  bool CheckExendable_With_Certain_Length_Head_Extend(int first_node_same_layer, int current_node, int length, int minL, Grid &grid, int &direction);
  bool CheckExendable_With_Certain_Length_Tail_Extend(int first_node_same_layer, int current_node, int length, int minL, Grid &grid, int &direction);

  int trace_back_node(int current_node, Grid &grid, std::set<int> &source_index);
  int trace_back_node_parent(int current_node, Grid &grid, std::set<int> &source_index);
  std::vector<std::vector<int>> GetPath();
  bool expand_node_ud(int direction, std::vector<int> &temp_node, Grid &grid);
  void erase_candidate_node(std::set<int> &Close_set, std::vector<int> &candidate);
  bool Pre_trace_back(Grid &grid, int current_node, int left, int right, std::set<int> &src_index, std::set<int> &dest_index);
  void rm_cycle_path(std::vector<std::vector<int>> &Node_Path);
  void lable_father(Grid &grid, std::vector<std::vector<int>> &Node_Path);
  void compact_path(std::vector<std::vector<int>> &Node_Path);
  void print_path();
  bool Check_Path_Extension(Grid &grid, std::vector<std::vector<int>> &node_path, std::set<int> &source_index);
  int Calculate_Interval_number(Grid &grid, int node);
  int Find_Symmetry_cost(Grid &grid, int current_node, RouterDB::Metal &temp_path);
  int Find_Symmetry_Cost(Grid &grid, int current_node, vector<RouterDB::Metal> &sym_path);
  std::vector<std::vector<int>> A_star_algorithm_Sym(Grid &grid, int left_up, int right_down, vector<RouterDB::Metal> &sym_path);
  bool FindFeasiblePath_sym(Grid &grid, int pathNo, int left_up, int right_down, std::vector<RouterDB::Metal> &sym_path);
  std::vector<std::vector<int>> GetExtendLabel();
  std::vector<int> extend_manner_direction_check(std::vector<int> temp_path, Grid &grid);
};

#endif
