#ifndef A_STAR_H_
#define A_STAR_H_

#include <climits>
#include <vector>
#include <string>
#include <set>
#include <assert.h>
#include "Grid.h"
#include "Rdatatype.h"
#include "../PnRDB/datatype.h"
#include <algorithm>

class A_star {

  //friend class Grid;
  //friend class GlobalRouter;
  //friend class DetailRouter;

  private:

    vector<int> source, dest;
    bool shielding=-1;
    std::vector<std::vector<int> > Path;
    int path_number;
    PnRDB::Drc_info drc_info;

  public:
    A_star(Grid& grid, bool shielding);
    bool FindFeasiblePath(Grid& grid, int pathNo, int left_up, int right_down);
    int Manhattan_distan(int sindex, Grid& grid);
    void initial_source(Grid& grid, std::set<std::pair<int,int>, RouterDB::pairComp>& L_list, std::vector<int> &source);
    bool expand_node(std::vector<int> &direction, std::vector<int> &temp_node, Grid &grid);
    bool find_nodes_north(Grid& grid, int node, int number, std::vector<int>& temp_nodes);
    bool find_nodes_east(Grid& grid, int node, int number, std::vector<int>& temp_nodes);
    bool find_nodes_south(Grid& grid, int node, int number, std::vector<int>& temp_nodes);
    bool find_nodes_west(Grid& grid, int node, int number, std::vector<int>& temp_nodes);
    bool found_near_node(int current_node, Grid &grid, std::vector<int> &candidate_node);
    bool Check_Src_Dest(std::vector<int> &nodes, std::set<int> &src_dest);
    bool find_succsive_parallel_node(Grid& grid, int current_node, int left, int right, int mode, std::vector<int> &nodes, std::set<int> &src_index, std::set<int> &dest_index);
    bool parallel_routing(Grid& grid, int current_node, int next_node, int left, int right, std::set<int> &source_index, std::set<int> &dest_index);
    bool L_shape_Connection(Grid& grid, std::vector<int> &start_points, std::vector<int> &end_points);
    bool L_shape_Connection_Check(Grid& grid, int start_points, int end_points);
    int find_next_node( Grid& grid, int current_node, int x, int y, int layer, int dummy_layer);
    bool Check_activa_via_active(Grid& grid, std::vector<int> &nodes);
    bool Extention_checks(Grid& grid, std::vector<int> &nodes);
    bool Extention_check(Grid& grid, int current_node);
    std::vector<std::vector<int> > A_star_algorithm(Grid& grid, int left_up, int right_down);
    std::vector<std::vector<int> > Trace_Back_Paths(Grid& grid, int current_node, int left, int right, std::set<int> &src_index, std::set<int> &dest_index);
    std::vector<int> Trace_Back_Path(Grid& grid, int current_node);
    std::vector<std::vector<RouterDB::Metal> > ConvertPathintoPhysical(Grid& grid);
    std::vector<int> CovertToShieldingNet(Grid& grid, std::vector<int> &temp_path);
    void refreshGrid(Grid& grid);
    bool CheckExendable_With_Certain_Length(int first_node_same_layer,int current_node,int length,int minL,Grid &grid);
    int trace_back_node(int current_node, Grid& grid);
    std::vector<std::vector<int>> GetPath();
    bool expand_node_ud(int direction, std::vector<int> &temp_node, Grid &grid);
};

#endif
