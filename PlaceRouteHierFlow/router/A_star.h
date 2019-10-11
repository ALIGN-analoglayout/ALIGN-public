#ifndef A_STAR_H_
#define A_STAR_H_

#include <climits>
#include <vector>
#include <string>
#include <set>
#include "Grid.h"
#include "Rdatatype.h"
#include "../PnRDB/datatype.h"

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
    void initial_source(Grid& grid, std::set<std::pair<int,int>, RouterDB::pairComp>& L_list, const std::set<int> &S_or_D, int left_up, int right_down);
    bool expand_node(std::vector<int> &direction, std::vector<int> &temp_node, Grid &grid);
    bool expand_node_ud(int direction, std::vector<int> &temp_node, Grid &grid);
    bool found_near_node(int left_up, int right_down, int current_node, Grid &grid, std::vector<int> &candidate_node, std::set<int> dest_set);
    bool found_near_node_S(int left_up, int right_down, int current_node, Grid &grid, std::vector<int> &candidate_node, std::set<int> src_set, std::set<int> dest_set);
    std::vector<int> A_star_algorithm(Grid& grid, int left_up, int right_down);
    bool Check_Parallel_SD(int left_up, int right_down, int node_index, std::vector<int> &left_up_node, std::vector<int> &right_down_node, Grid& gird, std::set<int> S_or_D);
    bool Check_Parallel_Rule(int left_up, int right_down, int node_index, std::vector<int> &left_up_node, std::vector<int> &right_down_node, Grid& gird);
    void Search_direction(int nodeS, int nodeD, Grid& grid, int &v_search, int &h_search);
    bool L_shape_Connection(int nodeS, int nodeD, Grid& grid);
    bool Check_Connection_Rule(std::vector<int> &left_up1, std::vector<int> &right_up1, std::vector<int> &left_up2, std::vector<int> &right_up2, Grid& grid);
    bool Check_S_Connection_L(std::vector<int> &left_up_node, std::vector<int> &right_down_node, std::set<int> &src_set, Grid &grid);
    bool Check_S_Connection( std::vector<int> &left_up_node, std::vector<int> &right_down_node, std::set<int> &src_set, Grid &grid);
    //bool found_near_node_S(int left_up, int right_down, int current_node, Grid &grid, std::vector<int> &candidate_node, std::set<int> src_set, std::set<int> dest_set);
    std::vector<std::vector<RouterDB::Metal> > ConvertPathintoPhysical(Grid& grid);
    void CopyPath(Grid& grid, int left_up, int right_down);
    void Right_path(std::vector<int> &temp_path, Grid& grid, int number, std::vector<int> &left_path);
    void Left_path(std::vector<int> &temp_path, Grid& grid, int number, std::vector<int> &left_path);
    void XY_search(int start_point, int end_point, std::vector<int>& left_path, bool down_up, Grid &grid);
    void YX_search(int start_point, int end_point, std::vector<int>& left_path, bool down_up, Grid &grid);
    void Down_up_path(int end_index, Grid& grid, int down_up, std::vector<int>& path);
    void left_path_SD(int end_index, int number, Grid& grid, std::vector<int>& path);
    void right_path_SD(int end_index, int number, Grid& grid, std::vector<int>& path);
    void CovertToShieldingNet(Grid& grid, std::vector<int> &real_path, std::vector<int> &temp_path);
    void refreshGrid(Grid& grid);
};

#endif
