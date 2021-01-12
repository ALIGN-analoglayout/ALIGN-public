#ifndef GRAPH_H_
#define GRAPH_H_

#include <climits>
#include <vector>
#include <string>
#include <set>
#include "Grid.h"
#include "Rdatatype.h"
#include "../PnRDB/datatype.h"

class Graph {

  //friend class Grid;
  //friend class GlobalRouter;
  //friend class DetailRouter;

  private:

    struct Edge {
      int dest, weight;
    };

    struct Node {
      int src;
      std::vector<Edge> list;
    };
    int source, dest;
    std::vector<Node> graph;
    std::vector<std::vector<int> > Path;
    //std::vector<std::vector<RouterDB::Metal> > Phsical_Path; //how to get phsical_path, DRC_info is needed.
    //Grid grid;
    int path_number;

    RouterDB::PowerGrid Vdd_grid;
    RouterDB::PowerGrid Gnd_grid;
    void RemovefromMultMap(std::multimap<double, int>& mmap, double dist, int idx);
    void UpdateMultMap(std::multimap<double, int>& mmap, double olddist, int idx, double newdist);
    std::vector<int> minDistancefromMultiMap(std::multimap<double, int> &mmap);

  public:
    Graph(Grid& grid);
    Graph(Grid& grid, bool power_grid);
    Graph(Grid& grid, int pathNo); //use grid information to find shortest path;

    Graph(std::vector<std::pair<int,int> > &global_path, std::vector<std::vector<int> > &conectedTile, std::vector<int> &Tile_Source, std::vector<int> &Tile_Dest);
    void CreateAdjacentList_Global_Path(std::vector<std::pair<int,int> > &global_path, std::vector<std::vector<int> > &conectedTile, std::vector<int> &Tile_Source, std::vector<int> &Tile_Dest,   std::map<int,int> &tile_graph_map,std::map<int,int> &graph_tile_map);

    bool FindFeasiblePath(Grid& grid, int pathNo);
    RouterDB::PowerGrid GetVdd_grid(){return Vdd_grid;};
    RouterDB::PowerGrid GetGnd_grid(){return Gnd_grid;};
    void CreatePower_Grid(Grid& grid);

    void CreateAdjacentList(Grid& grid); //based on LL_graph and UR_graph
    std::vector<int> dijkstra(); // return path
    std::vector<int> dijkstraRetire(Grid& grid); // return path
    void UpdateEdgeWeight(std::vector<int>& path);
    void printPath(std::vector<int> &parent, int j, int Vsize, std::vector<int> & temp_path);
    std::vector<int> minDistance(std::vector<double> &dist, std::vector<int> &status, int V);
    //void UpdateEdgeWeight(std::vector<int>& path);
    void Path_graph_total(Grid& grid, std::vector<int> &temp_path);
    //vector<RouterDB:Metal> Get_Physical_Path(vector<int>& path);
    std::vector<std::vector<int> > GetShorestPath();
    std::vector<std::vector<RouterDB::Metal> > ConvertPathintoPhysical(Grid& grid);
    bool CheckActive(Grid& grid, int index);
    void power_grid_dsf(Grid& grid, int i, int graph_index, int& connection_graph_number, int power);
    void Connection_Check_Power_Grid(Grid& grid, int power);
    void collect_nodes(Grid &grid, vector<int> temp_vector, vector<int>& adjacent_nodes, int power);
    void collect_node(Grid &grid, int temp_vector, vector<int>& adjacent_nodes, int power);
};

#endif
