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

//1. From grid, create graph, remove the edge whose capacity is 0
//2. Find candidates for different net: iterated-1-stinter algorithm
//     2.1  n^2 node to explore stiner node, maybe 3-d
//     2.2  MST to find stiner node
//     2.3  Finally generate different candidates
//3. return candidates, a set of index of Edges
    
    struct Edge {
      int dest, weight, capacity;
    };

    struct Node {
      int src;
      std::vector<Edge> list;
    };

    std::vector<Edge> total_Edge;     

    //int source, dest;
    std::vector<Node> graph;
    std::vector<std::vector<int>> Path; //index of Edge, MST of mutil-pin net; mutil candidates

    //std::vector<std::vector<int> > Path;
    //std::vector<std::vector<RouterDB::Metal> > Phsical_Path; //how to get phsical_path, DRC_info is needed.
    //Grid grid;
    //int path_number;

    //RouterDB::PowerGrid Vdd_grid;
    //RouterDB::PowerGrid Gnd_grid;

/*
  public:
    Graph(Grid& grid);
    Graph(Grid& grid, bool power_grid);
    Graph(Grid& grid, int pathNo); //use grid information to find shortest path;
    bool FindFeasiblePath(Grid& grid, int pathNo);
    RouterDB::PowerGrid GetVdd_grid(){return Vdd_grid;};
    RouterDB::PowerGrid GetGnd_grid(){return Gnd_grid;};
    void CreatePower_Grid(Grid& grid);

    void CreateAdjacentList(Grid& grid); //based on LL_graph and UR_graph
    std::vector<int> dijkstra(Grid& grid); // return path
    void UpdateEdgeWeight(std::vector<int>& path);
    void printPath(int parent[], int j, int Vsize, std::vector<int> & temp_path);
    std::vector<int> minDistance(double dist[], int status[], int V);
    //void UpdateEdgeWeight(std::vector<int>& path);
    void Path_graph_total(Grid& grid, std::vector<int> &temp_path);
    //vector<RouterDB:Metal> Get_Physical_Path(vector<int>& path);
    std::vector<std::vector<int> > GetShorestPath();
    std::vector<std::vector<RouterDB::Metal> > ConvertPathintoPhysical(Grid& grid);
*/
};

#endif
