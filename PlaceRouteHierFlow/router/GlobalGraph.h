#ifndef GLOBALGRAPH_H_
#define GLOBALGRAPH_H_

#include <climits>
#include <set>
#include <string>
#include <vector>

#include "../PnRDB/datatype.h"
#include "GlobalGrid.h"
#include "Rdatatype.h"

class GlobalGraph {
  // friend class Grid;
  friend class GcellGlobalRouter;
  // friend class DetailRouter;

  private:
  // 1. From grid, create graph, remove the edge whose capacity is 0
  // 2. Find candidates for different net: iterated-1-stinter algorithm
  //     2.1  n^2 node to explore stiner node, maybe 3-d
  //     2.2  MST to find stiner node
  //     2.3  Finally generate different candidates
  // 3. return candidates, a set of index of Edges

  struct Edge {
    int dest, weight, capacity;
  };

  struct Node {
    int src;
    std::vector<int> metal_layer;
    bool active = true;
    std::vector<Edge> list;
  };

  std::vector<int> terminals;
  std::vector<std::vector<int> > Pin_terminals;
  int source, dest;
  std::vector<Node> graph;
  std::vector<std::vector<std::pair<int, int> > > Path;  // index of Edge, MST of mutil-pin net; mutil candidates
  int path_number;
  void RemovefromMultMap(std::multimap<double, int> &mmap, double dist, int idx);
  void UpdateMultMap(std::multimap<double, int> &mmap, double olddist, int idx, double newdist);
  std::vector<int> minDistancefromMultiMap(std::multimap<double, int> &mmap);

  public:
  GlobalGraph(GlobalGrid &grid);
  void FindSTs(GlobalGrid &grid, int pathNo, std::vector<int> &stiner_node);  // use grid information to find shortest path;
  void CreateAdjacentList(GlobalGrid &grid);                                  // based on LL_graph and UR_graph
  std::vector<int> dijkstra(GlobalGrid &grid);                                // return path
  std::vector<int> dijkstraRetire(GlobalGrid &grid);                          // return path
  void UpdateEdgeWeight(std::vector<std::pair<int, int> > temp_path);
  void refreshWeight(GlobalGrid &grid);
  void ChangeSrcDest(std::vector<int> &temp_src, std::vector<int> &temp_dest, std::vector<int> temp_single_path, std::vector<int> &pin_access);
  void Iterated_Steiner(GlobalGrid &grid, std::vector<int> &stiner_node);
  void AddStinerNodeToTerminals(std::vector<int> &Pontential_Stiner_node, int index);
  // std::vector<int> Get_Potential_Steiner_node(GlobalGrid &grid);
  void GetWireLength(int &WireLength, int &index, std::vector<int> Pontential_Stiner_node, GlobalGrid &grid);
  void MST(int &WireLength, std::vector<pair<int, int> > &temp_path, GlobalGrid &grid);
  int Calculate_Weight(std::vector<std::vector<int> > temp_path);
  std::vector<std::pair<int, int> > Get_MST_Edges(std::vector<std::vector<int> > temp_path);
  void SetSrcDest(std::vector<int> temp_src, std::vector<int> temp_dest);
  void RMSrcDest(std::vector<int> temp_src, std::vector<int> temp_dest);
  void printPath(std::vector<int> &parent, int j, int Vsize, std::vector<int> &temp_path);
  std::vector<int> minDistance(double dist[], int status[], int V);
  void setTerminals(const std::vector<std::vector<int> > &t);
  void setterminals(const std::vector<int> &t);
  std::vector<std::vector<std::pair<int, int> > > returnPath();
  void InitialSrcDest(std::vector<int> &temp_src, std::vector<int> &temp_dest, std::vector<int> &pin_access);
  void clearPath();
  void select_layers(int l_metal, int h_metal);
  void refresh_layers();
  void CreateAdjacentList_New(GlobalGrid &grid, int l_metal, int h_metal);
  // void Path_graph_total(GlobalGrid& grid, std::vector<int> &temp_path);
};

#endif
