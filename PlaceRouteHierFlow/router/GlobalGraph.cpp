#include "GlobalGraph.h"

#include "spdlog/spdlog.h"

GlobalGraph::GlobalGraph(GlobalGrid &grid) : path_number(1) {
  auto logger = spdlog::default_logger()->clone("router.GlobalGraph.GlobalGraph");

  // logger->debug("Start Creating adjacent list (graph)");
  CreateAdjacentList(grid);  // create adjacentList base gird.LL_graph and gird.UR_graph
  // logger->debug("End creating adjacent list (graph)");
};

void GlobalGraph::clearPath() { Path.clear(); };

void GlobalGraph::FindSTs(GlobalGrid &grid, int pathNo, std::vector<int> &stiner_node) {
  auto logger = spdlog::default_logger()->clone("router.GlobalGraph.FindSTs");

  this->path_number = pathNo;

  std::vector<std::vector<int> > temp_terminals = Pin_terminals;

  bool empty_flag = true;

  for(int i=0;i<temp_terminals.size();i++){
      if(temp_terminals[i].size()!=0){
          empty_flag = false;
       }
  }

  if(empty_flag) return;

  for (int i = 0; i < pathNo; ++i) {
    Pin_terminals = temp_terminals;

    std::vector<std::pair<int, int> > temp_path;
    // std::cout<<"Start iterate steiner"<<std::endl;
    Iterated_Steiner(grid, stiner_node);
    // std::cout<<"End iterate steiner"<<std::endl;
    int weight;

    MST(weight, temp_path, grid);
    // logger->debug("End MTS1");
    UpdateEdgeWeight(temp_path);
    // logger->debug("End Update weight");
    // return the shortest path
    Path.push_back(temp_path);
  }

  refreshWeight(grid);
};

void GlobalGraph::UpdateEdgeWeight(std::vector<std::pair<int, int> > temp_path) {
  int times = 2;

  for (unsigned int i = 0; i < temp_path.size(); i++) {
    for (unsigned int j = 0; j < graph[temp_path[i].first].list.size(); j++) {
      if (graph[temp_path[i].first].list[j].dest == temp_path[i].second) {
        graph[temp_path[i].first].list[j].weight = graph[temp_path[i].first].list[j].weight * times;
      }
    }

    for (unsigned int j = 0; j < graph[temp_path[i].second].list.size(); j++) {
      if (graph[temp_path[i].second].list[j].dest == temp_path[i].first) {
        graph[temp_path[i].second].list[j].weight = graph[temp_path[i].second].list[j].weight * times;
      }
    }
  }
};

void GlobalGraph::refreshWeight(GlobalGrid &grid) {
  for (unsigned int i = 0; i < graph.size() - 2; i++) {
    for (unsigned int j = 0; j < graph[i].list.size(); j++) {
      graph[i].list[j].weight = (double)abs(grid.tiles_total[graph[i].src].x - grid.tiles_total[graph[i].list[j].dest].x) +
                                abs(grid.tiles_total[graph[i].src].y - grid.tiles_total[graph[i].list[j].dest].y);
    }
  }
};

void GlobalGraph::Iterated_Steiner(GlobalGrid &grid, std::vector<int> &Pontential_Stiner_node) {
  int iterate_number = Pin_terminals.size() - 2;

  int LastWireLength = INT_MAX;

  int WireLength = INT_MAX;

  int Flag = 1;

  while (iterate_number > 0 && Flag) {
    int index = -1;

    GetWireLength(WireLength, index, Pontential_Stiner_node, grid);  // based on all pontential stinter node

    int DetailWireLength = LastWireLength - WireLength;

    if (DetailWireLength > 0) {
      LastWireLength = WireLength;

      AddStinerNodeToTerminals(Pontential_Stiner_node, index);

    } else {
      Flag = 0;
    }

    iterate_number = iterate_number - 1;

    // find a stiner node
  }
};

void GlobalGraph::AddStinerNodeToTerminals(std::vector<int> &Pontential_Stiner_node, int index) {
  std::vector<int> Potential_node;

  for (unsigned int i = 0; i < Pontential_Stiner_node.size(); i++) {
    if ((int)i == index) {
      std::vector<int> temp_pin;
      temp_pin.push_back(Pontential_Stiner_node[i]);
      Pin_terminals.push_back(temp_pin);

    } else {
      Potential_node.push_back(Pontential_Stiner_node[i]);
    }
  }

  Pontential_Stiner_node = Potential_node;
};

void GlobalGraph::GetWireLength(int &WireLength, int &index, std::vector<int> Pontential_Stiner_node, GlobalGrid &grid) {
  // separete those two teminals

  //  std::cout<<"Start Get WireLength"<<std::endl;

  int Last_WireLength = INT_MAX;

  for (unsigned int i = 0; i < Pontential_Stiner_node.size(); i++) {
    std::vector<int> temp_pin;
    temp_pin.push_back(Pontential_Stiner_node[i]);
    Pin_terminals.push_back(temp_pin);
    std::vector<pair<int, int> > temp_path;
    //      std::cout<<"Start MST"<<std::endl;
    MST(WireLength, temp_path, grid);
    //      std::cout<<"End MST"<<std::endl;
    if (WireLength < Last_WireLength) {
      Last_WireLength = WireLength;
      index = i;
    }
    Pin_terminals.pop_back();
  }

  //  std::cout<<"End Get WireLength"<<std::endl;
};

void GlobalGraph::InitialSrcDest(std::vector<int> &temp_src, std::vector<int> &temp_dest, std::vector<int> &pin_access) {
  std::set<int> src_set;
  std::set<int> dest_set;

  for (unsigned int i = 0; i < Pin_terminals.size(); i++) {
    // for(int j=0;j<Pin_terminals[i].size();j++){

    if (i == 0) {
      for (unsigned int j = 0; j < Pin_terminals[i].size(); j++) {
        src_set.insert(Pin_terminals[i][j]);
      }
      pin_access.push_back(1);
      // pin_access.push_back(0);
    } else {
      for (unsigned int j = 0; j < Pin_terminals[i].size(); j++) {
        dest_set.insert(Pin_terminals[i][j]);
      }
      pin_access.push_back(0);
    }
  }

  std::set<int>::iterator itlow, itup, xit;

  itup = src_set.end();
  itlow = src_set.begin();

  for (xit = itlow; xit != itup; ++xit) {
    temp_src.push_back(*xit);
  }

  itup = dest_set.end();
  itlow = dest_set.begin();

  for (xit = itlow; xit != itup; ++xit) {
    temp_dest.push_back(*xit);
  }
};

void GlobalGraph::ChangeSrcDest(std::vector<int> &temp_src, std::vector<int> &temp_dest, std::vector<int> temp_single_path, std::vector<int> &pin_access) {
  auto logger = spdlog::default_logger()->clone("router.GlobalGraph.ChangeSrcDest");

  for (unsigned int i = 0; i < temp_single_path.size(); i++) {
    for (unsigned int j = 0; j < Pin_terminals.size(); j++) {
      for (unsigned int k = 0; k < Pin_terminals[j].size(); k++) {
        if (temp_single_path[i] == Pin_terminals[j][k]) {
          pin_access[j] = 1;
        }
      }
    }
  }
  // logger->debug("ChangeSrcDest test1");
  temp_src.clear();
  temp_dest.clear();

  std::set<int> src_set;
  std::set<int> dest_set;

  for (unsigned int i = 0; i < pin_access.size(); i++) {
    if (pin_access[i] == 1) {
      for (unsigned int j = 0; j < Pin_terminals[i].size(); j++) {
        src_set.insert(Pin_terminals[i][j]);
      }
    } else {
      for (unsigned int j = 0; j < Pin_terminals[i].size(); j++) {
        dest_set.insert(Pin_terminals[i][j]);
      }
    }
  }
  // logger->debug("ChangeSrcDest test2");
  for (unsigned int i = 0; i < temp_single_path.size(); i++) {
    src_set.insert(temp_single_path[i]);
  }

  std::set<int>::iterator itlow, itup, xit;

  itup = src_set.end();
  itlow = src_set.begin();

  for (xit = itlow; xit != itup; ++xit) {
    temp_src.push_back(*xit);
  }

  itup = dest_set.end();
  itlow = dest_set.begin();

  for (xit = itlow; xit != itup; ++xit) {
    temp_dest.push_back(*xit);
  }
  // logger->debug("ChangeSrcDest test3");
};

void GlobalGraph::MST(int &WireLength, std::vector<pair<int, int> > &temp_path, GlobalGrid &grid) {
  auto logger = spdlog::default_logger()->clone("router.GlobalGraph.MST");

  std::vector<std::vector<int> > MST_path;
  std::vector<int> temp_src;
  std::vector<int> temp_dest;
  std::vector<int> pin_access;
  // logger->debug("Starting initialSrcDest");
  InitialSrcDest(temp_src, temp_dest, pin_access);
  // logger->debug("End initialSrcDest");
  // std::cout<<"temp_dest size "<<temp_dest.size()<<std::endl;

  if (temp_dest.size() == 0) {
    std::vector<int> MST_temp_path;
    MST_temp_path.push_back(temp_src[0]);
    // MST_temp_path.push_back(temp_src[0]);
    MST_path.push_back(MST_temp_path);
  }

  while (temp_dest.size() > 0) {
    // std::cout<<"temp_dest size "<<temp_dest.size()<<std::endl;
    std::vector<int> src_set = temp_src;
    std::vector<int> dest_set = temp_dest;
    SetSrcDest(src_set, dest_set);
    std::vector<int> temp_single_path = dijkstra(grid);
    MST_path.push_back(temp_single_path);
    RMSrcDest(src_set, dest_set);
    ChangeSrcDest(temp_src, temp_dest, temp_single_path, pin_access);
  }
  WireLength = Calculate_Weigt(MST_path);
  temp_path = Get_MST_Edges(MST_path);
};

int GlobalGraph::Calculate_Weigt(std::vector<std::vector<int> > temp_path) {
  int sum = 0;
  for (unsigned int i = 0; i < temp_path.size(); i++) {
    for (unsigned int j = 0; j < temp_path[i].size() - 1; j++) {
      for (unsigned int k = 0; k < graph[temp_path[i][j]].list.size(); k++) {
        if (graph[temp_path[i][j]].list[k].dest == temp_path[i][j + 1]) {
          sum = sum + graph[temp_path[i][j]].list[k].weight;
          break;
        }
      }
    }
  }

  return sum;
};

std::vector<std::pair<int, int> > GlobalGraph::Get_MST_Edges(std::vector<std::vector<int> > temp_path) {
  std::vector<std::pair<int, int> > temp_MST_Edges;
  std::pair<int, int> temp_Edge;

  for (unsigned int i = 0; i < temp_path.size(); i++) {
    if (temp_path[i].size() == 1) {
      temp_Edge.first = temp_path[i][0];
      temp_Edge.second = temp_path[i][0];
      temp_MST_Edges.push_back(temp_Edge);
    }

    for (int j = 0; j < (int)temp_path[i].size() - 1; j++) {
      temp_Edge.first = temp_path[i][j];
      temp_Edge.second = temp_path[i][j + 1];
      temp_MST_Edges.push_back(temp_Edge);
    }
  }

  return temp_MST_Edges;
};

void GlobalGraph::CreateAdjacentList(GlobalGrid &grid) {
  Node tempNode;
  Edge tempEdge;

  auto update_node = [&](int p, std::vector<RouterDB::tileEdge> &temp_vector) {
    for (unsigned int q = 0; q < temp_vector.size(); q++) {
      if (temp_vector[q].capacity > 0 && temp_vector[q].next != -1) {
        tempEdge.dest = temp_vector[q].next;
        tempEdge.weight =
            (double)abs(grid.tiles_total[p].y - grid.tiles_total[temp_vector[q].next].y) + abs(grid.tiles_total[p].x - grid.tiles_total[temp_vector[q].next].x);
        tempEdge.capacity = temp_vector[q].capacity;
        tempNode.list.push_back(tempEdge);
      }
    }
  };

  for (unsigned int i = 0; i < grid.tiles_total.size(); i++) {
    // Node tempNode;
    tempNode.list.clear();
    tempNode.src = i;
    // Edge tempEdge;

    update_node(i, grid.tiles_total[i].north);
    update_node(i, grid.tiles_total[i].south);
    update_node(i, grid.tiles_total[i].east);
    update_node(i, grid.tiles_total[i].west);
    update_node(i, grid.tiles_total[i].up);
    update_node(i, grid.tiles_total[i].down);

    graph.push_back(tempNode);
  }

  source = graph.size();
  dest = source + 1;

  Node tempNodeS;
  tempNodeS.src = source;
  graph.push_back(tempNodeS);

  Node tempNodeD;
  tempNodeD.src = dest;
  graph.push_back(tempNodeD);
};

void GlobalGraph::SetSrcDest(std::vector<int> temp_src, std::vector<int> temp_dest) {
  for (unsigned int i = 0; i < temp_src.size(); ++i) {
    // if(temp_src[i]<graph.size()-1){
    Edge tempEdge;
    tempEdge.dest = temp_src[i];
    tempEdge.weight = 0;
    graph[source].list.push_back(tempEdge);
    tempEdge.dest = source;
    graph[temp_src[i]].list.push_back(tempEdge);
    //}
    // std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
  }

  for (unsigned int i = 0; i < temp_dest.size(); ++i) {
    // if(temp_dest[i]<graph.size()-1){
    Edge tempEdge;
    tempEdge.dest = temp_dest[i];
    tempEdge.weight = 0;
    graph[dest].list.push_back(tempEdge);
    tempEdge.dest = dest;
    graph[temp_dest[i]].list.push_back(tempEdge);
    //}
    // std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
  }
};

void GlobalGraph::RMSrcDest(std::vector<int> temp_src, std::vector<int> temp_dest) {
  graph[source].list.clear();
  graph[dest].list.clear();

  for (unsigned int i = 0; i < temp_src.size(); ++i) {
    // if(temp_src[i]<graph.size()-1){
    graph[temp_src[i]].list.pop_back();
    //}
    // std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
  }

  for (unsigned int i = 0; i < temp_dest.size(); ++i) {
    // if(temp_dest[i]<graph.size()-1){
    graph[temp_dest[i]].list.pop_back();
    //}
    // std::cout<<"graph S "<<grid.vertices_graph[graph_index].x<<" "<<grid.vertices_graph[graph_index].y<<std::endl;
  }
};

void GlobalGraph::RemovefromMultMap(std::multimap<double, int> &mmap, double dist, int idx) {
  auto logger = spdlog::default_logger()->clone("router.GlobalGraph.RemovefromMultMap");

  std::multimap<double, int>::iterator low = mmap.lower_bound(dist);
  std::multimap<double, int>::iterator high = mmap.upper_bound(dist);
  std::multimap<double, int>::iterator tar;
  bool mark = false;
  for (tar = low; tar != high; ++tar) {
    if (tar->second == idx) {
      mark = true;
      break;
    }
  }
  if (mark) {
    mmap.erase(tar);
  } else {
    logger->warn("Graph-Info: cannot found element in map");
  }
}

void GlobalGraph::UpdateMultMap(std::multimap<double, int> &mmap, double olddist, int idx, double newdist) {
  this->RemovefromMultMap(mmap, olddist, idx);
  mmap.insert(std::pair<double, int>(newdist, idx));
}

std::vector<int> GlobalGraph::minDistancefromMultiMap(std::multimap<double, int> &mmap) {
  std::vector<int> min_index;
  std::multimap<double, int>::iterator miter = mmap.begin();
  double min = miter->first;
  std::multimap<double, int>::iterator low = mmap.lower_bound(min);
  std::multimap<double, int>::iterator high = mmap.upper_bound(min);
  for (std::multimap<double, int>::iterator it = low; it != high; ++it) {
    min_index.push_back(it->second);
  }
  return min_index;
};

std::vector<int> GlobalGraph::dijkstra(GlobalGrid &grid) {
  std::vector<int> temp_path;

  std::vector<double> dist;
  dist.resize(graph.size());
  // double dist[graph.size()];

  std::vector<int> parent;
  parent.resize(graph.size());
  // int parent[graph.size()];

  std::vector<int> status;
  status.resize(graph.size());
  // int status[graph.size()];

  std::multimap<double, int> distMap;

  for (unsigned int i = 0; i < graph.size(); ++i) {
    parent[i] = -1;
    dist[i] = INT_MAX;
    status[i] = 0;
  }

  dist[source] = 0;
  status[source] = 1;
  distMap.insert(std::pair<double, int>(dist[source], source));
  int count = 0;
  int v;
  while (status[dest] != 2 && count < (int)graph.size() - 1) {
    std::vector<int> ulist = minDistancefromMultiMap(distMap);
    // std::cout<<"size of Q: "<<ulist.size()<<std::endl;
    if (ulist.empty()) {
      temp_path.clear();
      return temp_path;
    }
    int u = ulist[0];
    RemovefromMultMap(distMap, dist[u], u);
    // std::cout<<"check u: "<<u<<" x: "<<grid.vertices_graph[u].x<<" y: "<<grid.vertices_graph[u].y <<std::endl;
    status[u] = 2;

    for (unsigned int j = 0; j < graph[u].list.size(); ++j) {
      v = graph[u].list[j].dest;
      if (v != u) {
        if (status[v] == 0) {
          parent[v] = u;
          dist[v] = dist[u] + graph[u].list[j].weight;
          status[v] = 1;
          distMap.insert(std::pair<double, int>(dist[v], v));
        } else if (status[v] == 1 && dist[v] > dist[u] + graph[u].list[j].weight) {
          parent[v] = u;
          double olddist = dist[v];
          dist[v] = dist[u] + graph[u].list[j].weight;
          UpdateMultMap(distMap, olddist, v, dist[v]);
        }
      }
    }
    count++;
  }

  printPath(parent, dest, graph.size(), temp_path);
  // std::cout<<"temp path"<<std::endl;
  // for(int i=0;i<temp_path.size();i++) {std::cout<<temp_path[i]<<" "<<std::endl;}
  return temp_path;
};

void GlobalGraph::printPath(std::vector<int> &parent, int j, int Vsize, std::vector<int> &temp_path) {
  if (j == -1) {
    return;
  }
  printPath(parent, parent[j], Vsize, temp_path);
  if (!(j == source || j == dest)) {
    temp_path.push_back(j);
    // std::cout<<"path push "<<j<<std::endl;
  }
}

std::vector<int> GlobalGraph::minDistance(double dist[], int status[], int V) {
  double min = INT_MAX;
  std::vector<int> min_index;
  for (int v = 0; v < V; ++v) {
    if (status[v] == 1)  // only fringe node
    {
      if (dist[v] < min) {
        min = dist[v];
        min_index.clear();
        min_index.push_back(v);
      } else if (dist[v] == min) {
        min_index.push_back(v);
      }
    }
  }

  return min_index;
};

void GlobalGraph::setTerminals(const std::vector<std::vector<int> > &t) { Pin_terminals = t; };

void GlobalGraph::setterminals(const std::vector<int> &t) { terminals = t; };

std::vector<std::vector<std::pair<int, int> > > GlobalGraph::returnPath() { return Path; };
