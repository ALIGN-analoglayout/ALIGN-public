#include "Grid.h"

#include <cassert>

#include "spdlog/spdlog.h"

Grid::Grid(const Grid& other)
    : total2graph(other.total2graph),
      graph2total(other.graph2total),
      vertices_total(other.vertices_total),
      vertices_graph(other.vertices_graph),
      Start_index_metal_vertices(other.Start_index_metal_vertices),
      End_index_metal_vertices(other.End_index_metal_vertices),
      Source(other.Source),
      Dest(other.Dest),
      x_unit(other.x_unit),
      y_unit(other.y_unit),
      x_min(other.x_min),
      y_min(other.y_min),
      routeDirect(other.routeDirect),
      LL(other.LL),
      UR(other.UR),
      GridLL(other.GridLL),
      GridUR(other.GridUR),
      vertices_total_map(other.vertices_total_map),
      drc_info(other.drc_info),
      lowest_metal(other.lowest_metal),
      highest_metal(other.highest_metal),
      grid_scale(other.grid_scale),
      layerNo(other.layerNo){};
// Grid::Grid(const Grid& other) {
//  this->total2graph=other.total2graph;
//  this->graph2total=other.graph2total;
//  this->vertices_total=other.vertices_total;
//  this->Start_index_metal_vertices=other.Start_index_metal_vertices;
//  this->End_index_metal_vertices=other.End_index_metal_vertices;
//  this->Source=other.Source;
//  this->Dest=other.Dest;
//  this->x_unit=other.x_unit;
//  this->y_unit=other.y_unit;
//  this->x_min= other.x_min;
//  this->y_min= other.y_min;
//  this->routeDirect=other.routeDirect;
//  this->LL=other.LL;
//  this->UR=other.UR;
//  this->GridLL=other.GridLL;
//  this->GridUR=other.GridUR;
//  this->drc_info=other.drc_info;
//  this->lowest_metal=other.lowest_metal;
//  this->highest_metal=other.highest_metal;
//  this->grid_scale=other.grid_scale;
//  this->layerNo=other.layerNo;
//  this->vertices_total_map=other.vertices_total_map;
//}

Grid& Grid::operator=(const Grid& other) {
  this->total2graph = other.total2graph;
  this->graph2total = other.graph2total;
  this->vertices_total = other.vertices_total;
  this->vertices_graph = other.vertices_graph;
  this->Start_index_metal_vertices = other.Start_index_metal_vertices;
  this->End_index_metal_vertices = other.End_index_metal_vertices;
  this->Source = other.Source;
  this->Dest = other.Dest;
  this->x_unit = other.x_unit;
  this->y_unit = other.y_unit;
  this->x_min = other.x_min;
  this->y_min = other.y_min;
  this->routeDirect = other.routeDirect;
  this->LL = other.LL;
  this->UR = other.UR;
  this->GridLL = other.GridLL;
  this->GridUR = other.GridUR;
  this->drc_info = other.drc_info;
  this->lowest_metal = other.lowest_metal;
  this->highest_metal = other.highest_metal;
  this->grid_scale = other.grid_scale;
  this->layerNo = other.layerNo;
  this->vertices_total_map = other.vertices_total_map;
  return *this;
}

void Grid::CreateGridData() {
  std::ofstream matlabfile;
  matlabfile.open("Grid.txt");

  auto write_out_matlab_file = [&](const auto& p, const auto& q) {
    matlabfile << vertices_total[p].x;
    matlabfile << " ";
    matlabfile << vertices_total[p].y;
    matlabfile << " ";
    matlabfile << vertices_total[p].metal;
    matlabfile << " ";

    matlabfile << vertices_total[q].x;
    matlabfile << " ";
    matlabfile << vertices_total[q].y;
    matlabfile << " ";
    matlabfile << vertices_total[q].metal;
    matlabfile << " ";

    matlabfile << std::endl;
  };

  for (unsigned int i = 0; i < vertices_total.size(); i++) {
    for (unsigned int j = 0; j < vertices_total[i].north.size(); j++) {
      if (vertices_total[i].active && vertices_total[vertices_total[i].north[j]].active) {
        write_out_matlab_file(i, vertices_total[i].north[j]);
      }
    }

    for (unsigned int j = 0; j < vertices_total[i].south.size(); j++) {
      if (vertices_total[i].active && vertices_total[vertices_total[i].south[j]].active) {
        write_out_matlab_file(i, vertices_total[i].south[j]);
      }
    }

    for (unsigned int j = 0; j < vertices_total[i].west.size(); j++) {
      if (vertices_total[i].active && vertices_total[vertices_total[i].west[j]].active) {
        write_out_matlab_file(i, vertices_total[i].west[j]);
      }
    }

    for (unsigned int j = 0; j < vertices_total[i].east.size(); j++) {
      if (vertices_total[i].active && vertices_total[vertices_total[i].east[j]].active) {
        write_out_matlab_file(i, vertices_total[i].east[j]);
      }
    }

    for (int j = 0; j < 1; j++) {
      if (vertices_total[i].up != -1 && vertices_total[i].active && vertices_total[vertices_total[i].up].active) {
        write_out_matlab_file(i, vertices_total[i].up);
      }
    }

    for (int j = 0; j < 1; j++) {
      if (vertices_total[i].down != -1 && vertices_total[i].active && vertices_total[vertices_total[i].down].active) {
        write_out_matlab_file(i, vertices_total[i].down);
      }
    }
  }

  for (unsigned int i = 0; i < Source.size(); i++) {
    write_out_matlab_file(Source[i], Source[i]);
  }

  for (unsigned int i = 0; i < Dest.size(); i++) {
    write_out_matlab_file(Dest[i], Dest[i]);
  }

  matlabfile.close();

  std::ofstream matlabfile_via;
  matlabfile_via.open("Grid_via.txt");

  auto write_out_matlab_file_via = [&](const auto& p, const int& via_index) {
    matlabfile_via << vertices_total[p].x;
    matlabfile_via << " ";
    matlabfile_via << vertices_total[p].y;
    matlabfile_via << " ";
    matlabfile_via << vertices_total[p].metal;
    matlabfile_via << " ";
    matlabfile_via << via_index;

    matlabfile_via << std::endl;
  };

  for (unsigned int i = 0; i < vertices_total.size(); i++) {
    // std::cout<<"vertices_total "<<i<<" "<<vertices_total[i].active<<" "<<vertices_total[i].x<<" "<<vertices_total[i].y<<" "<<vertices_total[i].metal<<"
    // "<<vertices_total[i].down<<" "<<vertices_total[i].via_active_down<<" "<<vertices_total[i].up<<" "<< vertices_total[i].via_active_up<<std::endl;
    if (vertices_total[i].active and (vertices_total[i].down != -1 and vertices_total[i].via_active_down) and
        (vertices_total[i].up != -1 and vertices_total[i].via_active_up))
      write_out_matlab_file_via(i, 1);
    if (vertices_total[i].active and (vertices_total[i].down != -1 and vertices_total[i].via_active_down) and
        !(vertices_total[i].up != -1 and vertices_total[i].via_active_up))
      write_out_matlab_file_via(i, 2);
    if (vertices_total[i].active and !(vertices_total[i].down != -1 and vertices_total[i].via_active_down) and
        (vertices_total[i].up != -1 and vertices_total[i].via_active_up))
      write_out_matlab_file_via(i, 3);
  }

  matlabfile_via.close();
}

void Grid::CreateGridData_new() {
  std::ofstream matlabfile;
  matlabfile.open("Grid_new.txt");

  auto write_out_matlab_file = [&](const auto& p, auto index) {  // index 0 grid, index 1 src/dest
    matlabfile << vertices_total[p].x;
    matlabfile << " ";
    matlabfile << vertices_total[p].y;
    matlabfile << " ";
    matlabfile << vertices_total[p].metal;
    matlabfile << " ";
    matlabfile << index;
    matlabfile << std::endl;
  };

  for (unsigned int i = 0; i < vertices_total.size(); i++) {
    if (vertices_total[i].active) {
      write_out_matlab_file(i, 0);
    }
  }

  for (unsigned int i = 0; i < Source.size(); i++) {
    write_out_matlab_file(Source[i], 1);
  }

  for (unsigned int i = 0; i < Dest.size(); i++) {
    write_out_matlab_file(Dest[i], 1);
  }

  matlabfile.close();

  std::ofstream matlabfile_via;
  matlabfile_via.open("Grid_via_new.txt");

  auto write_out_matlab_file_via = [&](const auto& p, const int& via_index) {
    matlabfile_via << vertices_total[p].x;
    matlabfile_via << " ";
    matlabfile_via << vertices_total[p].y;
    matlabfile_via << " ";
    matlabfile_via << vertices_total[p].metal;
    matlabfile_via << " ";
    matlabfile_via << via_index;

    matlabfile_via << std::endl;
  };

  for (unsigned int i = 0; i < vertices_total.size(); i++) {
    // std::cout<<"vertices_total "<<i<<" "<<vertices_total[i].active<<" "<<vertices_total[i].x<<" "<<vertices_total[i].y<<" "<<vertices_total[i].metal<<"
    // "<<vertices_total[i].down<<" "<<vertices_total[i].via_active_down<<" "<<vertices_total[i].up<<" "<< vertices_total[i].via_active_up<<std::endl;
    if (vertices_total[i].active and (vertices_total[i].down != -1 and vertices_total[i].via_active_down) and
        (vertices_total[i].up != -1 and vertices_total[i].via_active_up))
      write_out_matlab_file_via(i, 1);
    if (vertices_total[i].active and (vertices_total[i].down != -1 and vertices_total[i].via_active_down) and
        !(vertices_total[i].up != -1 and vertices_total[i].via_active_up))
      write_out_matlab_file_via(i, 2);
    if (vertices_total[i].active and !(vertices_total[i].down != -1 and vertices_total[i].via_active_down) and
        (vertices_total[i].up != -1 and vertices_total[i].via_active_up))
      write_out_matlab_file_via(i, 3);
  }

  matlabfile_via.close();
}

void Grid::print_source_dest() {
  for (unsigned int i = 0; i < Source.size(); i++) {
    int p = Source[i];
    std::cout << "source " << p << " " << vertices_total[p].x << " " << vertices_total[p].y << " " << vertices_total[p].metal << " " << vertices_total[p].active
              << " " << vertices_total[p].up << " " << vertices_total[p].via_active_up << " " << vertices_total[p].down << " "
              << vertices_total[p].via_active_down << std::endl;
  }

  for (unsigned int i = 0; i < Dest.size(); i++) {
    int p = Dest[i];
    std::cout << "dest " << p << " " << vertices_total[p].x << " " << vertices_total[p].y << " " << vertices_total[p].metal << " " << vertices_total[p].active
              << " " << vertices_total[p].up << " " << vertices_total[p].via_active_up << " " << vertices_total[p].down << " "
              << vertices_total[p].via_active_down << std::endl;
  }
}

int Grid::gcd(int a, int b)  // get greatest common divider of two integers
{
  if (b == 0) return a;
  return gcd(b, a % b);
}

void Grid::InactivePointlist(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>>& plist) {
  for (std::vector<RouterDB::vertex>::iterator it = this->vertices_total.begin(); it != this->vertices_total.end(); ++it) {
    int mm = it->metal;
    RouterDB::point p;
    p.x = it->x;
    p.y = it->y;
    if (plist.at(mm).find(p) != plist.at(mm).end()) {
      it->active = false;
    }
  }
}

void Grid::InactivePointlist_via(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>>& plist, bool up) {
  if (up) {
    for (std::vector<RouterDB::vertex>::iterator it = this->vertices_total.begin(); it != this->vertices_total.end(); ++it) {
      int mm = it->metal;
      RouterDB::point p;
      p.x = it->x;
      p.y = it->y;
      if (plist.at(mm).find(p) != plist.at(mm).end()) {
        it->via_active_up = false;
      }
    }
  } else {
    for (std::vector<RouterDB::vertex>::iterator it = this->vertices_total.begin(); it != this->vertices_total.end(); ++it) {
      int mm = it->metal;
      RouterDB::point p;
      p.x = it->x;
      p.y = it->y;
      if (plist.at(mm).find(p) != plist.at(mm).end()) {
        it->via_active_down = false;
      }
    }
  }
}

void Grid::InactivePointlist_Power(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>>& plist) {
  for (std::vector<RouterDB::vertex>::iterator it = this->vertices_total.begin(); it != this->vertices_total.end(); ++it) {
    int mm = it->metal;
    RouterDB::point p;
    p.x = it->x;
    p.y = it->y;
    if (plist.at(mm).find(p) != plist.at(mm).end()) {
      it->active = false;
    }
  }
}

void Grid::ActivePointlist(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>>& plist) {
  for (std::vector<RouterDB::vertex>::iterator it = this->vertices_total.begin(); it != this->vertices_total.end(); ++it) {
    int mm = it->metal;
    RouterDB::point p;
    p.x = it->x;
    p.y = it->y;
    if (plist.at(mm).find(p) != plist.at(mm).end()) {
      it->active = true;
    }
  }
}

Grid::Grid(std::vector<std::vector<RouterDB::SinkData>>& SinkList, std::vector<RouterDB::Metal>& glb_path, PnRDB::Drc_info& drc_info, RouterDB::point ll,
           RouterDB::point ur, int Lmetal, int Hmetal, int grid_scale, int offset)
    : LL(ll), UR(ur) {
  auto logger = spdlog::default_logger()->clone("router.Grid.Grid");

  // 1. Initialize member variables I
  // this->LL=ll;
  // this->UR=ur;
  this->lowest_metal = Lmetal;
  this->highest_metal = Hmetal;
  this->grid_scale = grid_scale;
  this->layerNo = drc_info.Metal_info.size();
  this->Start_index_metal_vertices.resize(this->layerNo, 0);
  this->End_index_metal_vertices.resize(this->layerNo, -1);
  this->routeDirect.resize(this->layerNo);
  this->vertices_total.clear();
  this->drc_info = drc_info;
  // 2. Define member variables II
  this->x_unit.resize(this->layerNo, 0);
  this->y_unit.resize(this->layerNo, 0);
  this->x_min.resize(this->layerNo, 0);
  this->y_min.resize(this->layerNo, 0);
  this->vertices_total_map.clear();
  this->vertices_total_map.resize(this->layerNo);  // improve runtime of up/down edges - [wbxu: 20190505]
  // 3. Calculate grid unit and min length for each layer
  for (int i = 0; i < this->layerNo; i++) {
    // this->Start_index_metal_vertices.at(i)=0;
    // this->End_index_metal_vertices.at(i)=-1;
    this->routeDirect.at(i) = drc_info.Metal_info.at(i).direct;
    if (drc_info.Metal_info.at(i).direct == 0) {  // vertical
      this->x_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_x * grid_scale;
      this->y_min.at(i) = this->x_unit.at(i) / 2;
    } else if (drc_info.Metal_info.at(i).direct == 1) {  // horizontal
      this->y_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_y * grid_scale;
      this->x_min.at(i) = this->y_unit.at(i) / 2;
    } else {
      logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
      continue;
    }
  }
  // 4. Collect the vertices around global routes and block pins
  int mdx, pLLx, pLLy, pURx, pURy;
  int layer_offset = 2;  // offset to configure how many layers can be chosen for new grids in each metal contact
  this->GridLL.x = INT_MAX;
  this->GridLL.y = INT_MAX;
  this->GridUR.x = INT_MIN;
  this->GridUR.y = INT_MIN;
  std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>> Vset;
  std::vector<std::set<RouterDB::point, RouterDB::pointYXComp>> Hset;
  Vset.resize(this->layerNo);
  Hset.resize(this->layerNo);
  for (std::vector<std::vector<RouterDB::SinkData>>::iterator it = SinkList.begin(); it != SinkList.end(); ++it) {
    // for each pin
    for (std::vector<RouterDB::SinkData>::iterator it2 = it->begin(); it2 != it->end(); ++it2) {
      // for each pin contact
      mdx = it2->metalIdx;
      RouterDB::point gLL, gUR;
      pLLx = INT_MAX;
      pLLy = INT_MAX;
      pURx = INT_MIN;
      pURy = INT_MIN;
      for (std::vector<RouterDB::point>::iterator it3 = it2->coord.begin(); it3 != it2->coord.end(); ++it3) {
        if (pLLx > it3->x) pLLx = it3->x;
        if (pLLy > it3->y) pLLy = it3->y;
        if (pURx < it3->x) pURx = it3->x;
        if (pURy < it3->y) pURy = it3->y;
      }
      GetGlobalRouteRange(mdx, pLLx, pLLy, pURx, pURy, offset, gLL, gUR, this->lowest_metal, this->highest_metal);
      for (int i = mdx - layer_offset; i <= mdx + layer_offset; i++) {
        if (i >= this->lowest_metal && i <= this->highest_metal) {
          CollectPointSet(Vset, Hset, i, gLL.x, gLL.y, gUR.x, gUR.y, this->lowest_metal, this->highest_metal);
        }
      }
    }
  }
  for (std::vector<RouterDB::Metal>::iterator it = glb_path.begin(); it != glb_path.end(); ++it) {
    mdx = it->MetalIdx;
    RouterDB::point gLL, gUR;
    pLLx = it->MetalRect.placedLL.x;
    pLLy = it->MetalRect.placedLL.y;
    pURx = it->MetalRect.placedUR.x;
    pURy = it->MetalRect.placedUR.y;
    GetGlobalRouteRange(mdx, pLLx, pLLy, pURx, pURy, offset, gLL, gUR, this->lowest_metal, this->highest_metal);
    for (int i = mdx - layer_offset; i <= mdx + layer_offset; i++) {
      if (i >= this->lowest_metal && i <= this->highest_metal) {
        CollectPointSet(Vset, Hset, i, gLL.x, gLL.y, gUR.x, gUR.y, this->lowest_metal, this->highest_metal);
      }
    }
  }
  // 5. create fake grids in rectangular shape
  std::vector<int> fake_old_source, fake_new_source, fake_old_dest, fake_new_dest;
  std::map<int, int> fake_total2graph;                                 // mapping from total to graph vertices
  std::map<int, int> fake_graph2total;                                 // mapping from graph to total vertices
  std::vector<RouterDB::vertex> fake_vertices_total;                   // vertex total list
  std::vector<int> fake_Start_index_metal_vertices(this->layerNo, 0);  // starting index in list for each metal layer
  std::vector<int> fake_End_index_metal_vertices(this->layerNo, -1);   // ending index in list for each metal layer
  std::vector<std::map<RouterDB::point, int, RouterDB::pointXYComp>> fake_vertices_total_map(
      this->layerNo);  // improve runtime of up/down edges - [wbxu: 20190505]
  CreateGridCoreFunc(this->lowest_metal, this->highest_metal, false, this->GridLL, this->GridUR, fake_vertices_total, fake_Start_index_metal_vertices,
                     fake_End_index_metal_vertices, fake_vertices_total_map);
  // 6. activate vertices according to global routes and block pins
  for (std::vector<RouterDB::vertex>::iterator it = fake_vertices_total.begin(); it != fake_vertices_total.end(); ++it) {
    int mm = it->metal;
    RouterDB::point p;
    p.x = it->x;
    p.y = it->y;
    if (this->drc_info.Metal_info.at(mm).direct == 0) {  // if vertical layer
      if (Vset.at(mm).find(p) != Vset.at(mm).end()) {
        it->active = true;
      }
    } else if (this->drc_info.Metal_info.at(mm).direct == 1) {  //  if horizontal layer
      if (Hset.at(mm).find(p) != Hset.at(mm).end()) {
        it->active = true;
      }
    } else {
      logger->error("Router-Error: incorrect routing direction on metal layer {0}", mm);
      continue;
    }
  }
  // 7. create real grids
  ReduceGrid(fake_vertices_total, this->vertices_total, fake_total2graph, fake_graph2total, fake_old_source, fake_old_dest, fake_new_source, fake_new_dest,
             this->Start_index_metal_vertices, this->End_index_metal_vertices, this->GridLL.x, this->GridLL.y, this->GridUR.x, this->GridUR.y,
             this->vertices_total_map);
}

void Grid::ReduceGrid(std::vector<RouterDB::vertex>& old_vertices, std::vector<RouterDB::vertex>& new_vertices, std::map<int, int>& old2new,
                      std::map<int, int>& new2old, std::vector<int>& old_source, std::vector<int>& old_dest, std::vector<int>& new_source,
                      std::vector<int>& new_dest, std::vector<int>& new_start, std::vector<int>& new_end, int LLx, int LLy, int URx, int URy,
                      std::vector<std::map<RouterDB::point, int, RouterDB::pointXYComp>>& new_vertices_map) {
  new_vertices.clear();
  old2new.clear();
  new2old.clear();
  new_source.clear();
  new_dest.clear();
  new_start.clear();
  new_start.resize(this->layerNo, 0);
  new_end.clear();
  new_end.resize(this->layerNo, -1);
  // a. copy vertices from old list to new one, build mapping
  for (unsigned int i = 0; i < old_vertices.size(); i++) {
    if (old_vertices.at(i).active) {
      if (old_vertices.at(i).x >= LLx && old_vertices.at(i).x <= URx && old_vertices.at(i).y >= LLy && old_vertices.at(i).y <= URy) {
        new_vertices.push_back(old_vertices.at(i));
        old2new[i] = new_vertices.size() - 1;
        new2old[new_vertices.size() - 1] = i;
      }
    }
  }
  // b. update index within vertex and start/end flag of new list
  std::vector<int> tmpv;
  RouterDB::point tmpp;
  int preMetal = -2;
  for (unsigned int i = 0; i < new_vertices.size(); i++) {
    tmpp.x = new_vertices.at(i).x;
    tmpp.y = new_vertices.at(i).y;
    if (new_vertices.at(i).metal >= 0) {
      new_vertices_map.at(new_vertices.at(i).metal).insert(std::pair<RouterDB::point, int>(tmpp, i));  // improve runtime of up/down edges - [wbxu: 20190505]
    }
    if (preMetal != new_vertices.at(i).metal) {
      new_start.at(new_vertices.at(i).metal) = i;
      new_end.at(new_vertices.at(i).metal) = i;
      preMetal = new_vertices.at(i).metal;
    } else {
      new_end.at(preMetal) = i;
    }
    new_vertices.at(i).index = i;
    tmpv = new_vertices.at(i).north;
    new_vertices.at(i).north.clear();
    for (std::vector<int>::iterator it = tmpv.begin(); it != tmpv.end(); ++it) {
      if (old2new.find(*it) != old2new.end()) new_vertices.at(i).north.push_back(old2new[*it]);
    }
    tmpv = new_vertices.at(i).south;
    new_vertices.at(i).south.clear();
    for (std::vector<int>::iterator it = tmpv.begin(); it != tmpv.end(); ++it) {
      if (old2new.find(*it) != old2new.end()) new_vertices.at(i).south.push_back(old2new[*it]);
    }
    tmpv = new_vertices.at(i).east;
    new_vertices.at(i).east.clear();
    for (std::vector<int>::iterator it = tmpv.begin(); it != tmpv.end(); ++it) {
      if (old2new.find(*it) != old2new.end()) new_vertices.at(i).east.push_back(old2new[*it]);
    }
    tmpv = new_vertices.at(i).west;
    new_vertices.at(i).west.clear();
    for (std::vector<int>::iterator it = tmpv.begin(); it != tmpv.end(); ++it) {
      if (old2new.find(*it) != old2new.end()) new_vertices.at(i).west.push_back(old2new[*it]);
    }
    int tmpi = new_vertices.at(i).up;
    if (old2new.find(tmpi) != old2new.end()) {
      new_vertices.at(i).up = old2new[tmpi];
    } else {
      new_vertices.at(i).up = -1;
    }
    tmpi = new_vertices.at(i).down;
    if (old2new.find(tmpi) != old2new.end()) {
      new_vertices.at(i).down = old2new[tmpi];
    } else {
      new_vertices.at(i).down = -1;
    }
  }
  // c. update new source/dest
  for (std::vector<int>::iterator it = old_source.begin(); it != old_source.end(); ++it) {
    if (old2new.find(*it) != old2new.end()) {
      new_source.push_back(old2new[*it]);
    }
  }
  for (std::vector<int>::iterator it = old_dest.begin(); it != old_dest.end(); ++it) {
    if (old2new.find(*it) != old2new.end()) {
      new_dest.push_back(old2new[*it]);
    }
  }
}

void Grid::CreateGridCoreFunc(int Lmetal, int Hmetal, bool VFlag, RouterDB::point AreaLL, RouterDB::point AreaUR,
                              std::vector<RouterDB::vertex>& fake_vertices_total, std::vector<int>& fake_Start_index_metal_vertices,
                              std::vector<int>& fake_End_index_metal_vertices,
                              std::vector<std::map<RouterDB::point, int, RouterDB::pointXYComp>>& fake_vertices_total_map) {
  auto logger = spdlog::default_logger()->clone("router.Grid.CreateGridCoreFunc");

  fake_vertices_total.clear();
  fake_Start_index_metal_vertices.clear();
  fake_Start_index_metal_vertices.resize(this->layerNo, 0);
  fake_End_index_metal_vertices.clear();
  fake_End_index_metal_vertices.resize(this->layerNo, -1);
  RouterDB::point tmpp;  // improve runtime of up/down edges - [wbxu: 20190505]
  // a. create grids
  for (int i = Lmetal; i <= Hmetal; i++) {
    fake_Start_index_metal_vertices.at(i) = fake_vertices_total.size();
    if (this->drc_info.Metal_info.at(i).direct == 0) {                        // if vertical layer
      int curlayer_unit = this->x_unit.at(i);                                 // current layer direction: vertical
      int nexlayer_unit;                                                      // neighboring layer direction: horizontal
      int LLx = curlayer_unit * (int)ceil(double(AreaLL.x) / curlayer_unit);  // X lower boudary
      int LLy;                                                                // Y lower boundary
      if (i == 0) {                                                           // if lowest layer
        nexlayer_unit = this->y_unit.at(i + 1);
        LLy = nexlayer_unit * (int)ceil(double(AreaLL.y) / nexlayer_unit);
      } else if (i == this->layerNo - 1) {  // if highest layer
        nexlayer_unit = this->y_unit.at(i - 1);
        LLy = nexlayer_unit * (int)ceil(double(AreaLL.y) / nexlayer_unit);
      } else {  // if middle layer
        nexlayer_unit = gcd(this->y_unit.at(i - 1), this->y_unit.at(i + 1));
        int LLy_1 = this->y_unit.at(i - 1) * (int)ceil(double(AreaLL.y) / this->y_unit.at(i - 1));
        int LLy_2 = this->y_unit.at(i + 1) * (int)ceil(double(AreaLL.y) / this->y_unit.at(i + 1));
        LLy = (LLy_1 < LLy_2) ? LLy_1 : LLy_2;
      }
      for (int X = LLx; X <= AreaUR.x; X += curlayer_unit) {
        for (int Y = LLy; Y <= AreaUR.y; Y += nexlayer_unit) {
          RouterDB::vertex tmpv;
          bool pmark = false;
          if (i == 0) {
            tmpv.gridmetal.push_back(i + 1);
            pmark = true;
          } else if (i == this->layerNo - 1) {
            tmpv.gridmetal.push_back(i - 1);
            pmark = true;
          } else {
            if (Y % this->y_unit.at(i - 1) == 0) {
              tmpv.gridmetal.push_back(i - 1);
              pmark = true;
            }
            if (Y % this->y_unit.at(i + 1) == 0) {
              tmpv.gridmetal.push_back(i + 1);
              pmark = true;
            }
          }
          if (!pmark) {
            continue;
          }
          tmpp.x = X;
          tmpp.y = Y;  // improve runtime of up/down edges - [wbxu: 20190505]
          tmpv.y = Y;
          tmpv.x = X;
          tmpv.metal = i;
          tmpv.active = VFlag;
          tmpv.index = fake_vertices_total.size();
          tmpv.up = -1;
          tmpv.down = -1;
          tmpv.north.clear();
          tmpv.south.clear();
          tmpv.east.clear();
          tmpv.west.clear();
          bool mark = false;
          int w;
          for (w = tmpv.index - 1; w >= fake_Start_index_metal_vertices.at(i); w--) {
            if (fake_vertices_total.at(w).x == tmpv.x) {
              if (tmpv.y - fake_vertices_total.at(w).y >= this->y_min.at(i)) {
                mark = true;
                break;
              }
            } else {
              break;
            }
          }
          if (mark) {
            tmpv.south.push_back(w);
            fake_vertices_total.at(w).north.push_back(tmpv.index);
          }
          fake_vertices_total.push_back(tmpv);
          fake_vertices_total_map.at(i).insert(
              std::pair<RouterDB::point, int>(tmpp, fake_vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
        }
      }
    } else if (this->drc_info.Metal_info.at(i).direct == 1) {                 // if horizontal layer
      int curlayer_unit = this->y_unit.at(i);                                 // current layer direction: horizontal
      int nexlayer_unit;                                                      // neighboring layer direction: vertical
      int LLy = curlayer_unit * (int)ceil(double(AreaLL.y) / curlayer_unit);  // Y lower boudary
      int LLx;                                                                // X lower boundary
      if (i == 0) {                                                           // if lowest layer
        nexlayer_unit = this->x_unit.at(i + 1);
        LLx = nexlayer_unit * (int)ceil(double(AreaLL.x) / nexlayer_unit);
      } else if (i == this->layerNo - 1) {  // if highest layer
        nexlayer_unit = this->x_unit.at(i - 1);
        LLx = nexlayer_unit * (int)ceil(double(AreaLL.x) / nexlayer_unit);
      } else {  // if middle layer
        nexlayer_unit = gcd(this->x_unit.at(i - 1), this->x_unit.at(i + 1));
        int LLx_1 = this->x_unit.at(i - 1) * (int)ceil(double(AreaLL.x) / this->x_unit.at(i - 1));
        int LLx_2 = this->x_unit.at(i + 1) * (int)ceil(double(AreaLL.x) / this->x_unit.at(i + 1));
        LLx = (LLx_1 < LLx_2) ? LLx_1 : LLx_2;
      }
      for (int Y = LLy; Y <= AreaUR.y; Y += curlayer_unit) {
        for (int X = LLx; X <= AreaUR.x; X += nexlayer_unit) {
          RouterDB::vertex tmpv;
          bool pmark = false;
          if (i == 0) {
            tmpv.gridmetal.push_back(i + 1);
            pmark = true;
          } else if (i == this->layerNo - 1) {
            tmpv.gridmetal.push_back(i - 1);
            pmark = true;
          } else {
            if (X % this->x_unit.at(i - 1) == 0) {
              tmpv.gridmetal.push_back(i - 1);
              pmark = true;
            }
            if (X % this->x_unit.at(i + 1) == 0) {
              tmpv.gridmetal.push_back(i + 1);
              pmark = true;
            }
          }
          if (!pmark) {
            continue;
          }
          tmpp.x = X;
          tmpp.y = Y;  // improve runtime of up/down edges - [wbxu: 20190505]
          tmpv.y = Y;
          tmpv.x = X;
          tmpv.metal = i;
          tmpv.active = VFlag;
          tmpv.index = fake_vertices_total.size();
          tmpv.up = -1;
          tmpv.down = -1;
          tmpv.north.clear();
          tmpv.south.clear();
          tmpv.east.clear();
          tmpv.west.clear();
          bool mark = false;
          int w;
          for (w = tmpv.index - 1; w >= fake_Start_index_metal_vertices.at(i); w--) {
            if (fake_vertices_total.at(w).y == tmpv.y) {
              if (tmpv.x - fake_vertices_total.at(w).x >= this->x_min.at(i)) {
                mark = true;
                break;
              }
            } else {
              break;
            }
          }
          if (mark) {
            tmpv.west.push_back(w);
            fake_vertices_total.at(w).east.push_back(tmpv.index);
          }
          fake_vertices_total.push_back(tmpv);
          fake_vertices_total_map.at(i).insert(
              std::pair<RouterDB::point, int>(tmpp, fake_vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
        }
      }
    } else {
      logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
      continue;
    }
    fake_End_index_metal_vertices.at(i) = fake_vertices_total.size() - 1;
  }
  // b. Add up/down infom for grid points
  std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit;  // improve runtime of up/down edges - [wbxu: 20190505]
  for (int k = Lmetal; k < Hmetal; k++) {
    for (int i = fake_Start_index_metal_vertices.at(k); i <= fake_End_index_metal_vertices.at(k); i++) {
      // improve runtime of up/down edges - [wbxu: 20190505]
      tmpp.x = fake_vertices_total[i].x;
      tmpp.y = fake_vertices_total[i].y;
      mit = fake_vertices_total_map.at(k + 1).find(tmpp);
      if (mit != fake_vertices_total_map.at(k + 1).end()) {
        fake_vertices_total[i].up = mit->second;
        fake_vertices_total[mit->second].down = i;
      }
      // for(int j=fake_Start_index_metal_vertices.at(k+1);j<=fake_End_index_metal_vertices.at(k+1);j++) {
      //  if(fake_vertices_total[j].x==fake_vertices_total[i].x && fake_vertices_total[j].y==fake_vertices_total[i].y ) {
      //    fake_vertices_total[j].down=i;
      //    fake_vertices_total[i].up=j;
      //    break;
      //  }
      //}
    }
  }
}

void Grid::GetGlobalRouteRange(int mdx, int pLLx, int pLLy, int pURx, int pURy, int offset, RouterDB::point& gLL, RouterDB::point& gUR, int Lmetal,
                               int Hmetal) {
  auto logger = spdlog::default_logger()->clone("router.Grid.GetGlobalRouteRange");

  if (this->drc_info.Metal_info.at(mdx).direct == 0) {  // if vertical layer
    int curlayer_unit = this->x_unit.at(mdx);           // current layer direction: vertical
    int nexlayer_unit;                                  // neighboring layer direction: horizontal
    int gLLx = 0, gLLy = 0, gURx = 0, gURy = 0;
    gLLx = curlayer_unit * (int)floor(double(pLLx) / curlayer_unit);  // X lower boudary
    gLLx -= curlayer_unit * offset;
    gURx = curlayer_unit * (int)ceil(double(pURx) / curlayer_unit);  // X upper boudary
    gURx += curlayer_unit * offset;
    if (mdx == 0) {  // if lowest layer
      nexlayer_unit = this->y_unit.at(mdx + 1);
      gLLy = nexlayer_unit * (int)floor(double(pLLy) / nexlayer_unit);
      gLLy -= nexlayer_unit * offset;
      gURy = nexlayer_unit * (int)ceil(double(pURy) / nexlayer_unit);
      gURy += nexlayer_unit * offset;
    } else if (mdx == this->layerNo - 1) {  // if highest layer
      nexlayer_unit = this->y_unit.at(mdx - 1);
      gLLy = nexlayer_unit * (int)floor(double(pLLy) / nexlayer_unit);
      gLLy -= nexlayer_unit * offset;
      gURy = nexlayer_unit * (int)ceil(double(pURy) / nexlayer_unit);
      gURy += nexlayer_unit * offset;
    } else if (mdx > 0 && mdx < this->layerNo - 1) {  // if middle layer
      // nexlayer_unit=gcd(this->y_unit.at(mdx-1), this->y_unit.at(mdx+1));
      int LLy_1, LLy_2;
      LLy_1 = this->y_unit.at(mdx - 1) * (int)floor(double(pLLy) / this->y_unit.at(mdx - 1));
      LLy_1 -= this->y_unit.at(mdx - 1) * offset;
      LLy_2 = this->y_unit.at(mdx + 1) * (int)floor(double(pLLy) / this->y_unit.at(mdx + 1));
      LLy_2 -= this->y_unit.at(mdx + 1) * offset;
      gLLy = (LLy_1 < LLy_2) ? LLy_1 : LLy_2;
      LLy_1 = this->y_unit.at(mdx - 1) * (int)ceil(double(pURy) / this->y_unit.at(mdx - 1));
      LLy_1 += this->y_unit.at(mdx - 1) * offset;
      LLy_2 = this->y_unit.at(mdx + 1) * (int)ceil(double(pURy) / this->y_unit.at(mdx + 1));
      LLy_2 += this->y_unit.at(mdx + 1) * offset;
      gURy = (LLy_1 > LLy_2) ? LLy_1 : LLy_2;
    } else {
      logger->error("Router-Error: metal index {0} cannot be found", mdx);
    }
    gLL.x = gLLx;
    gLL.y = gLLy;
    gUR.x = gURx;
    gUR.y = gURy;
    if (gLLx < this->LL.x) {
      this->GridLL.x = this->LL.x;
    } else {
      if (this->GridLL.x > gLLx) {
        this->GridLL.x = gLLx;
      }
    }

    if (gLLy < this->LL.y) {
      this->GridLL.y = this->LL.y;
    } else {
      if (this->GridLL.y > gLLy) {
        this->GridLL.y = gLLy;
      }
    }

    if (gURx > this->UR.x) {
      this->GridUR.x = this->UR.x;
    } else {
      if (this->GridUR.x < gURx) {
        this->GridUR.x = gURx;
      }
    }

    if (gURy > this->UR.y) {
      this->GridUR.y = this->UR.y;
    } else {
      if (this->GridUR.y < gURy) {
        this->GridUR.y = gURy;
      }
    }
  } else if (this->drc_info.Metal_info.at(mdx).direct == 1) {  // if horizontal layer
    int curlayer_unit = this->y_unit.at(mdx);                  // current layer direction: horizontal
    int nexlayer_unit;                                         // neighboring layer direction: vertical
    int gLLx = 0, gLLy = 0, gURx = 0, gURy = 0;
    gLLy = curlayer_unit * (int)floor(double(pLLy) / curlayer_unit);  // Y lower boudary
    gLLy -= curlayer_unit * offset;
    gURy = curlayer_unit * (int)ceil(double(pURy) / curlayer_unit);  // Y upper boudary
    gURy += curlayer_unit * offset;
    if (mdx == 0) {  // if lowest layer
      nexlayer_unit = this->x_unit.at(mdx + 1);
      gLLx = nexlayer_unit * (int)floor(double(pLLx) / nexlayer_unit);
      gLLx -= nexlayer_unit * offset;
      gURx = nexlayer_unit * (int)ceil(double(pURx) / nexlayer_unit);
      gURx += nexlayer_unit * offset;
    } else if (mdx == this->layerNo - 1) {  // if highest layer
      nexlayer_unit = this->x_unit.at(mdx - 1);
      gLLx = nexlayer_unit * (int)floor(double(pLLx) / nexlayer_unit);
      gLLx -= nexlayer_unit * offset;
      gURx = nexlayer_unit * (int)ceil(double(pURx) / nexlayer_unit);
      gURx += nexlayer_unit * offset;
    } else if (mdx > 0 && mdx < this->layerNo - 1) {  // if middle layer
      // nexlayer_unit=gcd(this->x_unit.at(mdx-1), this->x_unit.at(mdx+1));
      int LL_1, LL_2;
      LL_1 = this->x_unit.at(mdx - 1) * (int)floor(double(pLLx) / this->x_unit.at(mdx - 1));
      LL_1 -= this->x_unit.at(mdx - 1) * offset;
      LL_2 = this->x_unit.at(mdx + 1) * (int)floor(double(pLLx) / this->x_unit.at(mdx + 1));
      LL_2 -= this->x_unit.at(mdx + 1) * offset;
      gLLx = (LL_1 < LL_2) ? LL_1 : LL_2;
      LL_1 = this->x_unit.at(mdx - 1) * (int)ceil(double(pURx) / this->x_unit.at(mdx - 1));
      LL_1 += this->x_unit.at(mdx - 1) * offset;
      LL_2 = this->x_unit.at(mdx + 1) * (int)ceil(double(pURx) / this->x_unit.at(mdx + 1));
      LL_2 += this->x_unit.at(mdx + 1) * offset;
      gURx = (LL_1 > LL_2) ? LL_1 : LL_2;
    } else {
      logger->error("Router-Error: metal index {0} cannot be found", mdx);
    }
    gLL.x = gLLx;
    gLL.y = gLLy;
    gUR.x = gURx;
    gUR.y = gURy;
    if (gLLx < this->LL.x) {
      this->GridLL.x = this->LL.x;
    } else {
      if (this->GridLL.x > gLLx) {
        this->GridLL.x = gLLx;
      }
    }

    if (gLLy < this->LL.y) {
      this->GridLL.y = this->LL.y;
    } else {
      if (this->GridLL.y > gLLy) {
        this->GridLL.y = gLLy;
      }
    }

    if (gURx > this->UR.x) {
      this->GridUR.x = this->UR.x;
    } else {
      if (this->GridUR.x < gURx) {
        this->GridUR.x = gURx;
      }
    }

    if (gURy > this->UR.y) {
      this->GridUR.y = this->UR.y;
    } else {
      if (this->GridUR.y < gURy) {
        this->GridUR.y = gURy;
      }
    }
  } else {
    logger->error("Router-Error: incorrect routing direction on metal layer", mdx);
  }
}

void Grid::CollectPointSet(std::vector<std::set<RouterDB::point, RouterDB::pointXYComp>>& Vset,
                           std::vector<std::set<RouterDB::point, RouterDB::pointYXComp>>& Hset, int mdx, int pLLx, int pLLy, int pURx, int pURy, int Lmetal,
                           int Hmetal) {
  auto logger = spdlog::default_logger()->clone("router.Grid.CollectPointSet");

  if (this->drc_info.Metal_info.at(mdx).direct == 0) {  // if vertical layer
    int curlayer_unit = this->x_unit.at(mdx);           // current layer direction: vertical
    int nexlayer_unit = 1;                              // neighboring layer direction: horizontal
    int gLLx = 0, gLLy = 0, gURx = 0, gURy = 0;
    gLLx = curlayer_unit * (int)ceil(double(pLLx) / curlayer_unit);   // X lower boudary
    gURx = curlayer_unit * (int)floor(double(pURx) / curlayer_unit);  // X upper boudary
    if (mdx == 0) {                                                   // if lowest layer
      nexlayer_unit = this->y_unit.at(mdx + 1);
      gLLy = nexlayer_unit * (int)ceil(double(pLLy) / nexlayer_unit);
      gURy = nexlayer_unit * (int)floor(double(pURy) / nexlayer_unit);
    } else if (mdx == this->layerNo - 1) {  // if highest layer
      nexlayer_unit = this->y_unit.at(mdx - 1);
      gLLy = nexlayer_unit * (int)ceil(double(pLLy) / nexlayer_unit);
      gURy = nexlayer_unit * (int)floor(double(pURy) / nexlayer_unit);
    } else if (mdx > 0 && mdx < this->layerNo - 1) {  // if middle layer
      nexlayer_unit = gcd(this->y_unit.at(mdx - 1), this->y_unit.at(mdx + 1));
      int LLy_1, LLy_2;
      LLy_1 = this->y_unit.at(mdx - 1) * (int)ceil(double(pLLy) / this->y_unit.at(mdx - 1));
      LLy_2 = this->y_unit.at(mdx + 1) * (int)ceil(double(pLLy) / this->y_unit.at(mdx + 1));
      gLLy = (LLy_1 < LLy_2) ? LLy_1 : LLy_2;
      LLy_1 = this->y_unit.at(mdx - 1) * (int)floor(double(pURy) / this->y_unit.at(mdx - 1));
      LLy_2 = this->y_unit.at(mdx + 1) * (int)floor(double(pURy) / this->y_unit.at(mdx + 1));
      gURy = (LLy_1 > LLy_2) ? LLy_1 : LLy_2;
    } else {
      logger->error("Router-Error: metal index {0} cannot be found", mdx);
      assert(0);
    }
    for (int X = gLLx; X <= gURx; X += curlayer_unit) {
      for (int Y = gLLy; Y <= gURy; Y += nexlayer_unit) {
        RouterDB::point tmpv;
        bool pmark = false;
        if (mdx == 0 || mdx == this->layerNo - 1) {
          pmark = true;
        } else {
          if (Y % this->y_unit.at(mdx - 1) == 0) {
            pmark = true;
          }
          if (Y % this->y_unit.at(mdx + 1) == 0) {
            pmark = true;
          }
        }
        if (!pmark) {
          continue;
        }
        tmpv.y = Y;
        tmpv.x = X;
        Vset.at(mdx).insert(tmpv);
      }
    }
  } else if (this->drc_info.Metal_info.at(mdx).direct == 1) {  // if horizontal layer
    int curlayer_unit = this->y_unit.at(mdx);                  // current layer direction: horizontal
    int nexlayer_unit = 1;                                     // neighboring layer direction: vertical
    int gLLx = 0, gLLy = 0, gURx = 0, gURy = 0;
    gLLy = curlayer_unit * (int)ceil(double(pLLy) / curlayer_unit);   // Y lower boudary
    gURy = curlayer_unit * (int)floor(double(pURy) / curlayer_unit);  // Y upper boudary
    if (mdx == 0) {                                                   // if lowest layer
      nexlayer_unit = this->x_unit.at(mdx + 1);
      gLLx = nexlayer_unit * (int)ceil(double(pLLx) / nexlayer_unit);
      gURx = nexlayer_unit * (int)floor(double(pURx) / nexlayer_unit);
    } else if (mdx == this->layerNo - 1) {  // if highest layer
      nexlayer_unit = this->x_unit.at(mdx - 1);
      gLLx = nexlayer_unit * (int)ceil(double(pLLx) / nexlayer_unit);
      gURx = nexlayer_unit * (int)floor(double(pURx) / nexlayer_unit);
    } else if (mdx > 0 && mdx < this->layerNo - 1) {  // if middle layer
      nexlayer_unit = gcd(this->x_unit.at(mdx - 1), this->x_unit.at(mdx + 1));
      int LL_1, LL_2;
      LL_1 = this->x_unit.at(mdx - 1) * (int)ceil(double(pLLx) / this->x_unit.at(mdx - 1));
      LL_2 = this->x_unit.at(mdx + 1) * (int)ceil(double(pLLx) / this->x_unit.at(mdx + 1));
      gLLx = (LL_1 < LL_2) ? LL_1 : LL_2;
      LL_1 = this->x_unit.at(mdx - 1) * (int)floor(double(pURx) / this->x_unit.at(mdx - 1));
      LL_2 = this->x_unit.at(mdx + 1) * (int)floor(double(pURx) / this->x_unit.at(mdx + 1));
      gURx = (LL_1 > LL_2) ? LL_1 : LL_2;
    } else {
      logger->error("Router-Error: metal index {0} cannot be found", mdx);
      assert(0);
    }
    for (int Y = gLLy; Y <= gURy; Y += curlayer_unit) {
      for (int X = gLLx; X <= gURx; X += nexlayer_unit) {
        RouterDB::point tmpv;
        bool pmark = false;
        if (mdx == 0 || mdx == this->layerNo - 1) {
          pmark = true;
        } else {
          if (X % this->x_unit.at(mdx - 1) == 0) {
            pmark = true;
          }
          if (X % this->x_unit.at(mdx + 1) == 0) {
            pmark = true;
          }
        }
        if (!pmark) {
          continue;
        }
        tmpv.y = Y;
        tmpv.x = X;
        Hset.at(mdx).insert(tmpv);
      }
    }
  } else {
    logger->error("Router-Error: incorrect routing direction on metal layer {0}", mdx);
  }
}

Grid::Grid(PnRDB::Drc_info& drc_info, RouterDB::point ll, RouterDB::point ur, int Lmetal, int Hmetal, int grid_scale) : LL(ll), UR(ur), GridLL(ll), GridUR(ur) {
  auto logger = spdlog::default_logger()->clone("router.Grid.Grid");

  for (unsigned int i = 0; i < drc_info.Metal_info.size(); i++) {
    logger->debug("grid info {0} {1} ", drc_info.Metal_info.at(i).grid_unit_x, drc_info.Metal_info.at(i).grid_unit_y);
  }

  // Limitation: assume that neighboring layers have different routing diretions
  // 1. Initialize member variables I
  // this->LL=ll;
  // this->UR=ur;
  // this->GridLL=ll;
  // this->GridUR=ur;
  this->lowest_metal = Lmetal;
  this->highest_metal = Hmetal;
  this->grid_scale = grid_scale;
  this->layerNo = drc_info.Metal_info.size();
  this->Start_index_metal_vertices.resize(this->layerNo, 0);
  this->End_index_metal_vertices.resize(this->layerNo, -1);
  this->routeDirect.resize(this->layerNo);
  this->vertices_total.clear();
  this->drc_info = drc_info;
  // 2. Define member variables II
  this->x_unit.resize(this->layerNo, 0);
  this->y_unit.resize(this->layerNo, 0);
  this->x_min.resize(this->layerNo, 0);
  this->y_min.resize(this->layerNo, 0);
  this->vertices_total_map.clear();
  this->vertices_total_map.resize(this->layerNo);  // improve runtime of up/down edges - [wbxu: 20190505]
  // 3. Calculate grid unit and min length for each layer
  for (int i = 0; i < this->layerNo; i++) {
    // this->Start_index_metal_vertices.at(i)=0;
    // this->End_index_metal_vertices.at(i)=-1;
    this->routeDirect.at(i) = drc_info.Metal_info.at(i).direct;
    if (drc_info.Metal_info.at(i).direct == 0) {  // vertical
      // layer_unit.at(i)=drc_info.Metal_info.at(i).grid_unit_x;
      this->x_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_x * grid_scale;
      // this->y_min.at(i)=this->x_unit.at(i)/2;
      this->y_min.at(i) = 1;
    } else if (drc_info.Metal_info.at(i).direct == 1) {  // horizontal
      // layer_unit.at(i)=drc_info.Metal_info.at(i).grid_unit_y;
      this->y_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_y * grid_scale;
      // this->x_min.at(i)=this->y_unit.at(i)/2;
      this->x_min.at(i) = 1;
    } else {
      logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
      continue;
    }
  }
  // 4. Create grid points
  bool Power = false;
  RouterDB::point tmpp;  // improve runtime of up/down edges - [wbxu: 20190505]
  for (int i = this->lowest_metal; i <= this->highest_metal; i++) {
    this->Start_index_metal_vertices.at(i) = this->vertices_total.size();
    if (drc_info.Metal_info.at(i).direct == 0) {  // if vertical layer
      int curlayer_unit = x_unit.at(i);           // current layer direction: vertical
      int nexlayer_unit;                          // neighboring layer direction: horizontal
      // int LLx = int(ceil(double(LL.x)/curlayer_unit))
      int LLx = (LL.x % curlayer_unit == 0) ? (LL.x)
                                            : ((LL.x / curlayer_unit) * curlayer_unit < LL.x ? (LL.x / curlayer_unit + 1) * curlayer_unit
                                                                                             : (LL.x / curlayer_unit) * curlayer_unit);  // X lower boudary
      int LLy;                                                                                                                           // Y lower boundary
      if (i == 0) {                                                                                                                      // if lowest layer
        nexlayer_unit = y_unit.at(i + 1);
        LLy = (LL.y % y_unit.at(i + 1) == 0) ? (LL.y)
                                             : ((LL.y / y_unit.at(i + 1)) * y_unit.at(i + 1) < LL.y ? (LL.y / y_unit.at(i + 1) + 1) * y_unit.at(i + 1)
                                                                                                    : (LL.y / y_unit.at(i + 1)) * y_unit.at(i + 1));
      } else if (i == this->layerNo - 1) {  // if highest layer
        nexlayer_unit = y_unit.at(i - 1);
        LLy = (LL.y % y_unit.at(i - 1) == 0) ? (LL.y)
                                             : ((LL.y / y_unit.at(i - 1)) * y_unit.at(i - 1) < LL.y ? (LL.y / y_unit.at(i - 1) + 1) * y_unit.at(i - 1)
                                                                                                    : (LL.y / y_unit.at(i - 1)) * y_unit.at(i - 1));
      } else {  // if middle layer
        nexlayer_unit = gcd(y_unit.at(i - 1), y_unit.at(i + 1));
        int LLy_1 = (LL.y % y_unit.at(i - 1) == 0) ? (LL.y)
                                                   : ((LL.y / y_unit.at(i - 1)) * y_unit.at(i - 1) < LL.y ? (LL.y / y_unit.at(i - 1) + 1) * y_unit.at(i - 1)
                                                                                                          : (LL.y / y_unit.at(i - 1)) * y_unit.at(i - 1));
        int LLy_2 = (LL.y % y_unit.at(i + 1) == 0) ? (LL.y)
                                                   : ((LL.y / y_unit.at(i + 1)) * y_unit.at(i + 1) < LL.y ? (LL.y / y_unit.at(i + 1) + 1) * y_unit.at(i + 1)
                                                                                                          : (LL.y / y_unit.at(i + 1)) * y_unit.at(i + 1));
        LLy = (LLy_1 < LLy_2) ? LLy_1 : LLy_2;
      }
      // std::cout<<"Create grid on layer test1"<<i<<std::endl;
      for (int X = LLx; X <= UR.x; X += curlayer_unit) {
        Power = !Power;
        for (int Y = LLy; Y <= UR.y; Y += nexlayer_unit) {
          RouterDB::vertex tmpv;
          bool pmark = false;
          if (i == 0) {
            tmpv.gridmetal.push_back(i + 1);
            pmark = true;
          } else if (i == this->layerNo - 1) {
            tmpv.gridmetal.push_back(i - 1);
            pmark = true;
          } else {
            if (Y % y_unit.at(i - 1) == 0) {
              tmpv.gridmetal.push_back(i - 1);
              pmark = true;
            }
            if (Y % y_unit.at(i + 1) == 0) {
              tmpv.gridmetal.push_back(i + 1);
              pmark = true;
            }
          }
          if (!pmark) {
            continue;
          }
          tmpp.x = X;
          tmpp.y = Y;  // improve runtime of up/down edges - [wbxu: 20190505]
          tmpv.y = Y;
          tmpv.x = X;
          tmpv.metal = i;
          if (Power) {
            tmpv.power = 1;
          } else {
            tmpv.power = 0;
          }
          tmpv.active = true;
          tmpv.index = this->vertices_total.size();
          tmpv.up = -1;
          tmpv.down = -1;
          tmpv.north.clear();
          tmpv.south.clear();
          tmpv.east.clear();
          tmpv.west.clear();
          bool mark = false;
          int w;
          for (w = tmpv.index - 1; w >= this->Start_index_metal_vertices.at(i); w--) {
            if (this->vertices_total.at(w).x == tmpv.x) {
              if (tmpv.y - this->vertices_total.at(w).y >= y_min.at(i)) {
                mark = true;
                break;
              }
            } else {
              break;
            }
          }
          if (mark) {
            tmpv.south.push_back(w);
            this->vertices_total.at(w).north.push_back(tmpv.index);
          }
          this->vertices_total.push_back(tmpv);
          this->vertices_total_map.at(i).insert(
              std::pair<RouterDB::point, int>(tmpp, this->vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
        }
      }
    } else if (drc_info.Metal_info.at(i).direct == 1) {  // if horizontal layer
      // std::cout<<"Create grid on layer test2"<<i<<std::endl;
      int curlayer_unit = y_unit.at(i);  // current layer direction: horizontal
      int nexlayer_unit;                 // neighboring layer direction: vertical
      int LLy = (LL.y % curlayer_unit == 0) ? (LL.y)
                                            : ((LL.y / curlayer_unit) * curlayer_unit < LL.y ? (LL.y / curlayer_unit + 1) * curlayer_unit
                                                                                             : (LL.y / curlayer_unit) * curlayer_unit);  // Y lower boudary
      int LLx;                                                                                                                           // X lower boundary
      if (i == 0) {                                                                                                                      // if lowest layer
        nexlayer_unit = x_unit.at(i + 1);
        LLx = (LL.x % x_unit.at(i + 1) == 0) ? (LL.x)
                                             : ((LL.x / x_unit.at(i + 1)) * x_unit.at(i + 1) < LL.x ? (LL.x / x_unit.at(i + 1) + 1) * x_unit.at(i + 1)
                                                                                                    : (LL.x / x_unit.at(i + 1)) * x_unit.at(i + 1));
      } else if (i == this->layerNo - 1) {  // if highest layer
        nexlayer_unit = x_unit.at(i - 1);
        LLx = (LL.x % x_unit.at(i - 1) == 0) ? (LL.x)
                                             : ((LL.x / x_unit.at(i - 1)) * x_unit.at(i - 1) < LL.x ? (LL.x / x_unit.at(i - 1) + 1) * x_unit.at(i - 1)
                                                                                                    : (LL.x / x_unit.at(i - 1)) * x_unit.at(i - 1));
      } else {  // if middle layer
        nexlayer_unit = gcd(x_unit.at(i - 1), x_unit.at(i + 1));
        int LLx_1 = (LL.x % x_unit.at(i - 1) == 0) ? (LL.x)
                                                   : ((LL.x / x_unit.at(i - 1)) * x_unit.at(i - 1) < LL.x ? (LL.x / x_unit.at(i - 1) + 1) * x_unit.at(i - 1)
                                                                                                          : (LL.x / x_unit.at(i - 1)) * x_unit.at(i - 1));
        int LLx_2 = (LL.x % x_unit.at(i + 1) == 0) ? (LL.x)
                                                   : ((LL.x / x_unit.at(i + 1)) * x_unit.at(i + 1) < LL.x ? (LL.x / x_unit.at(i + 1) + 1) * x_unit.at(i + 1)
                                                                                                          : (LL.x / x_unit.at(i + 1)) * x_unit.at(i + 1));
        LLx = (LLx_1 < LLx_2) ? LLx_1 : LLx_2;
      }
      // std::cout<<"LLx , URx, LLy, URy "<<LLx<<" "<<UR.x<<" "<<LLy<<" "<<UR.y<<std::endl;
      // std::cout<<curlayer_unit<<" "<<nexlayer_unit<<std::endl;
      for (int Y = LLy; Y <= UR.y; Y += curlayer_unit) {
        Power = !Power;
        for (int X = LLx; X <= UR.x; X += nexlayer_unit) {
          RouterDB::vertex tmpv;
          bool pmark = false;
          if (i == 0) {
            tmpv.gridmetal.push_back(i + 1);
            pmark = true;
          } else if (i == this->layerNo - 1) {
            tmpv.gridmetal.push_back(i - 1);
            pmark = true;
          } else {
            if (X % x_unit.at(i - 1) == 0) {
              tmpv.gridmetal.push_back(i - 1);
              pmark = true;
            }
            if (X % x_unit.at(i + 1) == 0) {
              tmpv.gridmetal.push_back(i + 1);
              pmark = true;
            }
          }
          if (!pmark) {
            continue;
          }
          tmpp.x = X;
          tmpp.y = Y;  // improve runtime of up/down edges - [wbxu: 20190505]
          tmpv.y = Y;
          tmpv.x = X;
          tmpv.metal = i;
          if (Power) {
            tmpv.power = 1;
          } else {
            tmpv.power = 0;
          }
          tmpv.active = true;
          tmpv.index = this->vertices_total.size();
          tmpv.up = -1;
          tmpv.down = -1;
          tmpv.north.clear();
          tmpv.south.clear();
          tmpv.east.clear();
          tmpv.west.clear();
          bool mark = false;
          int w;
          for (w = tmpv.index - 1; w >= this->Start_index_metal_vertices.at(i); w--) {
            if (this->vertices_total.at(w).y == tmpv.y) {
              if (tmpv.x - this->vertices_total.at(w).x >= x_min.at(i)) {
                mark = true;
                break;
              }
            } else {
              break;
            }
          }
          if (mark) {
            tmpv.west.push_back(w);
            this->vertices_total.at(w).east.push_back(tmpv.index);
          }
          this->vertices_total.push_back(tmpv);
          this->vertices_total_map.at(i).insert(
              std::pair<RouterDB::point, int>(tmpp, this->vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
        }
      }
    } else {
      logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
      continue;
    }
    this->End_index_metal_vertices.at(i) = vertices_total.size() - 1;
    // std::cout<<"Finished Create grid on layer "<<i<<" "<<this->highest_metal<<std::endl;
  }

  // 5. Add up/down infom for grid points
  std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit;  // improve runtime of up/down edges - [wbxu: 20190505]
  for (int k = this->lowest_metal; k < this->highest_metal; k++) {
    for (int i = this->Start_index_metal_vertices.at(k); i <= this->End_index_metal_vertices.at(k); i++) {
      // improve runtime of up/down edges - [wbxu: 20190505]
      tmpp.x = this->vertices_total[i].x;
      tmpp.y = this->vertices_total[i].y;
      mit = this->vertices_total_map.at(k + 1).find(tmpp);
      if (mit != this->vertices_total_map.at(k + 1).end()) {
        this->vertices_total[i].up = mit->second;
        this->vertices_total[mit->second].down = i;
      }
      // for(int j=this->Start_index_metal_vertices.at(k+1);j<=this->End_index_metal_vertices.at(k+1);j++) {
      //  if(this->vertices_total[j].x==this->vertices_total[i].x && this->vertices_total[j].y==this->vertices_total[i].y ) {
      //    this->vertices_total[j].down=i;
      //    this->vertices_total[i].up=j;
      //    break;
      //  }
      //}
    }
  }
  // CheckVerticesTotal();
}

void Grid::CreatePlistSingleContact(std::vector<std::vector<RouterDB::point>>& plist, RouterDB::contact& Contacts) {
  // RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;

  mIdx = Contacts.metal;
  LLx = Contacts.placedLL.x;
  LLy = Contacts.placedLL.y;
  URx = Contacts.placedUR.x;
  URy = Contacts.placedUR.y;
  ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
};

void Grid::InactiveGlobalInternalMetal(std::vector<RouterDB::Block>& Blocks) {
  std::vector<std::vector<RouterDB::point>> plist;
  plist.resize(this->layerNo);
  // RouterDB::point tmpP;
  // int mIdx, LLx, LLy, URx, URy;
  for (std::vector<RouterDB::Block>::iterator bit = Blocks.begin(); bit != Blocks.end(); ++bit) {
    // 1. collect pin contacts on grids
    for (std::vector<RouterDB::Pin>::iterator pit = bit->pins.begin(); pit != bit->pins.end(); ++pit) {
      for (std::vector<RouterDB::contact>::iterator cit = pit->pinContacts.begin(); cit != pit->pinContacts.end(); ++cit) {
        CreatePlistSingleContact(plist, *cit);
      }
      for (std::vector<RouterDB::Via>::iterator cit = pit->pinVias.begin(); cit != pit->pinVias.end(); ++cit) {
        CreatePlistSingleContact(plist, cit->UpperMetalRect);
        CreatePlistSingleContact(plist, cit->LowerMetalRect);
      }
    }
    // 2. collect internal metals on grids
    for (std::vector<RouterDB::contact>::iterator pit = bit->InternalMetal.begin(); pit != bit->InternalMetal.end(); ++pit) {
      CreatePlistSingleContact(plist, *pit);
    }
    for (std::vector<RouterDB::Via>::iterator pit = bit->InternalVia.begin(); pit != bit->InternalVia.end(); ++pit) {
      CreatePlistSingleContact(plist, pit->UpperMetalRect);
      CreatePlistSingleContact(plist, pit->LowerMetalRect);
    }
  }
  // 3. inactive grid poins in collected list
  RouterDB::point tmpp;
  std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit;  // improve runtime of up/down edges - [wbxu: 20190505]
  for (int k = this->lowest_metal; k <= this->highest_metal; k++) {
    // improve runtime of up/down edges - [wbxu: 20190505]
    for (unsigned int j = 0; j < plist.at(k).size(); j++) {
      tmpp.x = plist.at(k).at(j).x;
      tmpp.y = plist.at(k).at(j).y;
      mit = this->vertices_total_map.at(k).find(tmpp);
      if (mit != this->vertices_total_map.at(k).end()) {
        this->vertices_total[mit->second].active = false;
      }
    }
    // for(int i=this->Start_index_metal_vertices.at(k);i<=this->End_index_metal_vertices.at(k);i++) {
    //  for(int j=0;j<plist.at(k).size();j++) {
    //    if(plist.at(k).at(j).x==this->vertices_total[i].x && plist.at(k).at(j).y==this->vertices_total[i].y ) {
    //      this->vertices_total[i].active=false;
    //      break;
    //    }
    //  }
    //}
  }
}

void Grid::InactivePlist(std::vector<std::vector<RouterDB::DetailPoint>>& plist) {
  for (int k = this->lowest_metal; k <= this->highest_metal; k++) {
    for (int i = this->Start_index_metal_vertices.at(k); i <= this->End_index_metal_vertices.at(k); i++) {
      for (unsigned int j = 0; j < plist.at(k).size(); j++) {
        if (plist.at(k).at(j).x == this->vertices_total[i].x && plist.at(k).at(j).y == this->vertices_total[i].y) {
          this->vertices_total[i].active = false;
          break;
        }
      }
    }
  }
}

void Grid::ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point>>& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  auto logger = spdlog::default_logger()->clone("router.Grid.ConvertRect2GridPoints");

  RouterDB::point tmpP;
  int obs_l = 0;
  int obs_h = this->layerNo - 1;
  int direction = drc_info.Metal_info[mIdx].direct;
  int minL = drc_info.Metal_info[mIdx].minL;

  if (direction == 1) {  // h

    if ((URx - LLx) < minL) {
      int extend_dis = ceil(minL - (URx - LLx)) / 2;
      LLx = LLx - extend_dis;
      URx = URx + extend_dis;
    }

  } else {  // v

    if ((URy - LLy) < minL) {
      int extend_dis = ceil(minL - (URy - LLy)) / 2;
      LLy = LLy - extend_dis;
      URy = URy + extend_dis;
    }
  }

  if (drc_info.Metal_info[mIdx].direct == 0) {  // vertical metal layer
    int curlayer_unit = drc_info.Metal_info.at(mIdx).grid_unit_x;
    int newLLx = LLx - curlayer_unit + drc_info.Metal_info.at(mIdx).width / 2;
    int newURx = URx + curlayer_unit - drc_info.Metal_info.at(mIdx).width / 2;
    int boundX = (newLLx % curlayer_unit == 0) ? (newLLx + curlayer_unit)
                                               : ((newLLx / curlayer_unit) * curlayer_unit < newLLx ? (newLLx / curlayer_unit + 1) * curlayer_unit
                                                                                                    : (newLLx / curlayer_unit) * curlayer_unit);
    for (int x = boundX; x < newURx; x += curlayer_unit) {
      if (mIdx != obs_l) {
        int nexlayer_unit = drc_info.Metal_info.at(mIdx - 1).grid_unit_y;

        // int newLLy=LLy-nexlayer_unit;
        // int newURy=URy+nexlayer_unit;
        // int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ?
        // (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );

        int newLLy = LLy - drc_info.Metal_info.at(mIdx).dist_ee;
        int newURy = URy + drc_info.Metal_info.at(mIdx).dist_ee;
        // int boundY=(newLLy%nexlayer_unit==0) ? (newLLy) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit :
        // (newLLy/nexlayer_unit)*nexlayer_unit  );
        int boundY = floor((double)newLLy / nexlayer_unit) * nexlayer_unit;
        newURy = ceil((double)newURy / nexlayer_unit) * nexlayer_unit;
        logger->debug("converter check point 1");
        for (int y = boundY; y <= newURy; y += nexlayer_unit) {
          if (x >= LLx && x <= URx && y >= LLy && y <= URy) {
            logger->debug("Plist problem");
            tmpP.x = x;
            tmpP.y = y;
            plist.at(mIdx).push_back(tmpP);
          }

          // tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if (mIdx != obs_h) {
        int nexlayer_unit = drc_info.Metal_info.at(mIdx + 1).grid_unit_y;

        // int newLLy=LLy-nexlayer_unit;
        // int newURy=URy+nexlayer_unit;
        // int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ?
        // (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );

        int newLLy = LLy - drc_info.Metal_info.at(mIdx).dist_ee;
        int newURy = URy + drc_info.Metal_info.at(mIdx).dist_ee;
        // int boundY=(newLLy%nexlayer_unit==0) ? (newLLy) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit :
        // (newLLy/nexlayer_unit)*nexlayer_unit  );
        int boundY = floor((double)newLLy / nexlayer_unit) * nexlayer_unit;
        newURy = ceil((double)newURy / nexlayer_unit) * nexlayer_unit;
        logger->debug("converter check point 2");
        for (int y = boundY; y <= newURy; y += nexlayer_unit) {
          if (x >= LLx && x <= URx && y >= LLy && y <= URy) {
            tmpP.x = x;
            tmpP.y = y;
            plist.at(mIdx).push_back(tmpP);
          }
          // tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else if (drc_info.Metal_info[mIdx].direct == 1) {  // horizontal metal layer
    int curlayer_unit = drc_info.Metal_info.at(mIdx).grid_unit_y;
    int newLLy = LLy - curlayer_unit + drc_info.Metal_info.at(mIdx).width / 2;
    int newURy = URy + curlayer_unit - drc_info.Metal_info.at(mIdx).width / 2;
    int boundY = (newLLy % curlayer_unit == 0) ? (newLLy + curlayer_unit)
                                               : ((newLLy / curlayer_unit) * curlayer_unit < newLLy ? (newLLy / curlayer_unit + 1) * curlayer_unit
                                                                                                    : (newLLy / curlayer_unit) * curlayer_unit);
    for (int y = boundY; y < newURy; y += curlayer_unit) {
      if (mIdx != obs_l) {
        int nexlayer_unit = drc_info.Metal_info.at(mIdx - 1).grid_unit_x;

        // int newLLx=LLx-nexlayer_unit;
        // int newURx=URx+nexlayer_unit;
        // int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ?
        // (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );

        int newLLx = LLx - drc_info.Metal_info.at(mIdx).dist_ee;
        int newURx = URx + drc_info.Metal_info.at(mIdx).dist_ee;
        // int boundX=(newLLx%nexlayer_unit==0) ? (newLLx) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit :
        // (newLLx/nexlayer_unit)*nexlayer_unit  );
        int boundX = floor((double)newLLx / nexlayer_unit) * nexlayer_unit;
        newURx = ceil((double)newURx / nexlayer_unit) * nexlayer_unit;
        logger->debug("converter check point 3");
        for (int x = boundX; x <= newURx; x += nexlayer_unit) {
          if (x >= LLx && x <= URx && y >= LLy && y <= URy) {
            tmpP.x = x;
            tmpP.y = y;
            plist.at(mIdx).push_back(tmpP);
          }
          // tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if (mIdx != obs_h) {
        int nexlayer_unit = drc_info.Metal_info.at(mIdx + 1).grid_unit_x;

        // int newLLx=LLx-nexlayer_unit;
        // int newURx=URx+nexlayer_unit;
        // int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ?
        // (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );

        int newLLx = LLx - drc_info.Metal_info.at(mIdx).dist_ee;
        int newURx = URx + drc_info.Metal_info.at(mIdx).dist_ee;
        // int boundX=(newLLx%nexlayer_unit==0) ? (newLLx) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit :
        // (newLLx/nexlayer_unit)*nexlayer_unit  );
        int boundX = floor((double)newLLx / nexlayer_unit) * nexlayer_unit;
        newURx = ceil((double)newURx / nexlayer_unit) * nexlayer_unit;
        logger->debug("converter check point 4");
        for (int x = boundX; x <= newURx; x += nexlayer_unit) {
          if (x >= LLx && x <= URx && y >= LLy && y <= URy) {
            tmpP.x = x;
            tmpP.y = y;
            plist.at(mIdx).push_back(tmpP);
          }
          // tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else {
    logger->error("Router-Error: incorrect routing direction");
  }
};

/*
void Grid::ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  RouterDB::point tmpP;
  if(this->routeDirect.at(mIdx)==0) { // vertical metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_x;
    int newLLx=LLx-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    int newURx=URx+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundX=(newLLx%curlayer_unit==0) ? (newLLx+curlayer_unit) : ( (newLLx/curlayer_unit)*curlayer_unit<newLLx ? (newLLx/curlayer_unit+1)*curlayer_unit :
(newLLx/curlayer_unit)*curlayer_unit  ); for(int x=boundX; x<newURx; x+=curlayer_unit) { if(mIdx!=0) { int
nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_y; int newLLy=LLy-nexlayer_unit; int newURy=URy+nexlayer_unit; int boundY=(newLLy%nexlayer_unit==0) ?
(newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        for(int y=boundY; y<newURy; y+=nexlayer_unit) {
          tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=this->layerNo-1) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_y;
        int newLLy=LLy-nexlayer_unit;
        int newURy=URy+nexlayer_unit;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit :
(newLLy/nexlayer_unit)*nexlayer_unit  ); for(int y=boundY; y<newURy; y+=nexlayer_unit) { tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else if(this->routeDirect.at(mIdx)==1) { // horizontal metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_y;
    int newLLy=LLy-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    int newURy=URy+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundY=(newLLy%curlayer_unit==0) ? (newLLy+curlayer_unit) : ( (newLLy/curlayer_unit)*curlayer_unit<newLLy ? (newLLy/curlayer_unit+1)*curlayer_unit :
(newLLy/curlayer_unit)*curlayer_unit  ); for(int y=boundY; y<newURy; y+=curlayer_unit) { if(mIdx!=0) { int
nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_x; int newLLx=LLx-nexlayer_unit; int newURx=URx+nexlayer_unit; int boundX=(newLLx%nexlayer_unit==0) ?
(newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        for(int x=boundX; x<newURx; x+=nexlayer_unit) {
          tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=this->layerNo-1) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_x;
        int newLLx=LLx-nexlayer_unit;
        int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit :
(newLLx/nexlayer_unit)*nexlayer_unit  ); for(int x=boundX; x<newURx; x+=nexlayer_unit) { tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else {
    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
  }
// Limitation:
// 1. all the grid nodes around the rectangle will be chosen,
// only if the rectangle boundary is exactly on grid
// 2. both nodes crossing with upper layer and lower layer will be chosen
// which results in perssimism
//  RouterDB::point tmpP;
//  if(this->routeDirect.at(mIdx)==0) { // vertical metal layer
//    for(int x=(LLx/x_unit.at(mIdx))*x_unit.at(mIdx); x<=int(ceil((double)URx/x_unit.at(mIdx)))*x_unit.at(mIdx); x+=x_unit.at(mIdx)) {
//      if( mIdx!=this->lowest_metal ) {
//        for(int y=(LLy/y_unit.at(mIdx-1))*y_unit.at(mIdx-1); y<=int(ceil((double)URy/y_unit.at(mIdx-1)))*y_unit.at(mIdx-1); y+=y_unit.at(mIdx-1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//      if( mIdx!=this->highest_metal ) {
//        for(int y=(LLy/y_unit.at(mIdx+1))*y_unit.at(mIdx+1); y<=int(ceil((double)URy/y_unit.at(mIdx+1)))*y_unit.at(mIdx+1); y+=y_unit.at(mIdx+1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//    }
//  } else if (this->routeDirect.at(mIdx)==1) { // horizontal metal layer
//    for(int y=(LLy/y_unit.at(mIdx))*y_unit.at(mIdx); y<=int(ceil((double)URy/y_unit.at(mIdx)))*y_unit.at(mIdx); y+=y_unit.at(mIdx)) {
//      if( mIdx!=this->lowest_metal ) {
//        for(int x=(LLx/x_unit.at(mIdx-1))*x_unit.at(mIdx-1); x<=int(ceil((double)URx/x_unit.at(mIdx-1)))*x_unit.at(mIdx-1); x+=x_unit.at(mIdx-1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//      if( mIdx!=this->highest_metal ) {
//        for(int x=(LLx/x_unit.at(mIdx+1))*x_unit.at(mIdx+1); x<=int(ceil((double)URx/x_unit.at(mIdx+1)))*x_unit.at(mIdx+1); x+=x_unit.at(mIdx+1)) {
//          tmpP.x=x; tmpP.y=y;
//          plist.at(mIdx).push_back(tmpP);
//        }
//      }
//    }
//  } else {
//    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
//  }
}
*/

void Grid::PrepareGraphVertices(int LLx, int LLy, int URx, int URy) {
  std::set<int> Source_set;
  for (std::vector<int>::iterator it = Source.begin(); it != Source.end(); ++it) {
    Source_set.insert(*it);
  }
  std::set<int> Dest_set;
  for (std::vector<int>::iterator it = Dest.begin(); it != Dest.end(); ++it) {
    Dest_set.insert(*it);
  }

  vertices_graph.clear();
  total2graph.clear();
  graph2total.clear();
  RouterDB::point minP, maxP;
  minP.x = LLx;
  minP.y = LLy;
  maxP.x = URx;
  maxP.y = URy;
  for (int k = 0; k < this->layerNo; ++k) {
    if (vertices_total_map.at(k).empty()) {
      continue;
    }
    std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator low = vertices_total_map.at(k).lower_bound(minP);
    std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator high = vertices_total_map.at(k).upper_bound(maxP);
    for (std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator pit = low; pit != high; ++pit) {
      int i = pit->second;
      if (vertices_total.at(i).active) {
        if (vertices_total.at(i).x >= LLx && vertices_total.at(i).x <= URx && vertices_total.at(i).y >= LLy && vertices_total.at(i).y <= URy) {
          vertices_graph.emplace_back(vertices_total.at(i));
          total2graph[i] = vertices_graph.size() - 1;
          graph2total[vertices_graph.size() - 1] = i;
        }
      }
    }
  }
}

void Grid::ActivateSourceDest() {
  for (std::vector<int>::iterator it = Source.begin(); it != Source.end(); ++it) {
    vertices_total.at(*it).active = true;
    // std::cout<<" {"<<vertices_total.at(*it).x<<","<<vertices_total.at(*it).y<<"} ";
  }
  for (std::vector<int>::iterator it = Dest.begin(); it != Dest.end(); ++it) {
    vertices_total.at(*it).active = true;
    // std::cout<<" {"<<vertices_total.at(*it).x<<","<<vertices_total.at(*it).y<<"} ";
  }
  // std::cout<<std::endl;
}

void Grid::InactivateSourceDest() {
  for (std::vector<int>::iterator it = Source.begin(); it != Source.end(); ++it) {
    vertices_total.at(*it).active = false;
  }
  for (std::vector<int>::iterator it = Dest.begin(); it != Dest.end(); ++it) {
    vertices_total.at(*it).active = false;
  }
}

// added by yg

std::vector<RouterDB::contact> Grid::setSrcDest(std::vector<RouterDB::SinkData>& Vsource, std::vector<RouterDB::SinkData>& Vdest, int width, int height,
                                                std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp>& Smap) {
  auto logger = spdlog::default_logger()->clone("router.Grid.setSrcDest");

  Source.clear();
  Dest.clear();
  std::vector<RouterDB::contact> Terminal_contact;
  RouterDB::contact terminal_contact;
  RouterDB::SinkData source, dest;
  // for source
  for (unsigned int i = 0; i < Vsource.size(); i++) {
    source = Vsource[i];
    std::vector<int> temp_Source;
    if (source.coord.size() > 1) {
      // for pin
      temp_Source = Mapping_function_pin(source);
      for (unsigned int j = 0; j < temp_Source.size(); j++) {
        Source.push_back(temp_Source[j]);
      }
    } else if (source.metalIdx != -1) {
      // for terminal
      int min_dis = INT_MAX;
      // wbxu: another logic problem in the following [fixed]
      int direction = 0;
      if (abs(source.coord[0].x - 0) < min_dis) {
        direction = 0;
        min_dis = abs(source.coord[0].x - 0);
      }
      if (abs(source.coord[0].x - width) < min_dis) {
        direction = 0;
        min_dis = abs(source.coord[0].x - width);
      }
      if (abs(source.coord[0].y - 0) < min_dis) {
        direction = 1;
        min_dis = abs(source.coord[0].y - 0);
      }
      if (abs(source.coord[0].y - height) < min_dis) {
        direction = 1;
        min_dis = abs(source.coord[0].y - height);
      }

      for (int temp_MetalIdx = lowest_metal; temp_MetalIdx <= highest_metal; temp_MetalIdx++) {
        temp_Source = Mapping_function_terminal(source, temp_MetalIdx, direction);
        if (temp_Source.size() > 0) {
          for (unsigned int j = 0; j < temp_Source.size(); j++) {
            int myext = this->drc_info.Metal_info.at(vertices_total[temp_Source[j]].metal).width / 2;
            Source.push_back(temp_Source[j]);
            terminal_contact.metal = vertices_total[temp_Source[j]].metal;
            terminal_contact.placedCenter.x = vertices_total[temp_Source[j]].x;
            terminal_contact.placedCenter.y = vertices_total[temp_Source[j]].y;
            terminal_contact.placedLL.x = terminal_contact.placedCenter.x - myext;
            terminal_contact.placedLL.y = terminal_contact.placedCenter.y - myext;
            terminal_contact.placedUR.x = terminal_contact.placedCenter.x + myext;
            terminal_contact.placedUR.y = terminal_contact.placedCenter.y + myext;
            // std::cout<<"INFO:: terminal contact metal"<<terminal_contact.metal<<" "<<terminal_contact.placedLL.x<<","<<terminal_contact.placedLL.y<<";
            // "<<terminal_contact.placedUR.x<<","<<terminal_contact.placedUR.y<<std::endl;
            Terminal_contact.push_back(terminal_contact);
          }
          int temp_width = 1;
          Vsource[i].coord.clear();
          RouterDB::point t_point;
          t_point.x = vertices_total[temp_Source[0]].x - temp_width;
          t_point.y = vertices_total[temp_Source[0]].y - temp_width;
          Vsource[i].coord.push_back(t_point);
          t_point.x = vertices_total[temp_Source[0]].x + temp_width;
          t_point.y = vertices_total[temp_Source[0]].y + temp_width;
          Vsource[i].coord.push_back(t_point);
          Vsource[i].metalIdx = vertices_total[temp_Source[0]].metal;
          break;
        } else {
          logger->error("Router-Warning: cannot find grid point for source terminal");
        }
      }

    } else {
      // logger->debug("Router-Info: detecting checkpoint4 {0}", i);
      // for stiner node
      if (Smap.find(source.coord[0]) == Smap.end()) {
        for (int temp_metalIdx = lowest_metal; temp_metalIdx <= highest_metal; temp_metalIdx++) {
          temp_Source = Mapping_function_stiner(source, temp_metalIdx);
          if (temp_Source.size() > 0) {
            for (unsigned int j = 0; j < temp_Source.size(); j++) {
              Source.push_back(temp_Source[j]);
            }
            Smap.insert(map<RouterDB::point, std::vector<int>>::value_type(source.coord[0], temp_Source));
            break;
          } else {
            logger->error("Router-Warning: cannot find grid point for source steiner node");
          }
        }
      } else {
        temp_Source = Smap[source.coord[0]];
        for (unsigned int j = 0; j < temp_Source.size(); j++) {
          Source.push_back(temp_Source[j]);
        }
      }
    }
  }
  if (Vsource.size() > 0 && Source.empty()) {
    logger->error("Router-Error: fail to find source vertices on grids");
    return Terminal_contact;
  }
  // for dest

  for (unsigned int i = 0; i < Vdest.size(); i++) {
    dest = Vdest[i];
    std::vector<int> temp_Dest;
    if (dest.coord.size() > 1) {
      // for pin

      temp_Dest = Mapping_function_pin(dest);

      for (unsigned int j = 0; j < temp_Dest.size(); j++) {
        Dest.push_back(temp_Dest[j]);
      }

    } else if (dest.metalIdx != -1) {
      // for terminal
      int min_dis = INT_MAX;
      int direction = 0;
      // wbxu: similar issue to source part [fixed]
      if (abs(dest.coord[0].x - 0) < min_dis) {
        direction = 0;  // 0 is v
        min_dis = abs(dest.coord[0].x - 0);
      }
      if (abs(dest.coord[0].x - width) < min_dis) {
        direction = 0;
        min_dis = abs(dest.coord[0].x - width);
      }
      if (abs(dest.coord[0].y - 0) < min_dis) {
        direction = 1;
        min_dis = abs(dest.coord[0].y - 0);
      }
      if (abs(dest.coord[0].y - height) < min_dis) {
        direction = 1;
        min_dis = abs(dest.coord[0].y - height);
      }

      for (int temp_MetalIdx = lowest_metal; temp_MetalIdx <= highest_metal; temp_MetalIdx++) {
        temp_Dest = Mapping_function_terminal(dest, temp_MetalIdx, direction);
        if (temp_Dest.size() > 0) {
          for (unsigned int j = 0; j < temp_Dest.size(); j++) {
            int myext = this->drc_info.Metal_info.at(vertices_total[temp_Dest[j]].metal).width / 2;
            Dest.push_back(temp_Dest[j]);
            terminal_contact.metal = vertices_total[temp_Dest[j]].metal;
            terminal_contact.placedCenter.x = vertices_total[temp_Dest[j]].x;
            terminal_contact.placedCenter.y = vertices_total[temp_Dest[j]].y;
            terminal_contact.placedLL.x = terminal_contact.placedCenter.x - myext;
            terminal_contact.placedLL.y = terminal_contact.placedCenter.y - myext;
            terminal_contact.placedUR.x = terminal_contact.placedCenter.x + myext;
            terminal_contact.placedUR.y = terminal_contact.placedCenter.y + myext;
            // std::cout<<"INFO:: terminal contact metal"<<terminal_contact.metal<<" "<<terminal_contact.placedLL.x<<","<<terminal_contact.placedLL.y<<";
            // "<<terminal_contact.placedUR.x<<","<<terminal_contact.placedUR.y<<std::endl;
            Terminal_contact.push_back(terminal_contact);
          }

          int temp_width = 1;
          Vdest[i].coord.clear();
          RouterDB::point t_point;
          t_point.x = vertices_total[temp_Dest[0]].x - temp_width;
          t_point.y = vertices_total[temp_Dest[0]].y - temp_width;
          Vdest[i].coord.push_back(t_point);
          t_point.x = vertices_total[temp_Dest[0]].x + temp_width;
          t_point.y = vertices_total[temp_Dest[0]].y + temp_width;
          Vdest[i].coord.push_back(t_point);
          Vdest[i].metalIdx = vertices_total[temp_Dest[0]].metal;
          break;
        } else {
          logger->error("Router-Error: cannot find grid point for dest terminal");
        }
        // std::cout<<"set dest check point 4"<<std::endl;
      }

    } else {
      // for stiner node

      if (Smap.find(dest.coord[0]) == Smap.end()) {
        for (int temp_metalIdx = lowest_metal; temp_metalIdx <= highest_metal; temp_metalIdx++) {
          temp_Dest = Mapping_function_stiner(dest, temp_metalIdx);
          if (temp_Dest.size() > 0) {
            for (unsigned int j = 0; j < temp_Dest.size(); j++) {
              Dest.push_back(temp_Dest[j]);
            }
            Smap.insert(map<RouterDB::point, std::vector<int>>::value_type(dest.coord[0], temp_Dest));
            break;
          } else {
            logger->error("Router-Error: cannot find grid point for source steiner node");
          }
        }
      } else {
        temp_Dest = Smap[dest.coord[0]];
        for (unsigned int j = 0; j < temp_Dest.size(); j++) {
          Dest.push_back(temp_Dest[j]);
        }
      }
    }
  }
  if (Vdest.size() > 0 && Dest.empty()) {
    logger->error("Router-Error: fail to find dest vertices on grids");
    return Terminal_contact;
  }

  return Terminal_contact;
}

std::vector<RouterDB::contact> Grid::setSrcDest_detail(std::vector<RouterDB::SinkData>& Vsource, std::vector<RouterDB::SinkData>& Vdest, int width, int height,
                                                       std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp>& Smap) {
  auto logger = spdlog::default_logger()->clone("router.Grid.setSrcDest_detail");

  Source.clear();
  Dest.clear();
  std::vector<RouterDB::contact> Terminal_contact;
  RouterDB::contact terminal_contact;
  RouterDB::SinkData source, dest;
  // for source
  for (unsigned int i = 0; i < Vsource.size(); i++) {
    // logger->debug("Router-Info: detecting source detailed- {0}", i);
    source = Vsource[i];
    std::vector<int> temp_Source;
    if (source.coord.size() > 1) {
      // for pin
      temp_Source = Mapping_function_pin_detail(source);
      for (unsigned int j = 0; j < temp_Source.size(); j++) {
        Source.push_back(temp_Source[j]);
      }
    } else if (source.metalIdx != -1) {
      // for terminal
      int min_dis = INT_MAX;
      // wbxu: another logic problem in the following [fixed]
      int direction = 0;
      if (abs(source.coord[0].x - 0) < min_dis) {
        direction = 0;
        min_dis = abs(source.coord[0].x - 0);
      }
      if (abs(source.coord[0].x - width) < min_dis) {
        direction = 0;
        min_dis = abs(source.coord[0].x - width);
      }
      if (abs(source.coord[0].y - 0) < min_dis) {
        direction = 1;
        min_dis = abs(source.coord[0].y - 0);
      }
      if (abs(source.coord[0].y - height) < min_dis) {
        direction = 1;
        min_dis = abs(source.coord[0].y - height);
      }

      for (int temp_MetalIdx = lowest_metal; temp_MetalIdx <= highest_metal; temp_MetalIdx++) {
        temp_Source = Mapping_function_terminal(source, temp_MetalIdx, direction);
        if (temp_Source.size() > 0) {
          for (unsigned int j = 0; j < temp_Source.size(); j++) {
            int myext = this->drc_info.Metal_info.at(vertices_total[temp_Source[j]].metal).width / 2;
            Source.push_back(temp_Source[j]);
            terminal_contact.metal = vertices_total[temp_Source[j]].metal;
            terminal_contact.placedCenter.x = vertices_total[temp_Source[j]].x;
            terminal_contact.placedCenter.y = vertices_total[temp_Source[j]].y;
            terminal_contact.placedLL.x = terminal_contact.placedCenter.x - myext;
            terminal_contact.placedLL.y = terminal_contact.placedCenter.y - myext;
            terminal_contact.placedUR.x = terminal_contact.placedCenter.x + myext;
            terminal_contact.placedUR.y = terminal_contact.placedCenter.y + myext;
            Terminal_contact.push_back(terminal_contact);
          }
          int temp_width = 1;
          Vsource[i].coord.clear();
          RouterDB::point t_point;
          t_point.x = vertices_total[temp_Source[0]].x - temp_width;
          t_point.y = vertices_total[temp_Source[0]].y - temp_width;
          Vsource[i].coord.push_back(t_point);
          t_point.x = vertices_total[temp_Source[0]].x + temp_width;
          t_point.y = vertices_total[temp_Source[0]].y + temp_width;
          Vsource[i].coord.push_back(t_point);
          Vsource[i].metalIdx = vertices_total[temp_Source[0]].metal;
          break;
        } else {
          logger->error("Router-Warning: cannot find grid point for source terminal");
        }
      }

    } else {
      // for stiner node
      if (Smap.find(source.coord[0]) == Smap.end()) {
        for (int temp_metalIdx = lowest_metal; temp_metalIdx <= highest_metal; temp_metalIdx++) {
          temp_Source = Mapping_function_stiner(source, temp_metalIdx);
          if (temp_Source.size() > 0) {
            for (unsigned int j = 0; j < temp_Source.size(); j++) {
              Source.push_back(temp_Source[j]);
            }
            /*
            Vsource[i].coord.clear();
            RouterDB::point t_point;
            t_point.x = vertices_total[temp_Source[0]].x;
            t_point.y = vertices_total[temp_Source[0]].y;
            Vsource[i].coord.push_back(t_point);
            Vsource[i].metalIdx = vertices_total[temp_Source[0]].metal;
            */
            Smap.insert(map<RouterDB::point, std::vector<int>>::value_type(source.coord[0], temp_Source));
            break;
          } else {
            logger->error("Router-Error: cannot find grid point for source steiner node");
          }
        }
      } else {
        temp_Source = Smap[source.coord[0]];
        /*
        Vsource[i].coord.clear();
        RouterDB::point t_point;
        t_point.x = vertices_total[temp_Source[0]].x;
        t_point.y = vertices_total[temp_Source[0]].y;
        Vsource[i].coord.push_back(t_point);
        Vsource[i].metalIdx = vertices_total[temp_Source[0]].metal;
        */
        for (unsigned int j = 0; j < temp_Source.size(); j++) {
          Source.push_back(temp_Source[j]);
        }
      }
    }
  }
  if (Vsource.size() > 0 && Source.empty()) {
    logger->error("Router-Error: fail to find source vertices on grids");
    return Terminal_contact;
  }
  // for dest

  for (unsigned int i = 0; i < Vdest.size(); i++) {
    dest = Vdest[i];
    std::vector<int> temp_Dest;
    if (dest.coord.size() > 1) {
      // for pin
      temp_Dest = Mapping_function_pin_detail(dest);
      for (unsigned int j = 0; j < temp_Dest.size(); j++) {
        Dest.push_back(temp_Dest[j]);
      }
    } else if (dest.metalIdx != -1) {
      // for terminal
      int min_dis = INT_MAX;
      int direction = 0;
      // wbxu: similar issue to source part [fixed]
      if (abs(dest.coord[0].x - 0) < min_dis) {
        direction = 0;  // 0 is v
        min_dis = abs(dest.coord[0].x - 0);
      }
      if (abs(dest.coord[0].x - width) < min_dis) {
        direction = 0;
        min_dis = abs(dest.coord[0].x - width);
      }
      if (abs(dest.coord[0].y - 0) < min_dis) {
        direction = 1;
        min_dis = abs(dest.coord[0].y - 0);
      }
      if (abs(dest.coord[0].y - height) < min_dis) {
        direction = 1;
        min_dis = abs(dest.coord[0].y - height);
      }

      for (int temp_MetalIdx = lowest_metal; temp_MetalIdx <= highest_metal; temp_MetalIdx++) {
        temp_Dest = Mapping_function_terminal(dest, temp_MetalIdx, direction);
        if (temp_Dest.size() > 0) {
          for (unsigned int j = 0; j < temp_Dest.size(); j++) {
            int myext = this->drc_info.Metal_info.at(vertices_total[temp_Dest[j]].metal).width / 2;
            Dest.push_back(temp_Dest[j]);
            terminal_contact.metal = vertices_total[temp_Dest[j]].metal;
            terminal_contact.placedCenter.x = vertices_total[temp_Dest[j]].x;
            terminal_contact.placedCenter.y = vertices_total[temp_Dest[j]].y;
            terminal_contact.placedLL.x = terminal_contact.placedCenter.x - myext;
            terminal_contact.placedLL.y = terminal_contact.placedCenter.y - myext;
            terminal_contact.placedUR.x = terminal_contact.placedCenter.x + myext;
            terminal_contact.placedUR.y = terminal_contact.placedCenter.y + myext;
            Terminal_contact.push_back(terminal_contact);
          }

          int temp_width = 1;
          Vdest[i].coord.clear();
          RouterDB::point t_point;
          t_point.x = vertices_total[temp_Dest[0]].x - temp_width;
          t_point.y = vertices_total[temp_Dest[0]].y - temp_width;
          Vdest[i].coord.push_back(t_point);
          t_point.x = vertices_total[temp_Dest[0]].x + temp_width;
          t_point.y = vertices_total[temp_Dest[0]].y + temp_width;
          Vdest[i].coord.push_back(t_point);
          Vdest[i].metalIdx = vertices_total[temp_Dest[0]].metal;
          break;
        } else {
          logger->error("Router-Error: cannot find grid point for dest terminal");
        }
      }

    } else {
      // for stiner node
      if (Smap.find(dest.coord[0]) == Smap.end()) {
        for (int temp_metalIdx = lowest_metal; temp_metalIdx <= highest_metal; temp_metalIdx++) {
          temp_Dest = Mapping_function_stiner(dest, temp_metalIdx);
          if (temp_Dest.size() > 0) {
            for (unsigned int j = 0; j < temp_Dest.size(); j++) {
              Dest.push_back(temp_Dest[j]);
            }
            /*
            Vdest[i].coord.clear();
            RouterDB::point t_point;
            t_point.x = vertices_total[temp_Dest[0]].x;
            t_point.y = vertices_total[temp_Dest[0]].y;
            Vdest[i].coord.push_back(t_point);
            Vdest[i].metalIdx = vertices_total[temp_Dest[0]].metal;
            */
            Smap.insert(map<RouterDB::point, std::vector<int>>::value_type(dest.coord[0], temp_Dest));
            break;
          } else {
            logger->error("Router-Error: cannot find grid point for source steiner node");
          }
        }
      } else {
        temp_Dest = Smap[dest.coord[0]];
        /*
        Vdest[i].coord.clear();
        RouterDB::point t_point;
        t_point.x = vertices_total[temp_Dest[0]].x;
        t_point.y = vertices_total[temp_Dest[0]].y;
        Vdest[i].coord.push_back(t_point);
        Vdest[i].metalIdx = vertices_total[temp_Dest[0]].metal;
        */
        for (unsigned int j = 0; j < temp_Dest.size(); j++) {
          Dest.push_back(temp_Dest[j]);
        }
      }
    }
  }
  if (Vdest.size() > 0 && Dest.empty()) {
    logger->error("Router-Error: fail to find dest vertices on grids");
    return Terminal_contact;
  }

  return Terminal_contact;
}

std::vector<int> Grid::Mapping_function_pin_detail(RouterDB::SinkData& source) {
  std::vector<int> map_source;
  // wbxu: incorrect startpoint and endpoint if source.metalIdx==lowest_metal
  // it results in traversal starting from the second node in the subfunction [fixed]

  if (source.metalIdx < 0 || source.metalIdx > int(drc_info.Metal_info.size())) {
    return map_source;
  }

  if (source.metalIdx == 0) {
    if (drc_info.Metal_info[source.metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_pin_detail(source, drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y,
                                          drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                          Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);

    } else {
      // wbxu: incorrect index in the 5th parameters [fixed]
      // h
      map_source =
          Map_from_seg2gridseg_pin_detail(source, drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                          drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                          Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);
    }

  } else if (source.metalIdx == this->layerNo - 1) {
    if (drc_info.Metal_info[source.metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_pin_detail(source, drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                          drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y, grid_scale,
                                          Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);

    } else {
      // h
      map_source =
          Map_from_seg2gridseg_pin_detail(source, drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                          drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                          Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);
    }

  } else {
    if (drc_info.Metal_info[source.metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_pin_detail(source, drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                          drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                          Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);

    } else {
      // h
      map_source =
          Map_from_seg2gridseg_pin_detail(source, drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                          drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                          Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);
    }
  }
  return map_source;
};

std::vector<int> Grid::Mapping_function_pin(RouterDB::SinkData& source) {
  std::vector<int> map_source;
  // wbxu: incorrect startpoint and endpoint if source.metalIdx==lowest_metal
  // it results in traversal starting from the second node in the subfunction [fixed]

  if (source.metalIdx < 0 || source.metalIdx > int(drc_info.Metal_info.size())) {
    return map_source;
  }

  if (source.metalIdx == 0) {
    if (drc_info.Metal_info[source.metalIdx].direct == 0) {
      // v
      map_source = Map_from_seg2gridseg_pin(source, drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y,
                                            drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                            Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);

    } else {
      // wbxu: incorrect index in the 5th parameters [fixed]
      // h
      map_source = Map_from_seg2gridseg_pin(source, drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                            drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                            Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);
    }

  } else if (source.metalIdx == this->layerNo - 1) {
    if (drc_info.Metal_info[source.metalIdx].direct == 0) {
      // v
      map_source = Map_from_seg2gridseg_pin(source, drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                            drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y, grid_scale,
                                            Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);

    } else {
      // h
      map_source = Map_from_seg2gridseg_pin(source, drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                            drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                            Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);
    }

  } else {
    if (drc_info.Metal_info[source.metalIdx].direct == 0) {
      // v
      map_source = Map_from_seg2gridseg_pin(source, drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                            drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                            Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);

    } else {
      // h
      map_source = Map_from_seg2gridseg_pin(source, drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                            drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                            Start_index_metal_vertices[source.metalIdx], End_index_metal_vertices[source.metalIdx]);
    }
  }
  return map_source;
};

std::vector<int> Grid::Mapping_function_terminal(RouterDB::SinkData& source, int temp_metalIdx, int direction) {
  // wbxu: similar problem to mapping_function_pin [fixed]
  int terminal_stiner_scale = 10;
  std::vector<int> map_source;
  source.metalIdx = temp_metalIdx;
  if (temp_metalIdx == 0) {
    if (drc_info.Metal_info[temp_metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_terminal(source, drc_info.Metal_info[temp_metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y,
                                        drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                        Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale, direction);

    } else {
      // h

      map_source =
          Map_from_seg2gridseg_terminal(source, drc_info.Metal_info[temp_metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                        drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                        Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale, direction);
    }

  } else if (temp_metalIdx == this->layerNo - 1) {
    if (drc_info.Metal_info[temp_metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_terminal(source, drc_info.Metal_info[temp_metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                        drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y, grid_scale,
                                        Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale, direction);

    } else {
      // h
      map_source =
          Map_from_seg2gridseg_terminal(source, drc_info.Metal_info[temp_metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                        drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                        Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale, direction);
    }

  } else {
    if (drc_info.Metal_info[temp_metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_terminal(source, drc_info.Metal_info[temp_metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                        drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                        Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale, direction);

    } else {
      // h

      map_source =
          Map_from_seg2gridseg_terminal(source, drc_info.Metal_info[temp_metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                        drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                        Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale, direction);
    }
  }
  return map_source;
};

std::vector<int> Grid::Mapping_function_stiner(RouterDB::SinkData& source, int temp_metalIdx) {
  // wbxu: similar issue to mapping_function_pin [fixed]
  int terminal_stiner_scale = 5;
  std::vector<int> map_source;
  source.metalIdx = temp_metalIdx;
  if (temp_metalIdx == 0) {
    if (drc_info.Metal_info[temp_metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_stiner(source, drc_info.Metal_info[temp_metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y,
                                      drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                      Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale);

    } else {
      // h

      map_source =
          Map_from_seg2gridseg_stiner(source, drc_info.Metal_info[temp_metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                      drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                      Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale);
    }

  } else if (temp_metalIdx == this->layerNo - 1) {
    if (drc_info.Metal_info[temp_metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_stiner(source, drc_info.Metal_info[temp_metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                      drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y, grid_scale,
                                      Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale);

    } else {
      // h
      map_source =
          Map_from_seg2gridseg_stiner(source, drc_info.Metal_info[temp_metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                      drc_info.Metal_info[source.metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                      Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale);
    }

  } else {
    if (drc_info.Metal_info[temp_metalIdx].direct == 0) {
      // v
      map_source =
          Map_from_seg2gridseg_stiner(source, drc_info.Metal_info[temp_metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx - 1].grid_unit_y,
                                      drc_info.Metal_info[source.metalIdx].grid_unit_x, drc_info.Metal_info[source.metalIdx + 1].grid_unit_y, grid_scale,
                                      Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale);

    } else {
      // h

      map_source =
          Map_from_seg2gridseg_stiner(source, drc_info.Metal_info[temp_metalIdx - 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y,
                                      drc_info.Metal_info[source.metalIdx + 1].grid_unit_x, drc_info.Metal_info[source.metalIdx].grid_unit_y, grid_scale,
                                      Start_index_metal_vertices[temp_metalIdx], End_index_metal_vertices[temp_metalIdx], terminal_stiner_scale);
    }
  }
  return map_source;
};

std::vector<int> Grid::Map_from_seg2gridseg_pin(RouterDB::SinkData& sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                                int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3) {
  auto logger = spdlog::default_logger()->clone("router.Grid.Map_from_seg2gridseg_pin");

  int Lx, Ly, Ux, Uy;
  int grid_Lx, grid_Ly, grid_Ux, grid_Uy, grid_Lx1, grid_Ly1, grid_Ux1, grid_Uy1;
  Lx = sourcelist.coord[0].x;
  Ly = sourcelist.coord[0].y;
  Ux = sourcelist.coord[1].x;
  Uy = sourcelist.coord[1].y;
  std::set<RouterDB::point, RouterDB::pointXYComp> grid_node_coord;
  std::set<RouterDB::point, RouterDB::pointXYComp> covered_node_coord;
  RouterDB::point grid_node;
  // SinkData sourceL;
  // find the grid point nearby and insert it to the grid_seg;

  grid_Lx = Lx;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Lx -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Lx -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  grid_Lx = grid_Lx / (grid_unit_x * grid_scale_func);
  grid_Lx = grid_Lx * (grid_unit_x * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx += drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Lx += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Lx += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  // cout<<grid_Lx<<endl;

  grid_Ux = Ux;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  grid_Ux = (int)ceil(double(grid_Ux) / (grid_unit_x * grid_scale_func));
  grid_Ux = grid_Ux * (grid_unit_x * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Ux += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ux += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  // cout<<grid_Ux<<endl;

  grid_Ly = Ly;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Ly -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ly -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Ly -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Ly = grid_Ly / (grid_unit_y * grid_scale_func);
  grid_Ly = grid_Ly * (grid_unit_y * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Ly += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ly += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Ly += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }

  // cout<<grid_Ly<<endl;

  grid_Uy = Uy;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Uy -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Uy -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Uy -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Uy = (int)ceil(double(grid_Uy) / (grid_unit_y * grid_scale_func));
  grid_Uy = grid_Uy * (grid_unit_y * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Uy += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Uy += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Uy += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  // cout<<grid_Uy<<endl;

  grid_Lx1 = Lx;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  grid_Lx1 = grid_Lx1 / (grid_unit_x1 * grid_scale_func);
  grid_Lx1 = grid_Lx1 * (grid_unit_x1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Lx1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Lx1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  // cout<<grid_Lx1<<endl;

  grid_Ux1 = Ux;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  grid_Ux1 = (int)ceil(double(grid_Ux1) / (grid_unit_x1 * grid_scale_func));
  grid_Ux1 = grid_Ux1 * (grid_unit_x1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ux1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ux1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  // cout<<grid_Ux1<<endl;

  grid_Ly1 = Ly;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ly1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ly1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Ly1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Ly1 = grid_Ly1 / (grid_unit_y1 * grid_scale_func);
  grid_Ly1 = grid_Ly1 * (grid_unit_y1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ly1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ly1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Ly1 += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  // cout<<grid_Ly1<<endl;

  grid_Uy1 = Uy;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Uy1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Uy1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Uy1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Uy1 = (int)ceil(double(grid_Uy1) / (grid_unit_y1 * grid_scale_func));
  grid_Uy1 = grid_Uy1 * (grid_unit_y1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Uy1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Uy1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Uy1 += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  // cout<<grid_Uy1<<endl;

  for (int i = 0; i <= (grid_Ux - grid_Lx) / (grid_unit_x * grid_scale_func); i++) {
    grid_node.x = grid_Lx + i * grid_unit_x * grid_scale_func;
    if (grid_node.x >= Lx && grid_node.x <= Ux) {
      for (int j = 0; j <= (grid_Uy - grid_Ly) / (grid_unit_y * grid_scale_func); j++) {
        grid_node.y = grid_Ly + j * grid_unit_y * grid_scale_func;
        if (grid_node.y >= Ly && grid_node.y <= Uy) grid_node_coord.insert(grid_node);
      }
    }
  }
  // wbxu: the following codes can be optimized by using Set
  std::set<RouterDB::point, RouterDB::pointXYComp> new_grid_node_coord;
  for (int i = 0; i <= (grid_Ux1 - grid_Lx1) / (grid_unit_x1 * grid_scale_func); i++) {
    grid_node.x = grid_Lx1 + i * grid_unit_x1 * grid_scale_func;
    if (grid_node.x >= Lx && grid_node.x <= Ux) {
      for (int j = 0; j <= (grid_Uy1 - grid_Ly1) / (grid_unit_y1 * grid_scale_func); j++) {
        grid_node.y = grid_Ly1 + j * grid_unit_y1 * grid_scale_func;
        if (grid_node.y >= Ly && grid_node.y <= Uy) grid_node_coord.insert(grid_node);
      }
    }
  }

  std::vector<int> sourceL;
  for (int i = index_end_M1_M2; i <= index_end_M3_M3; i++) {
    RouterDB::point cand;
    cand.x = vertices_total[i].x;
    cand.y = vertices_total[i].y;
    if (grid_node_coord.find(cand) != grid_node_coord.end()) {
      sourceL.push_back(i);
    }
  }
  // std::cout<<std::endl;
  // logger->debug("Grid region ({0},{1}) ({2},{3})", grid_region_llx, grid_region_lly, grid_region_urx, grid_region_ury);

  return sourceL;
};

std::vector<int> Grid::Map_from_seg2gridseg_pin_detail(RouterDB::SinkData& sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                                       int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3) {
  int Lx, Ly, Ux, Uy;
  int grid_Lx, grid_Ly, grid_Ux, grid_Uy, grid_Lx1, grid_Ly1, grid_Ux1, grid_Uy1;
  Lx = sourcelist.coord[0].x;
  Ly = sourcelist.coord[0].y;
  Ux = sourcelist.coord[1].x;
  Uy = sourcelist.coord[1].y;
  std::set<RouterDB::point, RouterDB::pointXYComp> grid_node_coord;
  std::set<RouterDB::point, RouterDB::pointXYComp> covered_node_coord;
  RouterDB::point grid_node;
  // SinkData sourceL;
  // find the grid point nearby and insert it to the grid_seg;

  grid_Lx = Lx;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Lx -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Lx -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  grid_Lx = grid_Lx / (grid_unit_x * grid_scale_func);
  grid_Lx = grid_Lx * (grid_unit_x * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx += drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Lx += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Lx += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  // cout<<grid_Lx<<endl;

  grid_Ux = Ux;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  grid_Ux = (int)ceil(double(grid_Ux) / (grid_unit_x * grid_scale_func));
  grid_Ux = grid_Ux * (grid_unit_x * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx > 0)
      grid_Ux += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ux += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  }
  // cout<<grid_Ux<<endl;

  grid_Ly = Ly;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Ly -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ly -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Ly -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Ly = grid_Ly / (grid_unit_y * grid_scale_func);
  grid_Ly = grid_Ly * (grid_unit_y * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Ly += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Ly += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Ly += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }

  // cout<<grid_Ly<<endl;

  grid_Uy = Uy;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Uy -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Uy -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Uy -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Uy = (int)ceil(double(grid_Uy) / (grid_unit_y * grid_scale_func));
  grid_Uy = grid_Uy * (grid_unit_y * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx > 0)
      grid_Uy += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
    else
      grid_Uy += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
  } else {
    grid_Uy += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  // cout<<grid_Uy<<endl;

  grid_Lx1 = Lx;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  grid_Lx1 = grid_Lx1 / (grid_unit_x1 * grid_scale_func);
  grid_Lx1 = grid_Lx1 * (grid_unit_x1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Lx1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Lx1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Lx1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  // cout<<grid_Lx1<<endl;

  grid_Ux1 = Ux;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  grid_Ux1 = (int)ceil(double(grid_Ux1) / (grid_unit_x1 * grid_scale_func));
  grid_Ux1 = grid_Ux1 * (grid_unit_x1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0)
    grid_Ux1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  else {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ux1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ux1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  }
  // cout<<grid_Ux1<<endl;

  grid_Ly1 = Ly;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ly1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ly1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Ly1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Ly1 = grid_Ly1 / (grid_unit_y1 * grid_scale_func);
  grid_Ly1 = grid_Ly1 * (grid_unit_y1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Ly1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Ly1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Ly1 += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  // cout<<grid_Ly1<<endl;

  grid_Uy1 = Uy;
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Uy1 -= drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Uy1 -= drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Uy1 -= drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  grid_Uy1 = (int)ceil(double(grid_Uy1) / (grid_unit_y1 * grid_scale_func));
  grid_Uy1 = grid_Uy1 * (grid_unit_y1 * grid_scale_func);
  if (drc_info.Metal_info[sourcelist.metalIdx].direct == 0) {
    if (sourcelist.metalIdx < this->layerNo - 1)
      grid_Uy1 += drc_info.Metal_info[sourcelist.metalIdx + 1].offset;
    else
      grid_Uy1 += drc_info.Metal_info[sourcelist.metalIdx - 1].offset;
  } else {
    grid_Uy1 += drc_info.Metal_info[sourcelist.metalIdx].offset;
  }
  // cout<<grid_Uy1<<endl;

  for (int i = 0; i <= (grid_Ux - grid_Lx) / (grid_unit_x * grid_scale_func); i++) {
    grid_node.x = grid_Lx + i * grid_unit_x * grid_scale_func;
    if (grid_node.x>= Lx && grid_node.x<= Ux) {
      for (int j = 0; j <= (grid_Uy - grid_Ly) / (grid_unit_y * grid_scale_func); j++) {
        grid_node.y = grid_Ly + j * grid_unit_y * grid_scale_func;
        if (grid_node.y >= Ly && grid_node.y <= Uy) grid_node_coord.insert(grid_node);
      }
    }
  }
  // wbxu: the following codes can be optimized by using Set
  for (int i = 0; i <= (grid_Ux1 - grid_Lx1) / (grid_unit_x1 * grid_scale_func); i++) {
    grid_node.x = grid_Lx1 + i * grid_unit_x1 * grid_scale_func;
    if (grid_node.x>= Lx && grid_node.x<= Ux) {
      for (int j = 0; j <= (grid_Uy1 - grid_Ly1) / (grid_unit_y1 * grid_scale_func); j++) {
        grid_node.y = grid_Ly1 + j * grid_unit_y1 * grid_scale_func;
        if (grid_node.y >= Ly && grid_node.y <= Uy) grid_node_coord.insert(grid_node);
      }
    }
  }

  std::vector<int> sourceL;
  for (int i = index_end_M1_M2; i <= index_end_M3_M3; i++) {
    if (vertices_total[i].active == 1) {
      RouterDB::point cand;
      cand.x = vertices_total[i].x;
      cand.y = vertices_total[i].y;
      if (grid_node_coord.find(cand) != grid_node_coord.end()) {
        sourceL.push_back(i);
      }
    }
  }
  return sourceL;
};

bool Grid::CheckExtendable(int i, int metal) {
  bool feasible = true;

  int minL = drc_info.Metal_info[metal].minL;

  int half_minL = ceil(minL / 2);

  int up_direction = 1;

  int down_direction = -1;

  bool search_flag = true;
  int culmulated_length = 0;
  int dummy_node = i;
  while (search_flag) {
    if (culmulated_length >= half_minL) {
      search_flag = false;
    } else {
      unsigned int next_node = dummy_node + up_direction;
      if (next_node < 0 || next_node >= vertices_total.size()) {
        search_flag = false;
        feasible = false;
      } else if (vertices_total[next_node].active == 0) {
        search_flag = false;
        feasible = false;
      } else if ((vertices_total[next_node].x != vertices_total[i].x && vertices_total[next_node].y != vertices_total[i].y) ||
                 vertices_total[next_node].metal != vertices_total[i].metal) {
        search_flag = false;
        feasible = false;
      } else {
        culmulated_length = abs(vertices_total[next_node].x - vertices_total[i].x) + abs(vertices_total[next_node].y - vertices_total[i].y);
        dummy_node = next_node;
      }
    }
  }

  culmulated_length = 0;
  dummy_node = i;
  while (search_flag) {
    if (culmulated_length >= half_minL) {
      search_flag = false;
    } else {
      unsigned int next_node = dummy_node + down_direction;
      if (next_node < 0 || next_node >= vertices_total.size()) {
        search_flag = false;
        feasible = false;
      } else if (vertices_total[next_node].active == 0) {
        search_flag = false;
        feasible = false;
      } else if ((vertices_total[next_node].x != vertices_total[i].x && vertices_total[next_node].y != vertices_total[i].y) ||
                 vertices_total[next_node].metal != vertices_total[i].metal) {
        search_flag = false;
        feasible = false;
      } else {
        culmulated_length = abs(vertices_total[next_node].x - vertices_total[i].x) + abs(vertices_total[next_node].y - vertices_total[i].y);
        dummy_node = next_node;
      }
    }
  }

  return feasible;
};

std::vector<int> Grid::Map_from_seg2gridseg_terminal(RouterDB::SinkData& sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                                     int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3, int range, int direction) {
  auto logger = spdlog::default_logger()->clone("router.Grid.Map_from_seg2gridseg_terminal");

  // wbxu: similar issue to map_from_seg2gridseg_pin [fixed]
  // direction 1 h, 0 v
  int Cx, Cy;
  int grid_x, grid_y, grid_x1, grid_y1;
  Cx = sourcelist.coord[0].x;
  Cy = sourcelist.coord[0].y;

  // find the grid point nearby and insert it to the grid_seg;
  grid_x = Cx / (grid_unit_x * grid_scale_func);
  grid_x = grid_x * (grid_unit_x * grid_scale_func);

  grid_y = Cy / (grid_unit_y * grid_scale_func);
  grid_y = grid_y * (grid_unit_y * grid_scale_func);

  grid_x1 = Cx / (grid_unit_x1 * grid_scale_func);
  grid_x1 = grid_x1 * (grid_unit_x1 * grid_scale_func);

  grid_y1 = Cy / (grid_unit_y1 * grid_scale_func);
  grid_y1 = grid_y1 * (grid_unit_y1 * grid_scale_func);

  // use those four node to find all the grid point nearby
  std::vector<RouterDB::point> grid_node_coord;
  RouterDB::point grid_node;
  std::vector<int> sourceL;
  for (int i = -range * direction; i <= range * direction; i++) {
    for (int j = -range * (1 - direction); j <= range * (1 - direction); j++) {
      grid_node.x = grid_x + i * grid_unit_x * grid_scale_func;
      grid_node.y = grid_y + j * grid_unit_y * grid_scale_func;
      grid_node_coord.push_back(grid_node);
    }
  }
  std::vector<RouterDB::point> new_grid_node_coord;
  for (int i = -range * direction; i <= range * direction; i++) {
    for (int j = -range * (1 - direction); j <= range * (1 - direction); j++) {
      grid_node.x = grid_x1 + i * grid_unit_x1 * grid_scale_func;
      grid_node.y = grid_y1 + j * grid_unit_y1 * grid_scale_func;
      int flag_found = 0;
      for (unsigned int k = 0; k < grid_node_coord.size(); k++) {
        if (grid_node_coord[k].x == grid_node.x && grid_node_coord[k].y == grid_node.y) {
          flag_found = 1;
        }
      }
      if (flag_found == 0) {
        new_grid_node_coord.push_back(grid_node);
      }
    }
  }
  for (unsigned int i = 0; i < new_grid_node_coord.size(); i++) {
    grid_node_coord.push_back(new_grid_node_coord[i]);
  }

  // sourceL.metal = sourcelist.metal;

  int grid_distance = INT_MAX;
  int min_index = -1;
  // int grid_idx;
  // for(int i=0;i<grid_node_coord.size();i++){
  // std::cout<<"( "<<grid_node_coord[i].x<<" "<<grid_node_coord[i].y<<") ";
  //}
  // std::cout<<std::endl;
  // std::cout<<"Grid points:"<<std::endl;

  int grid_region_llx = INT_MAX;
  int grid_region_lly = INT_MAX;

  int grid_region_urx = INT_MIN;
  int grid_region_ury = INT_MIN;

  for (int i = index_end_M1_M2; i <= index_end_M3_M3; i++) {
    // std::cout<<"( "<<vertices_total[i].x<<" "<<vertices_total[i].y<<" "<<vertices_total[i].active<<") ";

    if (vertices_total[i].x > grid_region_urx) {
      grid_region_urx = vertices_total[i].x;
    }
    if (vertices_total[i].x < grid_region_llx) {
      grid_region_llx = vertices_total[i].x;
    }
    if (vertices_total[i].y > grid_region_ury) {
      grid_region_ury = vertices_total[i].y;
    }
    if (vertices_total[i].y < grid_region_lly) {
      grid_region_lly = vertices_total[i].y;
    }

    for (unsigned int j = 0; j < grid_node_coord.size(); j++) {
      if ((grid_node_coord[j].x == vertices_total[i].x) && (grid_node_coord[j].y == vertices_total[i].y) && (vertices_total[i].active == 1) &&
          (CheckExtendable(i, vertices_total[i].metal))) {
        int dist = abs(grid_node_coord[j].x - Cx) + abs(grid_node_coord[j].y - Cy);
        // std::cout<<"dist "<<dist<<std::endl;
        if (dist < grid_distance) {
          grid_distance = dist;
          min_index = i;
        }  // grid_idx=j;}
        break;
        // sourceL.ver_idx.push_back(vertices_total[i].index);
      }
    }
  }
  // std::cout<<std::endl;
  // logger->debug("Grid region ({0},{1}) ({2},{3})", grid_region_llx, grid_region_lly, grid_region_urx, grid_region_ury);

  if (min_index != -1) {
    sourceL.push_back(min_index);
    // sourceL.coord.push_back( grid_node_coord[grid_idx]  );
    // std::cout<<vertices_total[min_index].x<<","<<vertices_total[min_index].y<<","<<min_index<<std::endl;
    // std::cout<<"Can map from seg to grid seg: "<<Cx<<" "<<Cy<<" "<<grid_scale_func<<std::endl;
  } else {
    logger->error("Router-Warning: cannot map from seg to grid seg: {0} {1} {2}", Cx, Cy, grid_scale_func);
    // std::cout<<"grid_x"<<" "<<grid_x<<" grid_y "<<grid_y<<" grid_x1 "<<grid_x1<<" grid_y1 "<<grid_y1<<std::endl;
    // std::cout<<"grid_unit_x"<<" "<<grid_unit_x<<" grid_unit_y "<<grid_unit_y<<" grid_unit_x1 "<<grid_unit_x1<<" grid_unit_y1 "<<grid_unit_y1<<std::endl;
    // for(int l=0;l<grid_node_coord.size();l++){
    //   std::cout<<grid_node_coord[l].x<<" "<<grid_node_coord[l].y<<std::endl;
    //}
  }

  return sourceL;
};

std::vector<int> Grid::Map_from_seg2gridseg_stiner(RouterDB::SinkData& sourcelist, int grid_unit_x, int grid_unit_y, int grid_unit_x1, int grid_unit_y1,
                                                   int grid_scale_func, int index_end_M1_M2, int index_end_M3_M3, int range) {
  auto logger = spdlog::default_logger()->clone("router.Grid.Map_from_seg2gridseg_stiner");

  // wbxu: similar issue to map_from_seg2_gridseg_pin [fixed]
  int Cx, Cy;
  int grid_x, grid_y, grid_x1, grid_y1;
  Cx = sourcelist.coord[0].x;
  Cy = sourcelist.coord[0].y;

  // find the grid point nearby and insert it to the grid_seg;
  grid_x = Cx / (grid_unit_x * grid_scale_func);
  grid_x = grid_x * (grid_unit_x * grid_scale_func);

  grid_y = Cy / (grid_unit_y * grid_scale_func);
  grid_y = grid_y * (grid_unit_y * grid_scale_func);

  grid_x1 = Cx / (grid_unit_x1 * grid_scale_func);
  grid_x1 = grid_x1 * (grid_unit_x1 * grid_scale_func);

  grid_y1 = Cy / (grid_unit_y1 * grid_scale_func);
  grid_y1 = grid_y1 * (grid_unit_y1 * grid_scale_func);

  // use those four node to find all the grid point nearby
  std::vector<RouterDB::point> grid_node_coord;
  RouterDB::point grid_node;
  std::vector<int> sourceL;
  for (int i = -range; i <= range; i++) {
    for (int j = -range; j <= range; j++) {
      grid_node.x = grid_x + i * grid_unit_x * grid_scale_func;
      grid_node.y = grid_y + j * grid_unit_y * grid_scale_func;
      grid_node_coord.push_back(grid_node);
    }
  }
  std::vector<RouterDB::point> new_grid_node_coord;
  for (int i = -range; i <= range; i++) {
    for (int j = -range; j <= range; j++) {
      grid_node.x = grid_x1 + i * grid_unit_x1 * grid_scale_func;
      grid_node.y = grid_y1 + j * grid_unit_y1 * grid_scale_func;
      int flag_found = 0;
      for (unsigned int k = 0; k < grid_node_coord.size(); k++) {
        if (grid_node_coord[k].x == grid_node.x && grid_node_coord[k].y == grid_node.y) {
          flag_found = 1;
        }
      }
      if (flag_found == 0) {
        new_grid_node_coord.push_back(grid_node);
      }
    }
  }
  for (unsigned int i = 0; i < new_grid_node_coord.size(); i++) {
    grid_node_coord.push_back(new_grid_node_coord[i]);
  }

  // sourceL.metal = sourcelist.metal;
  /*
      int grid_distance=INT_MAX;
      int min_index=-1;
      int grid_idx;

      for(int i=index_end_M1_M2;i<index_end_M3_M3;i++){
          for(int j=0;j<grid_node_coord.size();j++){
             if((grid_node_coord[j].x==vertices_total[i].x)&&(grid_node_coord[j].y==vertices_total[i].y)&&(vertices_total[i].active==1)) {
                  sourceL.coord.push_back( grid_node_coord[j] );
                  sourceL.ver_idx.push_back(vertices_total[i].index);
                          }
                }
          }

  if(sourceL.coord.size()<25){
    sourceL.coord.clear();
    sourceL.ver_idx.clear();
  }
  */

  int grid_distance = INT_MAX;
  int min_index = -1;
  // int grid_idx;
  // std::cout<<"grid_node_coord.size(): "<<grid_node_coord.size()<<std::endl;
  for (int i = index_end_M1_M2; i <= index_end_M3_M3; i++) {
    for (unsigned int j = 0; j < grid_node_coord.size(); j++) {
      if ((grid_node_coord[j].x == vertices_total[i].x) && (grid_node_coord[j].y == vertices_total[i].y) && (vertices_total[i].active == 1)) {
        int dist = abs(grid_node_coord[j].x - Cx) + abs(grid_node_coord[j].y - Cy);
        // std::cout<<"dist "<<dist<<std::endl;
        if (dist < grid_distance) {
          grid_distance = dist;
          min_index = i;
        }  // grid_idx=j;}
        break;
        // sourceL.ver_idx.push_back(vertices_total[i].index);
      }
    }
  }
  if (min_index != -1) {
    sourceL.push_back(min_index);
    // sourceL.coord.push_back( grid_node_coord[grid_idx]  );
    // std::cout<<vertices_total[min_index].x<<","<<vertices_total[min_index].y<<","<<min_index<<std::endl;
    // std::cout<<"Can map from seg to grid seg: "<<Cx<<" "<<Cy<<" "<<grid_scale_func<<std::endl;
  } else {
    logger->error("Router-Warning: cannot map from seg to grid seg steiner: {0} {1} {2}", Cx, Cy, grid_scale_func);
    // std::cout<<"grid_x"<<" "<<grid_x<<" grid_y "<<grid_y<<" grid_x1 "<<grid_x1<<" grid_y1 "<<grid_y1<<std::endl;
    // std::cout<<"grid_unit_x"<<" "<<grid_unit_x<<" grid_unit_y "<<grid_unit_y<<" grid_unit_x1 "<<grid_unit_x1<<" grid_unit_y1 "<<grid_unit_y1<<std::endl;
    // for(int l=0;l<grid_node_coord.size();l++){
    //   std::cout<<grid_node_coord[l].x<<" "<<grid_node_coord[l].y<<std::endl;
    //}
  }

  return sourceL;
};

std::vector<RouterDB::point> Grid::GetMaxMinSrcDest() {
  int x = INT_MAX, y = INT_MAX, X = INT_MIN, Y = INT_MIN;
  for (std::vector<int>::iterator it = this->Source.begin(); it != this->Source.end(); ++it) {
    int Sx = vertices_total.at(*it).x;
    int Sy = vertices_total.at(*it).y;
    if (Sx > X) {
      X = Sx;
    }
    if (Sx < x) {
      x = Sx;
    }
    if (Sy > Y) {
      Y = Sy;
    }
    if (Sy < y) {
      y = Sy;
    }
  }
  for (std::vector<int>::iterator it = this->Dest.begin(); it != this->Dest.end(); ++it) {
    int Dx = vertices_total.at(*it).x;
    int Dy = vertices_total.at(*it).y;
    if (Dx > X) {
      X = Dx;
    }
    if (Dx < x) {
      x = Dx;
    }
    if (Dy > Y) {
      Y = Dy;
    }
    if (Dy < y) {
      y = Dy;
    }
  }
  int xMar, yMar;
  if (this->drc_info.Metal_info.at(this->highest_metal).direct == 0) {  // vertical
    xMar = this->drc_info.Metal_info.at(this->highest_metal).grid_unit_x * this->grid_scale;
    yMar = this->drc_info.Metal_info.at(this->highest_metal - 1).grid_unit_y * this->grid_scale;
  } else {  // horizontal
    yMar = this->drc_info.Metal_info.at(this->highest_metal).grid_unit_y * this->grid_scale;
    xMar = this->drc_info.Metal_info.at(this->highest_metal - 1).grid_unit_x * this->grid_scale;
  }
  RouterDB::point newnode;
  std::vector<RouterDB::point> newlist;
  newnode.x = x - 4 * xMar;
  newnode.y = y - 4 * yMar;
  if (newnode.x < this->LL.x) {
    newnode.x = this->LL.x;
  }
  if (newnode.y < this->LL.y) {
    newnode.y = this->LL.y;
  }
  newlist.push_back(newnode);
  newnode.x = X + 4 * xMar;
  newnode.y = Y + 4 * yMar;
  if (newnode.x > this->UR.x) {
    newnode.x = this->UR.x;
  }
  if (newnode.y > this->UR.y) {
    newnode.y = this->UR.y;
  }
  newlist.push_back(newnode);
  return newlist;
};

void Grid::CheckVerticesTotal() {
  auto logger = spdlog::default_logger()->clone("router.Grid.CheckVerticesTotal");

  logger->debug("===CheckVerticesTotal===");
  for (std::vector<RouterDB::vertex>::iterator it = this->vertices_total.begin(); it != this->vertices_total.end(); ++it) {
    if (it - this->vertices_total.begin() != it->index) {
      logger->debug("Incorrect index: actual {0} stored {1}", it - this->vertices_total.begin(), it->index);
    }
    logger->debug("Incorrect index: actual {0} stored {1}", it - this->vertices_total.begin(), it->index);
    for (std::vector<int>::iterator it2 = it->north.begin(); it2 != it->north.end(); ++it2) {
      if (vertices_total.at(*it2).x != it->x) {
        logger->debug("North direction error: {0} {1} {2}", it->x, it->y, *it2);
      }
    }
    for (std::vector<int>::iterator it2 = it->south.begin(); it2 != it->south.end(); ++it2) {
      if (vertices_total.at(*it2).x != it->x) {
        logger->debug("South direction error: {0} {1} {2}", it->x, it->y, *it2);
      }
    }
    for (std::vector<int>::iterator it2 = it->east.begin(); it2 != it->east.end(); ++it2) {
      if (vertices_total.at(*it2).y != it->y) {
        logger->debug("East direction error: {0} {1} {2}", it->x, it->y, *it2);
      }
    }
    for (std::vector<int>::iterator it2 = it->west.begin(); it2 != it->west.end(); ++it2) {
      if (vertices_total.at(*it2).y != it->y) {
        logger->debug("West direction error: {0} {1} {2}", it->x, it->y, *it2);
      }
    }
    if (it->up != -1) {
      if (vertices_total.at(it->up).x != it->x || vertices_total.at(it->up).y != it->y) {
        logger->debug("Up direction error: {0} {1} {2}", it->x, it->y, it->up);
      }
    }
    if (it->down != -1) {
      if (vertices_total.at(it->down).x != it->x || vertices_total.at(it->down).y != it->y) {
        logger->debug("down direction error: {0} {1} {2}", it->x, it->y, it->down);
      }
    }
  }
};

Grid::Grid(GlobalGrid& GG, std::vector<std::pair<int, int>>& ST, PnRDB::Drc_info& drc_info, RouterDB::point ll, RouterDB::point ur, int Lmetal, int Hmetal,
           int grid_scale)
    : LL(ll), UR(ur) {
  auto logger = spdlog::default_logger()->clone("router.Grid.Grid");

  // 1. Initialize member variables I

  this->GridLL.x = INT_MAX;
  this->GridLL.y = INT_MAX;
  this->GridUR.x = INT_MIN;
  this->GridUR.y = INT_MIN;
  this->lowest_metal = Lmetal;
  this->highest_metal = Hmetal;
  this->grid_scale = grid_scale;
  this->layerNo = drc_info.Metal_info.size();
  this->Start_index_metal_vertices.resize(this->layerNo, 0);
  this->End_index_metal_vertices.resize(this->layerNo, -1);
  this->routeDirect.resize(this->layerNo);
  this->vertices_total.clear();
  this->drc_info = drc_info;
  // 2. Define member variables II
  this->x_unit.resize(this->layerNo, 0);
  this->y_unit.resize(this->layerNo, 0);
  this->x_min.resize(this->layerNo, 0);
  this->y_min.resize(this->layerNo, 0);
  this->vertices_total_map.clear();
  this->vertices_total_map.resize(this->layerNo);  // improve runtime of up/down edges - [wbxu: 20190505]
  // 3. Calculate grid unit and min length for each layer
  for (int i = 0; i < this->layerNo; i++) {
    // this->Start_index_metal_vertices.at(i)=0;
    // this->End_index_metal_vertices.at(i)=-1;
    this->routeDirect.at(i) = drc_info.Metal_info.at(i).direct;
    if (drc_info.Metal_info.at(i).direct == 0) {  // vertical
      this->x_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_x * grid_scale;
      // this->y_min.at(i)=drc_info.Metal_info.at(i).minL;
      this->y_min.at(i) = 1;
    } else if (drc_info.Metal_info.at(i).direct == 1) {  // horizontal
      this->y_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_y * grid_scale;
      // this->x_min.at(i)=drc_info.Metal_info.at(i).minL;
      this->x_min.at(i) = 1;
    } else {
      logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
      continue;
    }
  }
  // 4. Create Hgrid/Vgrid with x/y index in each tile layer
  std::vector<std::vector<std::vector<int>>> Hgrid, Vgrid;
  Hgrid.resize(GG.GetTileLayerNum());
  Vgrid.resize(GG.GetTileLayerNum());
  for (int i = 0; i < GG.GetTileLayerNum(); ++i) {
    std::vector<int> Xarray(GG.GetMaxXidx() + 1, -1);
    std::vector<int> Yarray(GG.GetMaxYidx() + 1, -1);
    Hgrid.at(i).resize(GG.GetMaxYidx() + 1, Xarray);
    Vgrid.at(i).resize(GG.GetMaxXidx() + 1, Yarray);
  }
  for (std::vector<std::pair<int, int>>::iterator it = ST.begin(); it != ST.end(); ++it) {
    int idx = it->first;
    Hgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileYidx(idx)).at(GG.GetTileXidx(idx)) = idx;
    Vgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileXidx(idx)).at(GG.GetTileYidx(idx)) = idx;
    idx = it->second;
    Hgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileYidx(idx)).at(GG.GetTileXidx(idx)) = idx;
    Vgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileXidx(idx)).at(GG.GetTileYidx(idx)) = idx;
  }
  // 5. Convert Hgrid/Vgrid into tracks in each metal layer
  std::vector<std::vector<std::pair<int, int>>> tracks(this->layerNo);
  for (int i = 0; i < GG.GetTileLayerNum(); ++i) {
    std::set<int> midx = GG.GetMappedMetalIndex(i);
    for (std::set<int>::iterator it = midx.begin(); it != midx.end(); ++it) {
      if (drc_info.Metal_info.at(*it).direct == 0) {  // vertical
        for (unsigned int x = 0; x < Vgrid.at(i).size(); ++x) {
          int start = -1;
          for (unsigned int y = 0; y < Vgrid.at(i).at(x).size(); ++y) {
            if (start == -1) {
              if (Vgrid.at(i).at(x).at(y) != -1) {
                start = Vgrid.at(i).at(x).at(y);
              }
            } else {
              if (Vgrid.at(i).at(x).at(y) == -1) {
                tracks.at(*it).emplace_back(std::make_pair(start, Vgrid.at(i).at(x).at(y - 1)));
                start = -1;
              }
            }
          }
          if (start != -1) {
            tracks.at(*it).emplace_back(std::make_pair(start, Vgrid.at(i).at(x).at(Vgrid.at(i).at(x).size() - 1)));
          }
        }
      } else {  // horizontal
        for (unsigned int y = 0; y < Hgrid.at(i).size(); ++y) {
          int start = -1;
          for (unsigned int x = 0; x < Hgrid.at(i).at(y).size(); ++x) {
            if (start == -1) {
              if (Hgrid.at(i).at(y).at(x) != -1) {
                start = Hgrid.at(i).at(y).at(x);
              }
            } else {
              if (Hgrid.at(i).at(y).at(x) == -1) {
                tracks.at(*it).emplace_back(std::make_pair(start, Hgrid.at(i).at(y).at(x - 1)));
                start = -1;
              }
            }
          }
          if (start != -1) {
            tracks.at(*it).emplace_back(std::make_pair(start, Hgrid.at(i).at(y).at(Hgrid.at(i).at(y).size() - 1)));
          }
        }
      }
    }
  }
  // 6. Create grid vertices
  RouterDB::point tmpp;                     // improve runtime of up/down edges - [wbxu: 20190505]
  for (int i = Lmetal; i <= Hmetal; ++i) {  // for each metal layer
    this->Start_index_metal_vertices.at(i) = this->vertices_total.size();
    if (tracks.at(i).empty()) {
      logger->error("Router-Warning: no global tiles on metal layer {0}", i);
      continue;
    }
    for (std::vector<std::pair<int, int>>::iterator it = tracks.at(i).begin(); it != tracks.at(i).end(); ++it) {  // for each independent track (tile pair)
      int x1 = GG.GetTileX(it->first);
      int x2 = GG.GetTileX(it->second);
      int y1 = GG.GetTileY(it->first);
      int y2 = GG.GetTileY(it->second);
      int w1 = GG.GetTileWidth(it->first);
      int w2 = GG.GetTileWidth(it->second);
      int h1 = GG.GetTileHeight(it->first);
      int h2 = GG.GetTileHeight(it->second);
      int track_x = x1 - w1 / 2;
      int track_X = x2 + w2 / 2;
      int track_y = y1 - h1 / 2;
      int track_Y = y2 + h2 / 2;
      if (track_x < ll.x) {
        track_x = ll.x;
      }
      if (track_y < ll.y) {
        track_y = ll.y;
      }
      if (track_X > ur.x) {
        track_X = ur.x;
      }
      if (track_Y > ur.y) {
        track_Y = ur.y;
      }
      if (drc_info.Metal_info.at(i).direct == 0) {  // vertical
        if (x1 != x2) {
          logger->error("Router-Error: vertical tiles not found");
          continue;
        }
        int curlayer_unit = x_unit.at(i);  // current layer direction: vertical
        int nexlayer_unit;                 // neighboring layer direction: horizontal
        int LLx = int(ceil(double(track_x - drc_info.Metal_info[i].offset) / curlayer_unit)) * curlayer_unit + drc_info.Metal_info[i].offset;
        // (LL.x%curlayer_unit==0)?(LL.x):( (LL.x/curlayer_unit)*curlayer_unit<LL.x ? (LL.x/curlayer_unit+1)*curlayer_unit : (LL.x/curlayer_unit)*curlayer_unit
        // ); // X lower boudary
        int LLy;  // Y lower boundary
        set<int> adj_layer_y;
        if (i == 0) {  // if lowest layer
          nexlayer_unit = y_unit.at(i + 1);
          LLy = int(ceil(double(track_y - drc_info.Metal_info[i + 1].offset) / y_unit.at(i + 1))) * y_unit.at(i + 1) + drc_info.Metal_info[i + 1].offset;
          //(LL.y%y_unit.at(i+1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i+1))*y_unit.at(i+1)<LL.y ? (LL.y/y_unit.at(i+1)+1)*y_unit.at(i+1) :
          //(LL.y/y_unit.at(i+1))*y_unit.at(i+1) );
          for (int Y = LLy; Y <= track_Y; Y += nexlayer_unit) {
            adj_layer_y.insert(Y);
          }
        } else if (i == this->layerNo - 1) {  // if highest layer
          nexlayer_unit = y_unit.at(i - 1);
          LLy = int(ceil(double(track_y - drc_info.Metal_info[i - 1].offset) / y_unit.at(i - 1))) * y_unit.at(i - 1) + drc_info.Metal_info[i - 1].offset;
          for (int Y = LLy; Y <= track_Y; Y += nexlayer_unit) {
            adj_layer_y.insert(Y);
          }
          //(LL.y%y_unit.at(i-1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i-1))*y_unit.at(i-1)<LL.y ? (LL.y/y_unit.at(i-1)+1)*y_unit.at(i-1) :
          //(LL.y/y_unit.at(i-1))*y_unit.at(i-1) );
        } else {  // if middle layer
          nexlayer_unit = gcd(y_unit.at(i - 1), y_unit.at(i + 1));
          int LLy_1 = int(ceil(double(track_y - drc_info.Metal_info[i - 1].offset) / y_unit.at(i - 1))) * y_unit.at(i - 1) + drc_info.Metal_info[i - 1].offset;
          //(LL.y%y_unit.at(i-1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i-1))*y_unit.at(i-1)<LL.y ? (LL.y/y_unit.at(i-1)+1)*y_unit.at(i-1) :
          //(LL.y/y_unit.at(i-1))*y_unit.at(i-1) );
          for (int Y = LLy_1; Y <= track_Y; Y += y_unit.at(i - 1)) {
            adj_layer_y.insert(Y);
          }
          int LLy_2 = int(ceil(double(track_y - drc_info.Metal_info[i + 1].offset) / y_unit.at(i + 1))) * y_unit.at(i + 1) + drc_info.Metal_info[i + 1].offset;
          for (int Y = LLy_2; Y <= track_Y; Y += y_unit.at(i + 1)) {
            adj_layer_y.insert(Y);
          }
          //(LL.y%y_unit.at(i+1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i+1))*y_unit.at(i+1)<LL.y ? (LL.y/y_unit.at(i+1)+1)*y_unit.at(i+1) :
          //(LL.y/y_unit.at(i+1))*y_unit.at(i+1) );
          LLy = (LLy_1 < LLy_2) ? LLy_1 : LLy_2;
        }
        for (int X = LLx; X <= track_X; X += curlayer_unit) {
          int nb_start = -1;
          // Power = !Power;
          if (X < this->GridLL.x) {
            this->GridLL.x = X;
          }
          if (X > this->GridUR.x) {
            this->GridUR.x = X;
          }
          for (auto Y : adj_layer_y) {
            RouterDB::vertex tmpv;
            bool pmark = false;
            if (i == 0) {
              tmpv.gridmetal.emplace_back(i + 1);
              pmark = true;
            } else if (i == this->layerNo - 1) {
              tmpv.gridmetal.emplace_back(i - 1);
              pmark = true;
            } else {
              if (Y % y_unit.at(i - 1) == drc_info.Metal_info[i - 1].offset) {
                tmpv.gridmetal.emplace_back(i - 1);
                pmark = true;
              }
              if (Y % y_unit.at(i + 1) == drc_info.Metal_info[i + 1].offset) {
                tmpv.gridmetal.emplace_back(i + 1);
                pmark = true;
              }
            }
            if (!pmark) {
              continue;
            }
            if (Y < this->GridLL.y) {
              this->GridLL.y = Y;
            }
            if (Y > this->GridUR.y) {
              this->GridUR.y = Y;
            }
            tmpp.x = X;
            tmpp.y = Y;  // improve runtime of up/down edges - [wbxu: 20190505]
            tmpv.y = Y;
            tmpv.x = X;
            tmpv.metal = i;
            // if(Power){
            // tmpv.power = 1;
            //}else{
            // tmpv.power = 0;
            //}
            tmpv.active = true;
            tmpv.index = this->vertices_total.size();
            tmpv.up = -1;
            tmpv.down = -1;
            tmpv.north.clear();
            tmpv.south.clear();
            tmpv.east.clear();
            tmpv.west.clear();
            if (nb_start == -1) {
              nb_start = tmpv.index;
            } else {
              bool mark = false;
              int w;
              for (w = tmpv.index - 1; w >= nb_start; w--) {
                if (this->vertices_total.at(w).x == tmpv.x) {
                  if (tmpv.y - this->vertices_total.at(w).y >= y_min.at(i)) {
                    mark = true;
                    break;
                  }
                } else {
                  break;
                }
              }
              if (mark) {
                tmpv.south.emplace_back(w);
                this->vertices_total.at(w).north.emplace_back(tmpv.index);
              }
            }
            this->vertices_total.emplace_back(tmpv);
            this->vertices_total_map.at(i).insert(
                std::pair<RouterDB::point, int>(tmpp, this->vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
          }
        }

      } else if (drc_info.Metal_info.at(i).direct == 1) {  // horizontal
        if (y1 != y2) {
          logger->error("Router-Error: horizontal tiles not found");
          continue;
        }

        int curlayer_unit = y_unit.at(i);  // current layer direction: horizontal
        int nexlayer_unit;                 // neighboring layer direction: vertical
        int LLy = int(ceil(double(track_y - drc_info.Metal_info[i].offset) / curlayer_unit)) * curlayer_unit + drc_info.Metal_info[i].offset;
        //(LL.y%curlayer_unit==0)?(LL.y):( (LL.y/curlayer_unit)*curlayer_unit<LL.y ? (LL.y/curlayer_unit+1)*curlayer_unit : (LL.y/curlayer_unit)*curlayer_unit
        //); // Y lower boudary
        int LLx;  // X lower boundary
        set<int> adj_layer_x;
        if (i == 0) {  // if lowest layer
          nexlayer_unit = x_unit.at(i + 1);
          LLx = int(ceil(double(track_x - drc_info.Metal_info[i + 1].offset) / x_unit.at(i + 1))) * x_unit.at(i + 1) + drc_info.Metal_info[i + 1].offset;
          for (int X = LLx; X <= track_X; X += nexlayer_unit) {
            adj_layer_x.insert(X);
          }
          //(LL.x%x_unit.at(i+1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i+1))*x_unit.at(i+1)<LL.x ? (LL.x/x_unit.at(i+1)+1)*x_unit.at(i+1) :
          //(LL.x/x_unit.at(i+1))*x_unit.at(i+1) );
        } else if (i == this->layerNo - 1) {  // if highest layer
          nexlayer_unit = x_unit.at(i - 1);
          LLx = int(ceil(double(track_x - drc_info.Metal_info[i - 1].offset) / x_unit.at(i - 1))) * x_unit.at(i - 1) + drc_info.Metal_info[i - 1].offset;
          for (int X = LLx; X <= track_X; X += nexlayer_unit) {
            adj_layer_x.insert(X);
          }
          //(LL.x%x_unit.at(i-1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i-1))*x_unit.at(i-1)<LL.x ? (LL.x/x_unit.at(i-1)+1)*x_unit.at(i-1) :
          //(LL.x/x_unit.at(i-1))*x_unit.at(i-1) );
        } else {  // if middle layer
          nexlayer_unit = gcd(x_unit.at(i - 1), x_unit.at(i + 1));
          int LLx_1 = int(ceil(double(track_x - drc_info.Metal_info[i - 1].offset) / x_unit.at(i - 1))) * x_unit.at(i - 1) + drc_info.Metal_info[i - 1].offset;
          for (int X = LLx_1; X <= track_X; X += x_unit.at(i - 1)) {
            adj_layer_x.insert(X);
          }
          //(LL.x%x_unit.at(i-1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i-1))*x_unit.at(i-1)<LL.x ? (LL.x/x_unit.at(i-1)+1)*x_unit.at(i-1) :
          //(LL.x/x_unit.at(i-1))*x_unit.at(i-1) );
          int LLx_2 = int(ceil(double(track_x - drc_info.Metal_info[i + 1].offset) / x_unit.at(i + 1))) * x_unit.at(i + 1) + drc_info.Metal_info[i + 1].offset;
          for (int X = LLx_2; X <= track_X; X += x_unit.at(i + 1)) {
            adj_layer_x.insert(X);
          }
          //(LL.x%x_unit.at(i+1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i+1))*x_unit.at(i+1)<LL.x ? (LL.x/x_unit.at(i+1)+1)*x_unit.at(i+1) :
          //(LL.x/x_unit.at(i+1))*x_unit.at(i+1) );
          LLx = (LLx_1 < LLx_2) ? LLx_1 : LLx_2;
        }
        for (int Y = LLy; Y <= track_Y; Y += curlayer_unit) {
          int nb_start = -1;
          // Power=!Power;
          if (Y < this->GridLL.y) {
            this->GridLL.y = Y;
          }
          if (Y > this->GridUR.y) {
            this->GridUR.y = Y;
          }
          for (auto X : adj_layer_x) {
            RouterDB::vertex tmpv;
            bool pmark = false;
            if (i == 0) {
              tmpv.gridmetal.emplace_back(i + 1);
              pmark = true;
            } else if (i == this->layerNo - 1) {
              tmpv.gridmetal.emplace_back(i - 1);
              pmark = true;
            } else {
              if (X % x_unit.at(i - 1) == drc_info.Metal_info[i - 1].offset) {
                tmpv.gridmetal.emplace_back(i - 1);
                pmark = true;
              }
              if (X % x_unit.at(i + 1) == drc_info.Metal_info[i + 1].offset) {
                tmpv.gridmetal.emplace_back(i + 1);
                pmark = true;
              }
            }
            if (!pmark) {
              continue;
            }
            if (X < this->GridLL.x) {
              this->GridLL.x = X;
            }
            if (X > this->GridUR.x) {
              this->GridUR.x = X;
            }
            tmpp.x = X;
            tmpp.y = Y;  // improve runtime of up/down edges - [wbxu: 20190505]
            tmpv.y = Y;
            tmpv.x = X;
            tmpv.metal = i;
            // if(Power){
            // tmpv.power = 1;
            //}else{
            // tmpv.power = 0;
            //}
            tmpv.active = true;
            tmpv.index = this->vertices_total.size();
            tmpv.up = -1;
            tmpv.down = -1;
            tmpv.north.clear();
            tmpv.south.clear();
            tmpv.east.clear();
            tmpv.west.clear();
            if (nb_start == -1) {
              nb_start = tmpv.index;
            } else {
              bool mark = false;
              int w;
              for (w = tmpv.index - 1; w >= nb_start; w--) {
                if (this->vertices_total.at(w).y == tmpv.y) {
                  if (tmpv.x - this->vertices_total.at(w).x >= x_min.at(i)) {
                    mark = true;
                    break;
                  }
                } else {
                  break;
                }
              }
              if (mark) {
                tmpv.west.emplace_back(w);
                this->vertices_total.at(w).east.emplace_back(tmpv.index);
              }
            }
            this->vertices_total.emplace_back(tmpv);
            this->vertices_total_map.at(i).insert(
                std::pair<RouterDB::point, int>(tmpp, this->vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
          }
        }
      } else {
        logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
        continue;
      }
    }
    this->End_index_metal_vertices.at(i) = this->vertices_total.size() - 1;
  }
  // 7. Add up/down infom for grid points
  std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit;  // improve runtime of up/down edges - [wbxu: 20190505]
  for (int k = this->lowest_metal; k < this->highest_metal; k++) {
    for (int i = this->Start_index_metal_vertices.at(k); i <= this->End_index_metal_vertices.at(k); i++) {
      // improve runtime of up/down edges - [wbxu: 20190505]
      tmpp.x = this->vertices_total[i].x;
      tmpp.y = this->vertices_total[i].y;
      mit = this->vertices_total_map.at(k + 1).find(tmpp);
      if (mit != this->vertices_total_map.at(k + 1).end()) {
        this->vertices_total[i].up = mit->second;
        this->vertices_total[mit->second].down = i;
      }
    }
  }
}

Grid::Grid(GlobalGrid& GG, std::vector<std::pair<int, int>>& ST, PnRDB::Drc_info& drc_info, RouterDB::point ll, RouterDB::point ur, int Lmetal, int Hmetal,
           int grid_scale, bool offset)
    : LL(ll), UR(ur) {
  auto logger = spdlog::default_logger()->clone("router.Grid.Grid");

  // 1. Initialize member variables I

  this->GridLL.x = INT_MAX;
  this->GridLL.y = INT_MAX;
  this->GridUR.x = INT_MIN;
  this->GridUR.y = INT_MIN;
  this->lowest_metal = Lmetal;
  this->highest_metal = Hmetal;
  this->grid_scale = grid_scale;
  this->layerNo = drc_info.Metal_info.size();
  this->Start_index_metal_vertices.resize(this->layerNo, 0);
  this->End_index_metal_vertices.resize(this->layerNo, -1);
  this->routeDirect.resize(this->layerNo);
  this->vertices_total.clear();
  this->drc_info = drc_info;
  // 2. Define member variables II
  this->x_unit.resize(this->layerNo, 0);
  this->y_unit.resize(this->layerNo, 0);
  this->x_min.resize(this->layerNo, 0);
  this->y_min.resize(this->layerNo, 0);
  this->vertices_total_map.clear();
  this->vertices_total_map.resize(this->layerNo);  // improve runtime of up/down edges - [wbxu: 20190505]
  // 3. Calculate grid unit and min length for each layer
  for (int i = 0; i < this->layerNo; i++) {
    // this->Start_index_metal_vertices.at(i)=0;
    // this->End_index_metal_vertices.at(i)=-1;
    this->routeDirect.at(i) = drc_info.Metal_info.at(i).direct;
    if (drc_info.Metal_info.at(i).direct == 0) {  // vertical
      this->x_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_x * grid_scale;
      // this->y_min.at(i)=drc_info.Metal_info.at(i).minL;
      this->y_min.at(i) = 1;
    } else if (drc_info.Metal_info.at(i).direct == 1) {  // horizontal
      this->y_unit.at(i) = drc_info.Metal_info.at(i).grid_unit_y * grid_scale;
      // this->x_min.at(i)=drc_info.Metal_info.at(i).minL;
      this->x_min.at(i) = 1;
    } else {
      logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
      continue;
    }
  }
  // 4. Create Hgrid/Vgrid with x/y index in each tile layer
  std::vector<std::vector<std::vector<int>>> Hgrid, Vgrid;
  Hgrid.resize(GG.GetTileLayerNum());
  Vgrid.resize(GG.GetTileLayerNum());
  for (int i = 0; i < GG.GetTileLayerNum(); ++i) {
    std::vector<int> Xarray(GG.GetMaxXidx() + 1, -1);
    std::vector<int> Yarray(GG.GetMaxYidx() + 1, -1);
    Hgrid.at(i).resize(GG.GetMaxYidx() + 1, Xarray);
    Vgrid.at(i).resize(GG.GetMaxXidx() + 1, Yarray);
  }
  for (std::vector<std::pair<int, int>>::iterator it = ST.begin(); it != ST.end(); ++it) {
    int idx = it->first;
    Hgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileYidx(idx)).at(GG.GetTileXidx(idx)) = idx;
    Vgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileXidx(idx)).at(GG.GetTileYidx(idx)) = idx;
    idx = it->second;
    Hgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileYidx(idx)).at(GG.GetTileXidx(idx)) = idx;
    Vgrid.at(GG.GetTileLayer(idx)).at(GG.GetTileXidx(idx)).at(GG.GetTileYidx(idx)) = idx;
  }
  // 5. Convert Hgrid/Vgrid into tracks in each metal layer
  std::vector<std::vector<std::pair<int, int>>> tracks(this->layerNo);
  for (int i = 0; i < GG.GetTileLayerNum(); ++i) {
    std::set<int> midx = GG.GetMappedMetalIndex(i);
    for (std::set<int>::iterator it = midx.begin(); it != midx.end(); ++it) {
      if (drc_info.Metal_info.at(*it).direct == 0) {  // vertical
        for (unsigned int x = 0; x < Vgrid.at(i).size(); ++x) {
          int start = -1;
          for (unsigned int y = 0; y < Vgrid.at(i).at(x).size(); ++y) {
            if (start == -1) {
              if (Vgrid.at(i).at(x).at(y) != -1) {
                start = Vgrid.at(i).at(x).at(y);
              }
            } else {
              if (Vgrid.at(i).at(x).at(y) == -1) {
                tracks.at(*it).push_back(std::make_pair(start, Vgrid.at(i).at(x).at(y - 1)));
                start = -1;
              }
            }
          }
          if (start != -1) {
            tracks.at(*it).push_back(std::make_pair(start, Vgrid.at(i).at(x).at(Vgrid.at(i).at(x).size() - 1)));
          }
        }
      } else {  // horizontal
        for (unsigned int y = 0; y < Hgrid.at(i).size(); ++y) {
          int start = -1;
          for (unsigned int x = 0; x < Hgrid.at(i).at(y).size(); ++x) {
            if (start == -1) {
              if (Hgrid.at(i).at(y).at(x) != -1) {
                start = Hgrid.at(i).at(y).at(x);
              }
            } else {
              if (Hgrid.at(i).at(y).at(x) == -1) {
                tracks.at(*it).push_back(std::make_pair(start, Hgrid.at(i).at(y).at(x - 1)));
                start = -1;
              }
            }
          }
          if (start != -1) {
            tracks.at(*it).push_back(std::make_pair(start, Hgrid.at(i).at(y).at(Hgrid.at(i).at(y).size() - 1)));
          }
        }
      }
    }
  }
  // 6. Create grid vertices
  RouterDB::point tmpp;                     // improve runtime of up/down edges - [wbxu: 20190505]
  for (int i = Lmetal; i <= Hmetal; ++i) {  // for each metal layer
    this->Start_index_metal_vertices.at(i) = this->vertices_total.size();
    if (tracks.at(i).empty()) {
      logger->error("Router-Warning: no global tiles on metal layer {0}", i);
      continue;
    }
    for (std::vector<std::pair<int, int>>::iterator it = tracks.at(i).begin(); it != tracks.at(i).end(); ++it) {  // for each independent track (tile pair)
      int x1 = GG.GetTileX(it->first);
      int x2 = GG.GetTileX(it->second);
      int y1 = GG.GetTileY(it->first);
      int y2 = GG.GetTileY(it->second);
      int w1 = GG.GetTileWidth(it->first);
      int w2 = GG.GetTileWidth(it->second);
      int h1 = GG.GetTileHeight(it->first);
      int h2 = GG.GetTileHeight(it->second);
      int track_x = x1 - w1 / 2;
      int track_X = x2 + w2 / 2;
      int track_y = y1 - h1 / 2;
      int track_Y = y2 + h2 / 2;
      if (track_x < ll.x) {
        track_x = ll.x;
      }
      if (track_y < ll.y) {
        track_y = ll.y;
      }
      if (track_X > ur.x) {
        track_X = ur.x;
      }
      if (track_Y > ur.y) {
        track_Y = ur.y;
      }
      int track_y1 = track_y;
      int track_Y1 = track_Y;

      // without offset, xl <= a*x <= xu
      // with offset, xl <= a*x + b <= xu, then xl - b <= a*x <= xu -b, finally a*x + b should be grid point
      // that is the reason why the box need to -b, after that all the point + b
      // this method works for a single layer, what about muliple layer? b have bl and bu.
      // track_x = track_x - drc_info.Metal_info.at(i).offset;
      // track_X = track_X - drc_info.Metal_info.at(i).offset;
      // track_y = track_y - drc_info.Metal_info.at(i+1).offset; // something wrong here, i+1 or i-1
      // track_Y = track_Y - drc_info.Metal_info.at(i+1).offset; // something wrong here, i+1 or i-1

      if (drc_info.Metal_info.at(i).direct == 0) {  // vertical
        if (x1 != x2) {
          logger->error("Router-Error: vertical tiles not found");
          continue;
        }
        int curlayer_unit = x_unit.at(i);  // current layer direction: vertical
        int nexlayer_unit;                 // neighboring layer direction: horizontal
        int nexlayer_unit1;
        int LLx = int(ceil(double(track_x - drc_info.Metal_info.at(i).offset) / curlayer_unit)) * curlayer_unit;
        // (LL.x%curlayer_unit==0)?(LL.x):( (LL.x/curlayer_unit)*curlayer_unit<LL.x ? (LL.x/curlayer_unit+1)*curlayer_unit : (LL.x/curlayer_unit)*curlayer_unit
        // ); // X lower boudary
        int LLy;       // Y lower boundary
        int LLy1;      // another Y lower boundary
        int layers;    // -1 lower, 0 both, 1 upper
        if (i == 0) {  // if lowest layer
          nexlayer_unit1 = y_unit.at(i + 1);
          LLy1 = int(ceil(double(track_y - drc_info.Metal_info.at(i + 1).offset) / y_unit.at(i + 1))) * y_unit.at(i + 1);
          layers = 1;
          //(LL.y%y_unit.at(i+1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i+1))*y_unit.at(i+1)<LL.y ? (LL.y/y_unit.at(i+1)+1)*y_unit.at(i+1) :
          //(LL.y/y_unit.at(i+1))*y_unit.at(i+1) );
        } else if (i == this->layerNo - 1) {  // if highest layer
          nexlayer_unit1 = y_unit.at(i - 1);
          LLy = int(ceil(double(track_y - drc_info.Metal_info.at(i - 1).offset) / y_unit.at(i - 1))) * y_unit.at(i - 1);
          //(LL.y%y_unit.at(i-1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i-1))*y_unit.at(i-1)<LL.y ? (LL.y/y_unit.at(i-1)+1)*y_unit.at(i-1) :
          //(LL.y/y_unit.at(i-1))*y_unit.at(i-1) );
          layers = -1;
        } else {  // if middle layer
          // nexlayer_unit = gcd(y_unit.at(i - 1), y_unit.at(i + 1));
          nexlayer_unit = y_unit.at(i - 1);
          nexlayer_unit1 = y_unit.at(i + 1);
          int LLy_1 = int(ceil(double(track_y - drc_info.Metal_info.at(i - 1).offset) / y_unit.at(i - 1))) * y_unit.at(i - 1);
          //(LL.y%y_unit.at(i-1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i-1))*y_unit.at(i-1)<LL.y ? (LL.y/y_unit.at(i-1)+1)*y_unit.at(i-1) :
          //(LL.y/y_unit.at(i-1))*y_unit.at(i-1) );
          int LLy_2 = int(ceil(double(track_y - drc_info.Metal_info.at(i + 1).offset) / y_unit.at(i + 1))) * y_unit.at(i + 1);
          //(LL.y%y_unit.at(i+1)==0) ? (LL.y) : ( (LL.y/y_unit.at(i+1))*y_unit.at(i+1)<LL.y ? (LL.y/y_unit.at(i+1)+1)*y_unit.at(i+1) :
          //(LL.y/y_unit.at(i+1))*y_unit.at(i+1) );
          LLy = LLy_1;   // lower layer
          LLy1 = LLy_2;  // higher layer
          // LLy = (LLy_1 < LLy_2) ? LLy_1 : LLy_2;
          layers = 0;  // both
        }
        for (int X = LLx; X <= track_X - drc_info.Metal_info.at(i).offset; X += curlayer_unit) {
          int nb_start = -1;
          // Power = !Power;
          set<int> temp_y;
          if (layers == -1) {  // this is for lower layer

            for (int Y = LLy; Y < track_Y - drc_info.Metal_info.at(i - 1).offset; Y += nexlayer_unit) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_y.insert(Y + drc_info.Metal_info.at(i - 1).offset);
            }

          } else if (layers == 1) {  // this is for lower layer

            for (int Y = LLy1; Y < track_Y - drc_info.Metal_info.at(i + 1).offset; Y += nexlayer_unit1) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_y.insert(Y + drc_info.Metal_info.at(i + 1).offset);
            }

          } else if (layers == 0) {  // this is for both layer

            for (int Y = LLy; Y < track_Y - drc_info.Metal_info.at(i - 1).offset; Y += nexlayer_unit) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_y.insert(Y + drc_info.Metal_info.at(i - 1).offset);
            }

            for (int Y = LLy1; Y < track_Y - drc_info.Metal_info.at(i + 1).offset; Y += nexlayer_unit1) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_y.insert(Y + drc_info.Metal_info.at(i + 1).offset);
            }

          } else {
            std::cout << "Bug for setting up metal layers" << std::endl;
          }

          // then insert grid
          for (auto it : temp_y) {
            RouterDB::vertex tmpv;
            tmpv.y = it;
            tmpv.x = X;
            tmpv.metal = i;
            tmpv.active = true;
            tmpv.index = this->vertices_total.size();
            tmpv.up = -1;
            tmpv.down = -1;
            tmpv.north.clear();
            tmpv.south.clear();
            tmpv.east.clear();
            tmpv.west.clear();
            if (nb_start == -1) {
              nb_start = tmpv.index;
            } else {
              bool mark = false;
              int w;
              for (w = tmpv.index - 1; w >= nb_start; w--) {
                if (this->vertices_total.at(w).x == tmpv.x) {
                  if (tmpv.y - this->vertices_total.at(w).y >= y_min.at(i)) {
                    mark = true;
                    break;
                  }
                } else {
                  break;
                }
              }
              if (mark) {
                tmpv.south.push_back(w);
                this->vertices_total.at(w).north.push_back(tmpv.index);
              }
            }
            this->vertices_total.push_back(tmpv);
            this->vertices_total_map.at(i).insert(
                std::pair<RouterDB::point, int>(tmpp, this->vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
          }
        }
      } else if (drc_info.Metal_info.at(i).direct == 1) {  // horizontal
        if (y1 != y2) {
          logger->error("Router-Error: horizontal tiles not found");
          continue;
        }

        int curlayer_unit = y_unit.at(i);  // current layer direction: horizontal
        int nexlayer_unit;                 // neighboring layer direction: vertical
        int nexlayer_unit1;
        int layers;
        int LLy = int(ceil(double(track_y - drc_info.Metal_info.at(i).offset) / curlayer_unit)) * curlayer_unit;
        //(LL.y%curlayer_unit==0)?(LL.y):( (LL.y/curlayer_unit)*curlayer_unit<LL.y ? (LL.y/curlayer_unit+1)*curlayer_unit : (LL.y/curlayer_unit)*curlayer_unit
        //); // Y lower boudary
        int LLx;       // X lower boundary
        int LLx1;      // another Y lower boundary
        if (i == 0) {  // if lowest layer
          nexlayer_unit1 = x_unit.at(i + 1);
          LLx1 = int(ceil(double(track_x - drc_info.Metal_info.at(i + 1).offset) / x_unit.at(i + 1))) * x_unit.at(i + 1);
          layers = 1;
          //(LL.x%x_unit.at(i+1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i+1))*x_unit.at(i+1)<LL.x ? (LL.x/x_unit.at(i+1)+1)*x_unit.at(i+1) :
          //(LL.x/x_unit.at(i+1))*x_unit.at(i+1) );
        } else if (i == this->layerNo - 1) {  // if highest layer
          nexlayer_unit = x_unit.at(i - 1);
          LLx = int(ceil(double(track_x - drc_info.Metal_info.at(i - 1).offset) / x_unit.at(i - 1))) * x_unit.at(i - 1);
          //(LL.x%x_unit.at(i-1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i-1))*x_unit.at(i-1)<LL.x ? (LL.x/x_unit.at(i-1)+1)*x_unit.at(i-1) :
          //(LL.x/x_unit.at(i-1))*x_unit.at(i-1) );
          layers = -1;
        } else {  // if middle layer
          // nexlayer_unit = gcd(x_unit.at(i - 1), x_unit.at(i + 1));
          nexlayer_unit = x_unit.at(i - 1);
          nexlayer_unit1 = x_unit.at(i + 1);
          int LLx_1 = int(ceil(double(track_x - drc_info.Metal_info.at(i - 1).offset) / x_unit.at(i - 1))) * x_unit.at(i - 1);
          //(LL.x%x_unit.at(i-1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i-1))*x_unit.at(i-1)<LL.x ? (LL.x/x_unit.at(i-1)+1)*x_unit.at(i-1) :
          //(LL.x/x_unit.at(i-1))*x_unit.at(i-1) );
          int LLx_2 = int(ceil(double(track_x - drc_info.Metal_info.at(i + 1).offset) / x_unit.at(i + 1))) * x_unit.at(i + 1);
          //(LL.x%x_unit.at(i+1)==0) ? (LL.x) : ( (LL.x/x_unit.at(i+1))*x_unit.at(i+1)<LL.x ? (LL.x/x_unit.at(i+1)+1)*x_unit.at(i+1) :
          //(LL.x/x_unit.at(i+1))*x_unit.at(i+1) );
          LLx = LLx_1;
          LLx1 = LLx_2;
          layers = 0;
          // LLx = (LLx_1 < LLx_2) ? LLx_1 : LLx_2;
        }

        for (int Y = LLy; Y <= track_Y - drc_info.Metal_info.at(i).offset; Y += curlayer_unit) {
          int nb_start = -1;
          // Power=!Power;
          set<int> temp_x;

          if (layers == -1) {  // this is for lower layer

            for (int X = LLx; X <= track_X - drc_info.Metal_info.at(i - 1).offset; X += nexlayer_unit) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_x.insert(X + drc_info.Metal_info.at(i - 1).offset);
            }

          } else if (layers == 1) {  // this is for lower layer

            for (int X = LLx1; X <= track_X - drc_info.Metal_info.at(i + 1).offset; X += nexlayer_unit1) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_x.insert(X + drc_info.Metal_info.at(i + 1).offset);
            }

          } else if (layers == 0) {  // this is for both layer

            for (int X = LLx; X <= track_X - drc_info.Metal_info.at(i - 1).offset; X += nexlayer_unit) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_x.insert(X + drc_info.Metal_info.at(i - 1).offset);
            }

            for (int X = LLx1; X <= track_X - drc_info.Metal_info.at(i + 1).offset; X += nexlayer_unit1) {
              if (X < this->GridLL.x) {
                this->GridLL.x = X;
              }
              if (Y < this->GridLL.y) {
                this->GridLL.y = Y;
              }
              if (X > this->GridUR.x) {
                this->GridUR.x = X;
              }
              if (Y > this->GridUR.y) {
                this->GridUR.y = Y;
              }
              temp_x.insert(X + drc_info.Metal_info.at(i + 1).offset);
            }

          } else {
            std::cout << "Bug for setting up metal layers" << std::endl;
          }

          // then insert grid
          for (auto it : temp_x) {
            RouterDB::vertex tmpv;
            tmpv.y = Y;
            tmpv.x = it;
            tmpv.metal = i;
            tmpv.active = true;
            tmpv.index = this->vertices_total.size();
            tmpv.up = -1;
            tmpv.down = -1;
            tmpv.north.clear();
            tmpv.south.clear();
            tmpv.east.clear();
            tmpv.west.clear();
            if (nb_start == -1) {
              nb_start = tmpv.index;
            } else {
              bool mark = false;
              int w;
              for (w = tmpv.index - 1; w >= nb_start; w--) {
                if (this->vertices_total.at(w).y == tmpv.y) {
                  if (tmpv.x - this->vertices_total.at(w).x >= x_min.at(i)) {
                    mark = true;
                    break;
                  }
                } else {
                  break;
                }
              }
              if (mark) {
                tmpv.west.push_back(w);
                this->vertices_total.at(w).east.push_back(tmpv.index);
              }
            }
            this->vertices_total.push_back(tmpv);
            this->vertices_total_map.at(i).insert(
                std::pair<RouterDB::point, int>(tmpp, this->vertices_total.size() - 1));  // improve runtime of up/down edges - [wbxu: 20190505]
          }
        }
      } else {
        logger->error("Router-Error: incorrect routing direction on metal layer {0}", i);
        continue;
      }
    }
    this->End_index_metal_vertices.at(i) = this->vertices_total.size() - 1;
  }
  // 7. Add up/down infom for grid points
  std::map<RouterDB::point, int, RouterDB::pointXYComp>::iterator mit;  // improve runtime of up/down edges - [wbxu: 20190505]
  for (int k = this->lowest_metal; k < this->highest_metal; k++) {
    for (int i = this->Start_index_metal_vertices.at(k); i <= this->End_index_metal_vertices.at(k); i++) {
      // improve runtime of up/down edges - [wbxu: 20190505]
      tmpp.x = this->vertices_total[i].x;
      tmpp.y = this->vertices_total[i].y;
      mit = this->vertices_total_map.at(k + 1).find(tmpp);
      if (mit != this->vertices_total_map.at(k + 1).end()) {
        this->vertices_total[i].up = mit->second;
        this->vertices_total[mit->second].down = i;
      }
    }
  }
}

int Grid::Find_EndIndex(int start_index, int direction) {
  int end_index = -1;

  for (int i = start_index; i < (int)vertices_total.size(); i++) {
    if (direction == 0) {  // vertical

      if (vertices_total[i].x == vertices_total[start_index].x && vertices_total[i].metal == vertices_total[start_index].metal) {
        end_index = i;

      } else {
        break;
      }

    } else {
      if (vertices_total[i].y == vertices_total[start_index].y && vertices_total[i].metal == vertices_total[start_index].metal) {
        end_index = i;

      } else {
        break;
      }
    }
  }

  return end_index;
}

bool Grid::Check_Common_Part(int& start_index1, int& end_index1, int& start_index2, int& end_index2, int direction, int pitches_dis) {
  // same layer?

  if (vertices_total[start_index1].metal != vertices_total[start_index2].metal) {
    // std::cout<<"return point 1"<<std::endl;
    return 0;
  }

  // nearby?
  if (direction == 0) {  // vertical
    if (abs(vertices_total[start_index2].x - vertices_total[start_index1].x) != pitches_dis) {
      // std::cout<<"return point 2"<<std::endl;
      return 0;
    }
  } else {
    if (abs(vertices_total[start_index2].y - vertices_total[start_index1].y) != pitches_dis) {
      // std::cout<<"return point 3"<<std::endl;
      return 0;
    }
  }

  // find the common part
  int min_number = -1;
  int max_number = -1;

  if (direction == 0) {  // verical

    if (vertices_total[start_index1].y >= vertices_total[start_index2].y) {
      min_number = vertices_total[start_index1].y;
    } else {
      min_number = vertices_total[start_index2].y;
    }

    if (vertices_total[end_index1].y <= vertices_total[end_index2].y) {
      max_number = vertices_total[end_index1].y;
    } else {
      max_number = vertices_total[end_index2].y;
    }

  } else {
    if (vertices_total[start_index1].x >= vertices_total[start_index2].x) {
      min_number = vertices_total[start_index1].x;
    } else {
      min_number = vertices_total[start_index2].x;
    }

    if (vertices_total[end_index1].x <= vertices_total[end_index2].x) {
      max_number = vertices_total[end_index1].x;
    } else {
      max_number = vertices_total[end_index2].x;
    }
  }

  if (min_number > max_number) {
    // std::cout<<"return point 4"<<std::endl;
    return 0;
  }

  int new_start_index1 = -1;
  int new_end_index1 = -1;
  int new_start_index2 = -1;
  int new_end_index2 = -1;

  if (direction == 0) {  // vertical

    for (int i = start_index1; i <= end_index1; i++) {
      if (vertices_total[i].y == min_number) {
        new_start_index1 = i;
      }
      if (vertices_total[i].y == max_number) {
        new_end_index1 = i;
      }
    }

    for (int i = start_index2; i <= end_index2; i++) {
      if (vertices_total[i].y == min_number) {
        new_start_index2 = i;
      }
      if (vertices_total[i].y == max_number) {
        new_end_index2 = i;
      }
    }

  } else {  // heriontal

    for (int i = start_index1; i <= end_index1; i++) {
      if (vertices_total[i].x == min_number) {
        new_start_index1 = i;
      }
      if (vertices_total[i].x == max_number) {
        new_end_index1 = i;
      }
    }

    for (int i = start_index2; i <= end_index2; i++) {
      if (vertices_total[i].x == min_number) {
        new_start_index2 = i;
      }
      if (vertices_total[i].x == max_number) {
        new_end_index2 = i;
      }
    }
  }

  if (new_start_index1 == -1 || new_end_index1 == -1 || new_start_index2 == -1 || new_end_index2 == -1) {
    // std::cout<<"return point 5"<<std::endl;
    return 0;

  } else {
    start_index1 = new_start_index1;
    end_index1 = new_end_index1;
    start_index2 = new_start_index2;
    end_index2 = new_end_index2;
    // std::cout<<"return point 6"<<std::endl;
    return 1;
  }
}

void Grid::Full_Connected_Vertex() {
  vertices_total_full_connected = vertices_total;
  int start_index = 0;
  // int end_index=0;

  while (start_index < (int)vertices_total.size()) {
    // std::cout<<"Full connection vertex check point 1"<<std::endl;
    int end_index = Find_EndIndex(start_index, drc_info.Metal_info[vertices_total[start_index].metal].direct);
    int next_start_index = end_index + 1;
    int current_start_index = next_start_index;
    // std::cout<<"Full connection vertex check point 2"<<std::endl;
    if (next_start_index >= (int)vertices_total.size()) {
      start_index = next_start_index;
      continue;
    }
    int next_end_index = Find_EndIndex(next_start_index, drc_info.Metal_info[vertices_total[next_start_index].metal].direct);
    int current_end_index = next_end_index;
    // std::cout<<"Full connection vertex check point 2.5"<<std::endl;
    if (next_end_index == -1 || next_start_index >= (int)vertices_total.size()) {
      start_index = next_start_index;
      continue;
    }
    // std::cout<<"start and end index"<<start_index<<" "<<end_index<<" next start and end index "<<next_start_index<<" "<<next_end_index<<std::endl;

    bool common_part_exist;
    if (drc_info.Metal_info[vertices_total[start_index].metal].direct == 0) {  // vertical
      // std::cout<<"Full connection vertex check point 3"<<std::endl;
      common_part_exist =
          Check_Common_Part(start_index, end_index, current_start_index, current_end_index, drc_info.Metal_info[vertices_total[start_index].metal].direct,
                            drc_info.Metal_info[vertices_total[start_index].metal].grid_unit_x);
      // std::cout<<"start and end index"<<start_index<<" "<<end_index<<" next start and end index "<<next_start_index<<" "<<next_end_index<<"
      // "<<common_part_exist<<std::endl; std::cout<<"Full connection vertex check point 4"<<std::endl;
    } else {
      // std::cout<<"Full connection vertex check point 5"<<std::endl;
      common_part_exist =
          Check_Common_Part(start_index, end_index, current_start_index, current_end_index, drc_info.Metal_info[vertices_total[start_index].metal].direct,
                            drc_info.Metal_info[vertices_total[start_index].metal].grid_unit_y);
      // std::cout<<"start and end index"<<start_index<<" "<<end_index<<" next start and end index "<<next_start_index<<" "<<next_end_index<<"
      // "<<common_part_exist<<std::endl; std::cout<<"Full connection vertex check point 6"<<std::endl;
    }

    if (common_part_exist) {
      if (drc_info.Metal_info[vertices_total[start_index].metal].direct == 0) {  // vertical

        int east_index = current_start_index;

        for (int i = start_index; i <= end_index; i++) {
          // std::cout<<"Full connection vertex check point 7"<<std::endl;
          vertices_total_full_connected[i].east.push_back(east_index);
          vertices_total_full_connected[east_index].west.push_back(i);
          // std::cout<<"Full connection vertex check point 8"<<std::endl;
          // std::cout<<"Full connection East/West Node is add"<<std::endl;
          // std::cout<<"Node corrodinate and metal ( "<<vertices_total[i].x<<" "<<vertices_total[i].y<<" "<<vertices_total[i].metal<<" )
          // ("<<vertices_total[east_index].x<<" "<<vertices_total[east_index].y<<" "<<vertices_total[east_index].metal<<" ) "<<std::endl;
          east_index++;
        }

      } else {  // horitcal

        int north_index = current_start_index;

        for (int i = start_index; i <= end_index; i++) {
          // std::cout<<"Full connection vertex check point 9"<<std::endl;
          vertices_total_full_connected[i].north.push_back(north_index);
          vertices_total_full_connected[north_index].south.push_back(i);
          // std::cout<<"Full connection vertex check point 10"<<std::endl;
          // std::cout<<"Full connection North/South Node is add"<<std::endl;
          // std::cout<<"Node corrodinate and metal ( "<<vertices_total[i].x<<" "<<vertices_total[i].y<<" "<<vertices_total[i].metal<<" )
          // ("<<vertices_total[north_index].x<<" "<<vertices_total[north_index].y<<" "<<vertices_total[north_index].metal<<" ) "<<std::endl;
          north_index++;
        }
      }
    }
    start_index = next_start_index;
  }
}

void Grid::SetViaInactiveBox(std::vector<std::vector<int>> path, std::vector<std::pair<int, RouterDB::box>>& via_vec) {
  via_vec.clear();
  for (std::vector<std::vector<int>>::const_iterator paths_it = path.begin(); paths_it != path.end(); paths_it++) {
    for (std::vector<int>::const_iterator path_it = paths_it->begin(); path_it != paths_it->end(); path_it++) {
      if (path_it == paths_it->begin()) continue;  // start from the second vertice
      int mIdx1 = vertices_total[*(path_it - 1)].metal, mIdx2 = vertices_total[*path_it].metal;
      if (mIdx1 == mIdx2) continue;  // skip vertices in the same layer
      int x1 = vertices_total[*(path_it - 1)].x, y1 = vertices_total[*(path_it - 1)].y;
      int x2 = vertices_total[*path_it].x, y2 = vertices_total[*path_it].y;
      if (x1 != x2 || y1 != y2) continue;  // skip when vertices in different location
      int vIdx = std::min(mIdx1, mIdx2);
      RouterDB::point LL{x1 - drc_info.Via_info[vIdx].dist_ss, y1 - drc_info.Via_info[vIdx].dist_ss_y};
      RouterDB::point UR{x1 + drc_info.Via_info[vIdx].dist_ss, y1 + drc_info.Via_info[vIdx].dist_ss_y};
      RouterDB::box box{LL, UR};
      via_vec.push_back(std::make_pair(vIdx, box));
    }
  }
}
