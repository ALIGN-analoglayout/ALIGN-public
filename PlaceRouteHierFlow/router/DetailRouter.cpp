#include "DetailRouter.h"

#include "spdlog/spdlog.h"

DetailRouter::DetailRouter(){

};

DetailRouter::DetailRouter(PnRDB::hierNode& HierNode, GlobalRouter& GR, int path_number, int grid_scale) {
  // std::cout<<"start detail router\n";
  this->Nets = GR.Nets;
  this->Blocks = GR.Blocks;
  this->Terminals = GR.Terminals;
  this->drc_info = GR.drc_info;
  this->lowest_metal = GR.lowest_metal;
  this->highest_metal = GR.highest_metal;
  this->width = GR.width;
  this->height = GR.height;
  this->LL.x = 0;
  this->LL.y = 0;
  this->UR.x = GR.width;
  this->UR.y = GR.height;
  this->LL = GR.LL;
  this->UR = GR.UR;
  this->path_number = path_number;
  this->grid_scale = grid_scale;
  this->layerNo = GR.drc_info.Metal_info.size();
  this->isTop = GR.isTop;
  this->global_grid_scale = GR.grid_scale;

  /*
    Connection();

    std::cout<<"***********start check overlap**********"<<std::endl;
    RecoverOverlap();
    std::cout<<"***********end check overlap*************"<<std::endl;

    //std::cout<<"********start last connection*************"<<std::endl;
    //AddMetalToPin();
    //std::cout<<"********end last connection*************"<<std::endl;
  */

  create_detailrouter();

  // std::cout<<"***************physical metal and via"<<std::endl;
  Physical_metal_via();  // this needs modify

  // std::cout<<"***********start return node in detail router********"<<std::endl;
  ReturnHierNode(HierNode);
  // std::cout<<"************end return node in detail router**********"<<std::endl;
};

void DetailRouter::create_detailrouter() {
  // initial a set for internal metal
  std::vector<std::vector<RouterDB::point> > plist;
  plist.resize(this->layerNo);
  CreatePlistBlocks(plist, this->Blocks);
  CreatePlistTerminals(plist, this->Terminals);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_x;
  InsertPlistToSet_x(Set_x, plist);
  std::set<RouterDB::SinkData, RouterDB::SinkDataComp> Set_net;
  // end initial set
  // start detail router
  for (unsigned int i = 0; i < Nets.size(); i++) {
    // judge whether a net should be routed or not
    if (Nets[i].seg.size() == 0) {
      continue;
    }
    if (Nets[i].seg[0].chosenCand == -1) {
      continue;
    }  // this maybe revised [wbxu: need revision if only other seg has no candidate?]

    // collect pins & collect metal path
    // std::cout<<"starting check find pin"<<std::endl;
    std::vector<std::vector<RouterDB::SinkData> > temp_pins = findPins(Nets[i]);
    // std::cout<<"end check find pin"<<std::endl;

    // std::cout<<"starting check find path"<<std::endl;
    std::vector<RouterDB::Metal> temp_path = findGlobalPath(Nets[i]);
    // std::cout<<"end check find path"<<std::endl;
    // create grid
    // Grid grid(drc_info, grid_scale, lowest_metal, highest_metal, LL, UR, temp_pins, temp_path);
    Grid grid(temp_pins, temp_path, drc_info, LL, UR, lowest_metal, highest_metal, 1, this->global_grid_scale + 1);
    RouterDB::point gridll = grid.GetGridLL();
    RouterDB::point gridur = grid.GetGridUR();
    std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > plist = FindsetPlist(Set_x, gridll, gridur);
    grid.InactivePointlist(plist);
    // void InactivePointlist(std::vector< std::set<RouterDB::point, RouterDB::pointXYComp> > &plist);

    // initial source
    std::vector<RouterDB::SinkData> temp_source;
    std::vector<std::vector<RouterDB::point> > add_plist;
    add_plist.resize(this->layerNo);
    // temp_source = temp_pins[0];

    for (unsigned int j = 0; j < temp_pins[0].size(); j++) {
      temp_source.push_back(temp_pins[0][j]);
    }

    int source_lock = 0;
    for (unsigned int j = 1; j < temp_pins.size(); j++) {
      // create dest
      // std::cout<<"Working on dest "<<j<<std::endl;
      std::vector<RouterDB::SinkData> temp_dest = temp_pins[j];

      std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp> Smap;
      // std::vector<RouterDB::contact> Terminal_contact=grid.setSrcDest( temp_source, temp_dest, this->width, this->height, Smap);
      grid.setSrcDest(temp_source, temp_dest, this->width, this->height, Smap);

      grid.ActivateSourceDest();

      std::vector<std::set<RouterDB::point, RouterDB::pointXYComp> > netplist = FindsetPlist(Set_net, gridll, gridur);
      grid.InactivePointlist(netplist);

      // std::map<RouterDB::point, std::vector<int>, RouterDB::pointXYComp > Smap;
      // Terminal_contact=grid.setSrcDest_detail( temp_source, temp_dest, this->width, this->height, Smap);
      grid.setSrcDest_detail(temp_source, temp_dest, this->width, this->height, Smap);

      // what about this problem?????
      grid.PrepareGraphVertices(gridll.x, gridll.y, gridur.x, gridur.y);  // QQQQQto be fixed
      // what about this problem?????
      // Graph graph(grid, this->path_number);
      Graph graph(grid);
      bool pathMark = graph.FindFeasiblePath(grid, this->path_number);
      std::vector<std::vector<RouterDB::Metal> > physical_path;
      if (pathMark) {
        physical_path = graph.ConvertPathintoPhysical(grid);

        // lastmile connection source
        // check first point of physical path
        lastmile_source_new(physical_path, temp_source);
        // lastmile connection dest
        // check last point of physical path
        lastmile_dest_new(physical_path, temp_dest);

        // return physical path to net
        // splitPath(physical_path, Nets[i]);
        returnPath(physical_path, Nets[i]);
      } else {
        // std::cout<<"Router-Warning: feasible path might not be found\n";
        // std::cout<<Nets[i].netName<<std::endl;
      }

      // update physical path to
      UpdatePlistNets(physical_path, add_plist);

      if (source_lock == 1) {
        temp_source.clear();
        source_lock = 1;
      }

      // add
      updateSource(physical_path, temp_source);  // wbxu: temp_dest might need be appended into temp_source

      grid.InactivateSourceDest();

      for (unsigned int p = 0; p < temp_dest.size(); p++) {
        temp_source.push_back(temp_dest[p]);
      }
    }

    InsertPlistToSet_x(Set_net, add_plist);
  }
};

std::vector<std::vector<RouterDB::SinkData> > DetailRouter::findPins(RouterDB::Net temp_net) {
  std::vector<std::vector<RouterDB::SinkData> > temp_Pin;

  /*
     std::cout<<"Seg info of Net"<<std::endl;
     std::cout<<"Seg number"<<temp_net.seg.size()<<std::endl;
     for(int i=0;i<temp_net.seg.size();i++){
         std::cout<<"sourcelist"<<std::endl;
         for(int j=0;j<temp_net.seg[i].sourceList.size();j++){
             if(temp_net.seg[i].sourceList[j].metalIdx!=-1){std::cout<<"{ ("<<temp_net.seg[i].sourceList[j].coord[0].x<<"
     "<<temp_net.seg[i].sourceList[j].coord[0].y<<" ),("<<temp_net.seg[i].sourceList[j].coord[1].x<<" "<<temp_net.seg[i].sourceList[j].coord[1].y<<")
     }"<<std::endl;}
            }

         std::cout<<"destlist"<<std::endl;
         for(int j=0;j<temp_net.seg[i].destList.size();j++){
             if(temp_net.seg[i].destList[j].metalIdx!=-1){std::cout<<"{ ("<<temp_net.seg[i].destList[j].coord[0].x<<"
     "<<temp_net.seg[i].destList[j].coord[0].y<<" ),("<<temp_net.seg[i].destList[j].coord[1].x<<" "<<temp_net.seg[i].destList[j].coord[1].y<<") }"<<std::endl;}
            }

        }
  */
  for (unsigned int i = 0; i < temp_net.seg.size(); i++) {
    std::vector<RouterDB::SinkData> temp_pin_s;
    for (unsigned int j = 0; j < temp_net.seg[i].sourceList.size(); j++) {
      if (temp_net.seg[i].sourceList[j].metalIdx != -1) {
        temp_pin_s.push_back(temp_net.seg[i].sourceList[j]);
      }
    }

    std::vector<RouterDB::SinkData> temp_pin_d;
    for (unsigned int j = 0; j < temp_net.seg[i].destList.size(); j++) {
      if (temp_net.seg[i].destList[j].metalIdx != -1) {
        temp_pin_d.push_back(temp_net.seg[i].destList[j]);
      }
    }

    std::vector<RouterDB::SinkData> temp_pin_ss;
    for (unsigned int j = 0; j < temp_pin_s.size(); j++) {
      int found = 0;
      for (unsigned int k = 0; k < temp_Pin.size(); k++) {
        for (unsigned int l = 0; l < temp_Pin[k].size(); l++) {
          if (temp_pin_s[j].coord[0].x == temp_Pin[k][l].coord[0].x && temp_pin_s[j].coord[0].y == temp_Pin[k][l].coord[0].y &&
              temp_pin_s[j].coord[1].x == temp_Pin[k][l].coord[1].x && temp_pin_s[j].coord[1].y == temp_Pin[k][l].coord[1].y &&
              temp_pin_s[j].metalIdx == temp_Pin[k][l].metalIdx) {
            found = 1;
          }
        }
      }
      if (found == 0) {
        temp_pin_ss.push_back(temp_pin_s[j]);
      }
    }

    if (temp_pin_ss.size() > 0) {
      temp_Pin.push_back(temp_pin_ss);
    }

    std::vector<RouterDB::SinkData> temp_pin_dd;
    for (unsigned int j = 0; j < temp_pin_d.size(); j++) {
      int found = 0;
      for (unsigned int k = 0; k < temp_Pin.size(); k++) {
        for (unsigned int l = 0; l < temp_Pin[k].size(); l++) {
          if (temp_pin_d[j].coord[0].x == temp_Pin[k][l].coord[0].x && temp_pin_d[j].coord[0].y == temp_Pin[k][l].coord[0].y &&
              temp_pin_d[j].coord[1].x == temp_Pin[k][l].coord[1].x && temp_pin_d[j].coord[1].y == temp_Pin[k][l].coord[1].y &&
              temp_pin_d[j].metalIdx == temp_Pin[k][l].metalIdx) {
            found = 1;
          }
        }
      }
      if (found == 0) {
        temp_pin_dd.push_back(temp_pin_d[j]);
      }
    }

    if (temp_pin_dd.size() > 0) {
      temp_Pin.push_back(temp_pin_dd);
    }
  }

  // sort all the dis
  std::vector<RouterDB::SinkData> temp_label_point;
  std::vector<int> dis;
  temp_label_point = temp_Pin[0];
  for (unsigned int i = 0; i < temp_Pin.size(); i++) {
    int temp_dis = INT_MAX;
    for (unsigned int j = 0; j < temp_Pin[i].size(); j++) {
      for (unsigned int k = 0; k < temp_label_point.size(); k++) {
        if (abs(temp_Pin[i][j].coord[0].x - temp_label_point[k].coord[0].x) + abs(temp_Pin[i][j].coord[0].y - temp_label_point[k].coord[0].y) < temp_dis) {
          temp_dis = abs(temp_Pin[i][j].coord[0].x - temp_label_point[k].coord[0].x) + abs(temp_Pin[i][j].coord[0].y - temp_label_point[k].coord[0].y);
        }
        if (abs(temp_Pin[i][j].coord[0].x - temp_label_point[k].coord[1].x) + abs(temp_Pin[i][j].coord[0].y - temp_label_point[k].coord[1].y) < temp_dis) {
          temp_dis = abs(temp_Pin[i][j].coord[0].x - temp_label_point[k].coord[1].x) + abs(temp_Pin[i][j].coord[0].y - temp_label_point[k].coord[1].y);
        }
        if (abs(temp_Pin[i][j].coord[1].x - temp_label_point[k].coord[1].x) + abs(temp_Pin[i][j].coord[1].y - temp_label_point[k].coord[1].y) < temp_dis) {
          temp_dis = abs(temp_Pin[i][j].coord[1].x - temp_label_point[k].coord[1].x) + abs(temp_Pin[i][j].coord[1].y - temp_label_point[k].coord[1].y);
        }
        if (abs(temp_Pin[i][j].coord[1].x - temp_label_point[k].coord[0].x) + abs(temp_Pin[i][j].coord[1].y - temp_label_point[k].coord[0].y) < temp_dis) {
          temp_dis = abs(temp_Pin[i][j].coord[1].x - temp_label_point[k].coord[0].x) + abs(temp_Pin[i][j].coord[1].y - temp_label_point[k].coord[0].y);
        }
      }
    }
    dis.push_back(temp_dis);
  }

  vector<int> index;
  for (unsigned int i = 0; i < dis.size(); i++) {
    index.push_back(i);
  }

  int temp_dist;
  int temp_index;

  for (unsigned int i = 0; i < dis.size(); i++) {
    for (unsigned int j = i + 1; j < dis.size(); j++) {
      if (dis[i] > dis[j]) {
        temp_dist = dis[i];
        dis[i] = dis[j];
        dis[j] = temp_dist;
        temp_index = index[i];
        index[i] = index[j];
        index[j] = temp_index;
      }
    }
  }

  std::vector<std::vector<RouterDB::SinkData> > Pin;
  for (unsigned int i = 0; i < dis.size(); i++) {
    Pin.push_back(temp_Pin[index[i]]);
  }
  /*
    for(int i=0;i<temp_Pin.size();i++){
         for(int j=0;j<temp_Pin[i].size();j++){
              for(int k=0;k<temp_Pin.size();k++){
                   for(int l=0;l<temp_Pin[k].size();l++){
                         if(i==k && j==l){continue;}
                         if(temp_Pin[i][j].coord[0].x == temp_Pin[k][l].coord[0].x && temp_Pin[i][j].coord[0].y == temp_Pin[k][l].coord[0].y &&
    temp_Pin[i][j].coord[1].x == temp_Pin[k][l].coord[1].x && temp_Pin[i][j].coord[1].y == temp_Pin[k][l].coord[1].y && temp_Pin[i][j].metalIdx ==
    temp_Pin[k][l].metalIdx){std::cout<<"Pin Error"<<std::endl;}
                      }
                 }
            }
       }
  */
  return Pin;
};

std::vector<RouterDB::Metal> DetailRouter::findGlobalPath(RouterDB::Net temp_net) {
  std::vector<RouterDB::Metal> temp_metal;

  for (unsigned int i = 0; i < temp_net.seg.size(); i++) {
    int chosenCand = temp_net.seg[i].chosenCand;
    if (chosenCand == -1) {
      continue;
    }
    for (unsigned int j = 0; j < temp_net.seg[i].candis[chosenCand].metals.size(); j++) {
      temp_metal.push_back(temp_net.seg[i].candis[chosenCand].metals[j]);
    }
  }

  return temp_metal;
};

void DetailRouter::splitPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::Net& temp_net) {
  RouterDB::point temp_point = temp_path[0][0].LinePoint[0];
  int temp_metalIdx = temp_path[0][0].MetalIdx;
  int found_index = -1;

  RouterDB::point Lpoint;
  RouterDB::point Upoint;

  for (unsigned int i = 0; i < temp_net.path_metal.size(); i++) {
    if (temp_net.path_metal[i].LinePoint[0].x == temp_net.path_metal[i].LinePoint[1].x) {
      if (temp_net.path_metal[i].LinePoint[0].y <= temp_net.path_metal[i].LinePoint[1].y) {
        Lpoint = temp_net.path_metal[i].LinePoint[0];
        Upoint = temp_net.path_metal[i].LinePoint[1];
      } else {
        Lpoint = temp_net.path_metal[i].LinePoint[1];
        Upoint = temp_net.path_metal[i].LinePoint[0];
      }

    } else {
      if (temp_net.path_metal[i].LinePoint[0].x <= temp_net.path_metal[i].LinePoint[1].x) {
        Lpoint = temp_net.path_metal[i].LinePoint[0];
        Upoint = temp_net.path_metal[i].LinePoint[1];
      } else {
        Lpoint = temp_net.path_metal[i].LinePoint[1];
        Upoint = temp_net.path_metal[i].LinePoint[0];
      }
    }

    if (temp_metalIdx == temp_net.path_metal[i].MetalIdx && temp_point.x > Lpoint.x && temp_point.x < Upoint.x && temp_point.y == Lpoint.y &&
        temp_point.y == Upoint.y) {
      found_index = i;
      break;
    }

    if (temp_metalIdx == temp_net.path_metal[i].MetalIdx && temp_point.x == Lpoint.x && temp_point.x == Upoint.x && temp_point.y > Lpoint.y &&
        temp_point.y < Upoint.y) {
      found_index = i;
      break;
    }
  }

  if (found_index != -1) {
    RouterDB::point End_point = temp_net.path_metal[found_index].LinePoint[1];
    temp_net.path_metal[found_index].LinePoint[1] = temp_point;
    RouterDB::Metal temp_metal;
    temp_metal.MetalIdx = temp_net.path_metal[found_index].MetalIdx;
    temp_metal.LinePoint.push_back(temp_point);
    temp_metal.LinePoint.push_back(End_point);
    temp_metal.width = drc_info.Metal_info[temp_metalIdx].width;
    temp_net.path_metal.insert(temp_net.path_metal.begin() + found_index + 1, temp_metal);
  }
};

void DetailRouter::lastmile_source_new(std::vector<std::vector<RouterDB::Metal> >& temp_path, std::vector<RouterDB::SinkData> temp_source) {
  RouterDB::point temp_point = temp_path[0][0].LinePoint[0];
  int temp_metal_metalidx = temp_path[0][0].MetalIdx;
  // int temp_metal_metalidx = 5;
  int point_flag = 0;  // 0 is ll, 1 is ur

  RouterDB::point source_point;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for (unsigned int i = 0; i < temp_source.size(); i++) {
    // if(temp_source[i].coord[0].x<=temp_source[i].coord[1].x &&
    // temp_source[i].coord[0].y<=temp_source[i].coord[1].y){}else{}//std::cout<<"EEroor"<<std::endl;}

    if (temp_point.x >= temp_source[i].coord[0].x && temp_point.y >= temp_source[i].coord[0].y && temp_point.x <= temp_source[i].coord[1].x &&
        temp_point.y <= temp_source[i].coord[1].y && temp_source[i].metalIdx == temp_metal_metalidx) {
      connected = 1;
    }

    if (abs(temp_source[i].coord[0].x - temp_point.x) + abs(temp_source[i].coord[0].y - temp_point.y) < dis && temp_source[i].metalIdx == temp_metal_metalidx) {
      dis = abs(temp_source[i].coord[0].x - temp_point.x) + abs(temp_source[i].coord[0].y - temp_point.y);
      source_point = temp_source[i].coord[0];
      point_flag = 0;
    }

    if (abs(temp_source[i].coord[1].x - temp_point.x) + abs(temp_source[i].coord[1].y - temp_point.y) < dis && temp_source[i].metalIdx == temp_metal_metalidx) {
      dis = abs(temp_source[i].coord[1].x - temp_point.x) + abs(temp_source[i].coord[1].y - temp_point.y);
      source_point = temp_source[i].coord[1];
      point_flag = 1;
    }
  }

  if (point_flag == 1) {
    source_point.x = source_point.x - drc_info.Metal_info[temp_metal_metalidx].width / 2;
    source_point.y = source_point.y - drc_info.Metal_info[temp_metal_metalidx].width / 2;
  } else {
    source_point.x = source_point.x + drc_info.Metal_info[temp_metal_metalidx].width / 2;
    source_point.y = source_point.y + drc_info.Metal_info[temp_metal_metalidx].width / 2;
  }

  if (connected == 0) {
    // std::cout<<"source unconnected"<<std::endl;
    // std::cout<<"Source point ("<<source_point.x<<" "<<source_point.y<<")"<<std::endl;
    // std::cout<<"Dest point ("<<temp_point.x<<" "<<temp_point.y<<")"<<std::endl;

    RouterDB::Metal temp_metal;
    temp_metal.MetalIdx = temp_metal_metalidx;
    // temp_metal.MetalIdx = 5;
    temp_metal.width = drc_info.Metal_info[temp_metal_metalidx].width;

    if (drc_info.Metal_info[temp_metal_metalidx].direct == 0) {  // v
      if (temp_point.x == source_point.x) {
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].begin(), temp_metal);
        // std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<"
        // "<<temp_path[0][0].LinePoint[1].y<<std::endl;
      } else {
        temp_metal.LinePoint.push_back(source_point);
        if (source_point.x > temp_point.x) {
          source_point.x = temp_point.x - drc_info.Metal_info[temp_metal_metalidx].width / 2;
        } else {
          source_point.x = temp_point.x + drc_info.Metal_info[temp_metal_metalidx].width / 2;
        }
        temp_metal.LinePoint.push_back(source_point);

        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].begin(), temp_metal);
        // std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<"
        // "<<temp_path[0][0].LinePoint[1].y<<std::endl;

        temp_metal.LinePoint.clear();
        source_point.x = temp_point.x;
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        temp_path[0].insert(temp_path[0].begin() + 1, temp_metal);
      }
    } else {
      if (temp_point.y == source_point.y) {
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].begin(), temp_metal);
        // std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<"
        // "<<temp_path[0][0].LinePoint[1].y<<std::endl;
      } else {
        temp_metal.LinePoint.push_back(source_point);
        if (source_point.y > temp_point.y) {
          source_point.y = temp_point.y - drc_info.Metal_info[temp_metal_metalidx].width / 2;
        } else {
          source_point.y = temp_point.y + drc_info.Metal_info[temp_metal_metalidx].width / 2;
        }
        temp_metal.LinePoint.push_back(source_point);

        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].begin(), temp_metal);
        // std::cout<<temp_path[0][0].LinePoint[0].x<<" "<<temp_path[0][0].LinePoint[0].y<<" "<<temp_path[0][0].LinePoint[1].x<<"
        // "<<temp_path[0][0].LinePoint[1].y<<std::endl;

        temp_metal.LinePoint.clear();
        source_point.y = temp_point.y;
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        temp_path[0].insert(temp_path[0].begin() + 1, temp_metal);
      }
    }
  }
};

void DetailRouter::lastmile_dest_new(std::vector<std::vector<RouterDB::Metal> >& temp_path, std::vector<RouterDB::SinkData> temp_source) {
  int last_index = temp_path[0].size() - 1;
  RouterDB::point temp_point = temp_path[0][last_index].LinePoint[1];
  int temp_metal_metalidx = temp_path[0][last_index].MetalIdx;
  // int temp_metal_metalidx = 6;

  RouterDB::point source_point;
  int point_flag = 0;

  int dis = INT_MAX;

  RouterDB::point center;

  int connected = 0;

  for (unsigned int i = 0; i < temp_source.size(); i++) {
    // if(temp_source[i].coord[0].x<=temp_source[i].coord[1].x && temp_source[i].coord[0].y<=temp_source[i].coord[1].y){}else{std::cout<<"EEroor"<<std::endl;}

    if (temp_point.x >= temp_source[i].coord[0].x && temp_point.y >= temp_source[i].coord[0].y && temp_point.x <= temp_source[i].coord[1].x &&
        temp_point.y <= temp_source[i].coord[1].y && temp_source[i].metalIdx == temp_metal_metalidx) {
      connected = 1;
    }

    if (abs(temp_source[i].coord[0].x - temp_point.x) + abs(temp_source[i].coord[0].y - temp_point.y) < dis && temp_source[i].metalIdx == temp_metal_metalidx) {
      dis = abs(temp_source[i].coord[0].x - temp_point.x) + abs(temp_source[i].coord[0].y - temp_point.y);
      source_point = temp_source[i].coord[0];
      point_flag = 0;
    }

    if (abs(temp_source[i].coord[1].x - temp_point.x) + abs(temp_source[i].coord[1].y - temp_point.y) < dis && temp_source[i].metalIdx == temp_metal_metalidx) {
      dis = abs(temp_source[i].coord[1].x - temp_point.x) + abs(temp_source[i].coord[1].y - temp_point.y);
      source_point = temp_source[i].coord[1];
      point_flag = 1;
    }
  }

  if (point_flag == 1) {
    source_point.x = source_point.x - drc_info.Metal_info[temp_metal_metalidx].width / 2;
    source_point.y = source_point.y - drc_info.Metal_info[temp_metal_metalidx].width / 2;
  } else {
    source_point.x = source_point.x + drc_info.Metal_info[temp_metal_metalidx].width / 2;
    source_point.y = source_point.y + drc_info.Metal_info[temp_metal_metalidx].width / 2;
  }

  RouterDB::point exch_point = source_point;
  source_point = temp_point;
  temp_point = exch_point;

  if (connected == 0) {
    // std::cout<<"Dest unconnected"<<std::endl;

    // std::cout<<"Dest unconnected"<<std::endl;
    // std::cout<<"Source point ("<<source_point.x<<" "<<source_point.y<<")"<<std::endl;
    // std::cout<<"Dest point ("<<temp_point.x<<" "<<temp_point.y<<")"<<std::endl;

    RouterDB::Metal temp_metal;
    temp_metal.MetalIdx = temp_metal_metalidx;
    // temp_metal.MetalIdx = 6;
    temp_metal.width = drc_info.Metal_info[temp_metal_metalidx].width;
    // temp_metal.LinePoint.push_back(source_point);

    if (drc_info.Metal_info[temp_metal_metalidx].direct == 0) {  // v

      if (source_point.x == temp_point.x) {
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].end(), temp_metal);
        // int last_end_index = temp_path[0].size()-1;
        // std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<"
        // "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
      } else {
        temp_metal.LinePoint.push_back(source_point);
        if (source_point.y > temp_point.y) {
          source_point.y = temp_point.y - drc_info.Metal_info[temp_metal_metalidx].width / 2;
        } else {
          source_point.y = temp_point.y + drc_info.Metal_info[temp_metal_metalidx].width / 2;
        }
        temp_metal.LinePoint.push_back(source_point);

        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].end(), temp_metal);
        temp_metal.LinePoint.clear();
        source_point.y = temp_point.y;
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        temp_path[0].insert(temp_path[0].end(), temp_metal);
        // int last_end_index = temp_path[0].size()-1;
        // std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<"
        // "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
      }

    } else {
      if (source_point.y == temp_point.y) {
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].end(), temp_metal);
        // int last_end_index = temp_path[0].size()-1;
        // std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<"
        // "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
      } else {
        temp_metal.LinePoint.push_back(source_point);
        if (source_point.x > temp_point.x) {
          source_point.x = temp_point.x - drc_info.Metal_info[temp_metal_metalidx].width / 2;
        } else {
          source_point.x = temp_point.x + drc_info.Metal_info[temp_metal_metalidx].width / 2;
        }
        temp_metal.LinePoint.push_back(source_point);

        // std::cout<<"path ( "<<temp_metal.LinePoint[0].x<<" "<<temp_metal.LinePoint[0].y<<") ("<<temp_metal.LinePoint[1].x<<" "<<temp_metal.LinePoint[1].y<<")
        // "<<std::endl;
        temp_path[0].insert(temp_path[0].end(), temp_metal);
        temp_metal.LinePoint.clear();
        source_point.x = temp_point.x;
        temp_metal.LinePoint.push_back(source_point);
        temp_metal.LinePoint.push_back(temp_point);
        temp_path[0].insert(temp_path[0].end(), temp_metal);
        // int last_end_index = temp_path[0].size()-1;
        // std::cout<<temp_path[0][last_end_index].LinePoint[0].x<<" "<<temp_path[0][last_end_index].LinePoint[0].y<<"
        // "<<temp_path[0][last_end_index].LinePoint[1].x<<" "<<temp_path[0][last_end_index].LinePoint[1].y<<std::endl;
      }
    }
  }
};

void DetailRouter::updateSource(std::vector<std::vector<RouterDB::Metal> > temp_path, std::vector<RouterDB::SinkData>& temp_source) {
  RouterDB::SinkData temp_sink;
  int width = 1;

  for (unsigned int i = 0; i < temp_path.size(); i++) {
    for (unsigned int j = 0; j < temp_path[i].size(); j++) {
      temp_sink.coord.clear();
      temp_sink.metalIdx = temp_path[i][j].MetalIdx;
      RouterDB::point Lpoint;
      RouterDB::point Upoint;

      RouterDB::point spoint;
      RouterDB::point epoint;
      spoint = temp_path[i][j].LinePoint[0];
      epoint = temp_path[i][j].LinePoint[1];

      if (spoint.x == epoint.x) {
        if (spoint.y <= epoint.y) {
          Lpoint.x = spoint.x - width;
          Lpoint.y = spoint.y;
          Upoint.x = epoint.x + width;
          Upoint.y = epoint.y;
        } else {
          Lpoint.x = epoint.x - width;
          Lpoint.y = epoint.y;
          Upoint.x = spoint.x + width;
          Upoint.y = spoint.y;
        }

      } else {
        if (spoint.x <= epoint.x) {
          Lpoint.x = spoint.x;
          Lpoint.y = spoint.y - width;
          Upoint.x = epoint.x;
          Upoint.y = epoint.y + width;
        } else {
          Lpoint.x = epoint.x;
          Lpoint.y = epoint.y - width;
          Upoint.x = spoint.x;
          Upoint.y = spoint.y + width;
        }
      }

      temp_sink.coord.push_back(Lpoint);
      temp_sink.coord.push_back(Upoint);
      temp_source.push_back(temp_sink);
    }
  }
};

void DetailRouter::returnPath(std::vector<std::vector<RouterDB::Metal> > temp_path, RouterDB::Net& temp_net) {
  for (unsigned int i = 0; i < temp_path.size(); i++) {
    for (unsigned int j = 0; j < temp_path[i].size(); j++) {
      temp_net.path_metal.push_back(temp_path[i][j]);
    }
  }
};

void DetailRouter::Physical_metal_via() {
  for (unsigned int i = 0; i < Nets.size(); i++) {
    GetPhsical_Metal_Via(i);
  }
};

void DetailRouter::UpdateVia(RouterDB::Via& temp_via) {
  // ViaRect
  temp_via.ViaRect.metal = temp_via.model_index;
  temp_via.ViaRect.placedCenter = temp_via.position;
  temp_via.ViaRect.placedLL.x = drc_info.Via_model[temp_via.model_index].ViaRect[0].x + temp_via.position.x;
  temp_via.ViaRect.placedLL.y = drc_info.Via_model[temp_via.model_index].ViaRect[0].y + temp_via.position.y;
  temp_via.ViaRect.placedUR.x = drc_info.Via_model[temp_via.model_index].ViaRect[1].x + temp_via.position.x;
  temp_via.ViaRect.placedUR.y = drc_info.Via_model[temp_via.model_index].ViaRect[1].y + temp_via.position.y;
  // LowerMetalRect
  temp_via.LowerMetalRect.metal = drc_info.Via_model[temp_via.model_index].LowerIdx;
  temp_via.LowerMetalRect.placedCenter = temp_via.position;
  temp_via.LowerMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].LowerRect[0].x + temp_via.position.x;
  temp_via.LowerMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].LowerRect[0].y + temp_via.position.y;
  temp_via.LowerMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].LowerRect[1].x + temp_via.position.x;
  temp_via.LowerMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].LowerRect[1].y + temp_via.position.y;
  // UpperMetalRect
  temp_via.UpperMetalRect.metal = drc_info.Via_model[temp_via.model_index].UpperIdx;
  temp_via.UpperMetalRect.placedCenter = temp_via.position;
  temp_via.UpperMetalRect.placedLL.x = drc_info.Via_model[temp_via.model_index].UpperRect[0].x + temp_via.position.x;
  temp_via.UpperMetalRect.placedLL.y = drc_info.Via_model[temp_via.model_index].UpperRect[0].y + temp_via.position.y;
  temp_via.UpperMetalRect.placedUR.x = drc_info.Via_model[temp_via.model_index].UpperRect[1].x + temp_via.position.x;
  temp_via.UpperMetalRect.placedUR.y = drc_info.Via_model[temp_via.model_index].UpperRect[1].y + temp_via.position.y;
};

void DetailRouter::GetPhsical_Metal_Via(int i) {
  for (unsigned int h = 0; h < Nets[i].path_metal.size(); h++) {
    Nets[i].path_metal[h].MetalRect.metal = Nets[i].path_metal[h].MetalIdx;
    Nets[i].path_metal[h].MetalRect.placedCenter.x = (Nets[i].path_metal[h].LinePoint[0].x + Nets[i].path_metal[h].LinePoint[1].x) / 2;
    Nets[i].path_metal[h].MetalRect.placedCenter.y = (Nets[i].path_metal[h].LinePoint[0].y + Nets[i].path_metal[h].LinePoint[1].y) / 2;

    if (Nets[i].path_metal[h].LinePoint[0].y == Nets[i].path_metal[h].LinePoint[1].y) {
      if (Nets[i].path_metal[h].LinePoint[0].x < Nets[i].path_metal[h].LinePoint[1].x) {
        Nets[i].path_metal[h].MetalRect.placedLL.x = Nets[i].path_metal[h].LinePoint[0].x;
        Nets[i].path_metal[h].MetalRect.placedLL.y = Nets[i].path_metal[h].LinePoint[0].y - Nets[i].path_metal[h].width / 2;
        Nets[i].path_metal[h].MetalRect.placedUR.x = Nets[i].path_metal[h].LinePoint[1].x;
        Nets[i].path_metal[h].MetalRect.placedUR.y = Nets[i].path_metal[h].LinePoint[1].y + Nets[i].path_metal[h].width / 2;
      } else {
        Nets[i].path_metal[h].MetalRect.placedLL.x = Nets[i].path_metal[h].LinePoint[1].x;
        Nets[i].path_metal[h].MetalRect.placedLL.y = Nets[i].path_metal[h].LinePoint[1].y - Nets[i].path_metal[h].width / 2;
        Nets[i].path_metal[h].MetalRect.placedUR.x = Nets[i].path_metal[h].LinePoint[0].x;
        Nets[i].path_metal[h].MetalRect.placedUR.y = Nets[i].path_metal[h].LinePoint[0].y + Nets[i].path_metal[h].width / 2;
      }
    } else {
      if (Nets[i].path_metal[h].LinePoint[0].y < Nets[i].path_metal[h].LinePoint[1].y) {
        Nets[i].path_metal[h].MetalRect.placedLL.x = Nets[i].path_metal[h].LinePoint[0].x - Nets[i].path_metal[h].width / 2;
        ;
        Nets[i].path_metal[h].MetalRect.placedLL.y = Nets[i].path_metal[h].LinePoint[0].y;
        Nets[i].path_metal[h].MetalRect.placedUR.x = Nets[i].path_metal[h].LinePoint[1].x + Nets[i].path_metal[h].width / 2;
        ;
        Nets[i].path_metal[h].MetalRect.placedUR.y = Nets[i].path_metal[h].LinePoint[1].y;
      } else {
        Nets[i].path_metal[h].MetalRect.placedLL.x = Nets[i].path_metal[h].LinePoint[1].x - Nets[i].path_metal[h].width / 2;
        ;
        Nets[i].path_metal[h].MetalRect.placedLL.y = Nets[i].path_metal[h].LinePoint[1].y;
        Nets[i].path_metal[h].MetalRect.placedUR.x = Nets[i].path_metal[h].LinePoint[0].x + Nets[i].path_metal[h].width / 2;
        ;
        Nets[i].path_metal[h].MetalRect.placedUR.y = Nets[i].path_metal[h].LinePoint[0].y;
      }
    }

    if (Nets[i].path_metal[h].LinePoint[0].y == Nets[i].path_metal[h].LinePoint[1].y &&
        Nets[i].path_metal[h].LinePoint[0].x == Nets[i].path_metal[h].LinePoint[1].x) {
      Nets[i].path_metal[h].MetalRect.placedLL.x = Nets[i].path_metal[h].LinePoint[0].x - Nets[i].path_metal[h].width / 2;
      Nets[i].path_metal[h].MetalRect.placedLL.y = Nets[i].path_metal[h].LinePoint[0].y - Nets[i].path_metal[h].width / 2;
      Nets[i].path_metal[h].MetalRect.placedUR.x = Nets[i].path_metal[h].LinePoint[1].x + Nets[i].path_metal[h].width / 2;
      Nets[i].path_metal[h].MetalRect.placedUR.y = Nets[i].path_metal[h].LinePoint[1].y + Nets[i].path_metal[h].width / 2;
    }
  }

  std::vector<RouterDB::Via> Vias;
  RouterDB::Via temp_via;
  std::set<RouterDB::Via, RouterDB::ViaComp> set_via;

  for (unsigned int h = 0; h < Nets[i].path_metal.size(); h++) {
    int temp_metal_index = Nets[i].path_metal[h].MetalIdx;
    for (unsigned int l = 0; l < Nets[i].path_metal.size(); l++) {
      int next_metal_index = Nets[i].path_metal[l].MetalIdx;

      if (l == h) {
        continue;
      }

      if (temp_metal_index == next_metal_index - 1) {
        if (Nets[i].path_metal[h].LinePoint[0].x == Nets[i].path_metal[l].LinePoint[0].x &&
            Nets[i].path_metal[h].LinePoint[0].y == Nets[i].path_metal[l].LinePoint[0].y) {
          temp_via.position = Nets[i].path_metal[h].LinePoint[0];
          temp_via.model_index = temp_metal_index;
          UpdateVia(temp_via);
          set_via.insert(temp_via);
        }

        if (Nets[i].path_metal[h].LinePoint[0].x == Nets[i].path_metal[l].LinePoint[1].x &&
            Nets[i].path_metal[h].LinePoint[0].y == Nets[i].path_metal[l].LinePoint[1].y) {
          temp_via.position = Nets[i].path_metal[h].LinePoint[0];
          temp_via.model_index = temp_metal_index;
          UpdateVia(temp_via);
          set_via.insert(temp_via);
        }

        if (Nets[i].path_metal[h].LinePoint[1].x == Nets[i].path_metal[l].LinePoint[0].x &&
            Nets[i].path_metal[h].LinePoint[1].y == Nets[i].path_metal[l].LinePoint[0].y) {
          temp_via.position = Nets[i].path_metal[h].LinePoint[1];
          temp_via.model_index = temp_metal_index;
          UpdateVia(temp_via);
          set_via.insert(temp_via);
        }

        if (Nets[i].path_metal[h].LinePoint[1].x == Nets[i].path_metal[l].LinePoint[1].x &&
            Nets[i].path_metal[h].LinePoint[1].y == Nets[i].path_metal[l].LinePoint[1].y) {
          temp_via.position = Nets[i].path_metal[h].LinePoint[1];
          temp_via.model_index = temp_metal_index;
          UpdateVia(temp_via);
          set_via.insert(temp_via);
        }
      }
    }
  }

  std::set<RouterDB::Via, RouterDB::ViaComp>::iterator via_begin, via_end, via_it;
  via_begin = set_via.begin();
  via_end = set_via.end();

  for (via_it = via_begin; via_it != via_end; ++via_it) {
    Nets[i].path_via.push_back(*via_it);
  }
};

void DetailRouter::CreatePlistBlocks(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::Block>& Blocks) {
  // RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;
  for (std::vector<RouterDB::Block>::iterator bit = Blocks.begin(); bit != Blocks.end(); ++bit) {
    // 1. collect pin contacts on grids
    for (std::vector<RouterDB::Pin>::iterator pit = bit->pins.begin(); pit != bit->pins.end(); ++pit) {
      for (std::vector<RouterDB::contact>::iterator cit = pit->pinContacts.begin(); cit != pit->pinContacts.end(); ++cit) {
        mIdx = cit->metal;
        LLx = cit->placedLL.x;
        LLy = cit->placedLL.y;
        URx = cit->placedUR.x;
        URy = cit->placedUR.y;
        // std::cout<<"check point createplistBlocks 1 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
      }
      for (std::vector<RouterDB::Via>::iterator cit = pit->pinVias.begin(); cit != pit->pinVias.end(); ++cit) {
        mIdx = cit->UpperMetalRect.metal;
        LLx = cit->UpperMetalRect.placedLL.x;
        LLy = cit->UpperMetalRect.placedLL.y;
        URx = cit->UpperMetalRect.placedUR.x;
        URy = cit->UpperMetalRect.placedUR.y;
        // std::cout<<"check point createplistBlocks 2 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
        mIdx = cit->LowerMetalRect.metal;
        LLx = cit->LowerMetalRect.placedLL.x;
        LLy = cit->LowerMetalRect.placedLL.y;
        URx = cit->LowerMetalRect.placedUR.x;
        URy = cit->LowerMetalRect.placedUR.y;
        // std::cout<<"check point createplistBlocks 3 "<<mIdx<<std::endl;
        ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
      }
    }
    // 2. collect internal metals on grids
    for (std::vector<RouterDB::contact>::iterator pit = bit->InternalMetal.begin(); pit != bit->InternalMetal.end(); ++pit) {
      // std::cout<<"check point createplistBlocks 4.0 "<<std::endl;
      mIdx = pit->metal;
      LLx = pit->placedLL.x;
      LLy = pit->placedLL.y;
      URx = pit->placedUR.x;
      URy = pit->placedUR.y;
      // std::cout<<"check point createplistBlocks 4 "<<mIdx<<std::endl;
      // std::cout<<"LL ("<<LLx<<","<<LLy<<") UR ("<<URx<<","<<URy<<")"<<std::endl;
      ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
      // std::cout<<"check point createplistBlocks 4.5 "<<std::endl;
    }
    for (std::vector<RouterDB::Via>::iterator pit = bit->InternalVia.begin(); pit != bit->InternalVia.end(); ++pit) {
      mIdx = pit->UpperMetalRect.metal;
      LLx = pit->UpperMetalRect.placedLL.x;
      LLy = pit->UpperMetalRect.placedLL.y;
      URx = pit->UpperMetalRect.placedUR.x;
      URy = pit->UpperMetalRect.placedUR.y;
      // std::cout<<"check point createplistBlocks 5 "<<mIdx<<std::endl;
      ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
      mIdx = pit->LowerMetalRect.metal;
      LLx = pit->LowerMetalRect.placedLL.x;
      LLy = pit->LowerMetalRect.placedLL.y;
      URx = pit->LowerMetalRect.placedUR.x;
      URy = pit->LowerMetalRect.placedUR.y;
      // std::cout<<"check point createplistBlocks 6 "<<mIdx<<std::endl;
      ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
    }
  }
};

void DetailRouter::CreatePlistTerminals(std::vector<std::vector<RouterDB::point> >& plist, std::vector<RouterDB::terminal> Terminals) {
  // RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;

  for (unsigned int i = 0; i < Terminals.size(); i++) {
    for (unsigned int j = 0; j < Terminals[i].termContacts.size(); j++) {
      mIdx = Terminals[i].termContacts[j].metal;
      LLx = Terminals[i].termContacts[j].placedLL.x;
      LLy = Terminals[i].termContacts[j].placedLL.y;
      URx = Terminals[i].termContacts[j].placedUR.x;
      URy = Terminals[i].termContacts[j].placedUR.y;
      ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
    }
  }
};

void DetailRouter::UpdatePlistNets(std::vector<std::vector<RouterDB::Metal> >& physical_path, std::vector<std::vector<RouterDB::point> >& plist) {
  // RouterDB::point tmpP;
  int mIdx, LLx, LLy, URx, URy;

  GetPhsical_Metal(physical_path);

  // here intervia is not included
  for (unsigned int i = 0; i < physical_path.size(); i++) {
    for (unsigned int j = 0; j < physical_path[i].size(); j++) {
      mIdx = physical_path[i][j].MetalIdx;
      LLx = physical_path[i][j].MetalRect.placedLL.x;
      LLy = physical_path[i][j].MetalRect.placedLL.y;
      URx = physical_path[i][j].MetalRect.placedUR.x;
      URy = physical_path[i][j].MetalRect.placedUR.y;
      ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
    }
  }

  std::vector<RouterDB::contact> temp_via_contact;
  GetPhsical_Via_contacts(physical_path, temp_via_contact);

  for (unsigned int i = 0; i < temp_via_contact.size(); i++) {
    mIdx = temp_via_contact[i].metal;
    LLx = temp_via_contact[i].placedLL.x;
    LLy = temp_via_contact[i].placedLL.y;
    URx = temp_via_contact[i].placedUR.x;
    URy = temp_via_contact[i].placedUR.y;
    ConvertRect2GridPoints(plist, mIdx, LLx, LLy, URx, URy);
  }
};

void DetailRouter::GetPhsical_Via_contacts(std::vector<std::vector<RouterDB::Metal> > physical_path, std::vector<RouterDB::contact>& temp_via_contact) {
  RouterDB::Via temp_via;
  std::set<RouterDB::Via, RouterDB::ViaComp> set_via;

  for (unsigned int i = 0; i < physical_path.size(); i++) {
    std::vector<RouterDB::Metal> temp_path = physical_path[i];

    for (unsigned int j = 0; j < temp_path.size(); j++) {
      int temp_metal_index = temp_path[j].MetalIdx;

      for (unsigned int h = 0; h < temp_path.size(); h++) {
        int next_metal_index = temp_path[h].MetalIdx;

        if (j == h) {
          continue;
        }

        if (temp_metal_index == next_metal_index - 1) {
          if (temp_path[j].LinePoint[0].x == temp_path[h].LinePoint[0].x && temp_path[j].LinePoint[0].y == temp_path[h].LinePoint[0].y) {
            temp_via.position = temp_path[j].LinePoint[0];
            temp_via.model_index = temp_metal_index;
            UpdateVia(temp_via);
            set_via.insert(temp_via);
          }

          if (temp_path[j].LinePoint[0].x == temp_path[h].LinePoint[1].x && temp_path[j].LinePoint[0].y == temp_path[h].LinePoint[1].y) {
            temp_via.position = temp_path[j].LinePoint[0];
            temp_via.model_index = temp_metal_index;
            UpdateVia(temp_via);
            set_via.insert(temp_via);
          }

          if (temp_path[j].LinePoint[1].x == temp_path[h].LinePoint[0].x && temp_path[j].LinePoint[1].y == temp_path[h].LinePoint[0].y) {
            temp_via.position = temp_path[j].LinePoint[1];
            temp_via.model_index = temp_metal_index;
            UpdateVia(temp_via);
            set_via.insert(temp_via);
          }

          if (temp_path[j].LinePoint[1].x == temp_path[h].LinePoint[1].x && temp_path[j].LinePoint[1].y == temp_path[h].LinePoint[1].y) {
            temp_via.position = temp_path[j].LinePoint[1];
            temp_via.model_index = temp_metal_index;
            UpdateVia(temp_via);
            set_via.insert(temp_via);
          }
        }
      }
    }
  }

  std::set<RouterDB::Via, RouterDB::ViaComp>::iterator via_begin, via_end, via_it;
  via_begin = set_via.begin();
  via_end = set_via.end();

  for (via_it = via_begin; via_it != via_end; ++via_it) {
    temp_via_contact.push_back(via_it->UpperMetalRect);
    temp_via_contact.push_back(via_it->LowerMetalRect);
  }
};

void DetailRouter::GetPhsical_Metal(std::vector<std::vector<RouterDB::Metal> >& physical_path) {
  // via is not included here
  for (unsigned int i = 0; i < physical_path.size(); i++) {
    for (unsigned int j = 0; j < physical_path[i].size(); j++) {
      if (drc_info.Metal_info[physical_path[i][j].MetalIdx].direct == 1) {
        if (physical_path[i][j].LinePoint[0].x <= physical_path[i][j].LinePoint[1].x) {
          physical_path[i][j].MetalRect.placedLL.x = physical_path[i][j].LinePoint[0].x;
          physical_path[i][j].MetalRect.placedLL.y = physical_path[i][j].LinePoint[0].y - physical_path[i][j].width / 2;
          physical_path[i][j].MetalRect.placedUR.x = physical_path[i][j].LinePoint[1].x;
          physical_path[i][j].MetalRect.placedUR.y = physical_path[i][j].LinePoint[1].y + physical_path[i][j].width / 2;
        } else {
          physical_path[i][j].MetalRect.placedLL.x = physical_path[i][j].LinePoint[1].x;
          physical_path[i][j].MetalRect.placedLL.y = physical_path[i][j].LinePoint[1].y - physical_path[i][j].width / 2;
          physical_path[i][j].MetalRect.placedUR.x = physical_path[i][j].LinePoint[0].x;
          physical_path[i][j].MetalRect.placedUR.y = physical_path[i][j].LinePoint[0].y + physical_path[i][j].width / 2;
        }
      } else {
        if (physical_path[i][j].LinePoint[0].y <= physical_path[i][j].LinePoint[1].y) {
          physical_path[i][j].MetalRect.placedLL.x = physical_path[i][j].LinePoint[0].x - physical_path[i][j].width / 2;
          physical_path[i][j].MetalRect.placedLL.y = physical_path[i][j].LinePoint[0].y;
          physical_path[i][j].MetalRect.placedUR.x = physical_path[i][j].LinePoint[1].x + physical_path[i][j].width / 2;
          physical_path[i][j].MetalRect.placedUR.y = physical_path[i][j].LinePoint[1].y;
        } else {
          physical_path[i][j].MetalRect.placedLL.x = physical_path[i][j].LinePoint[1].x - physical_path[i][j].width / 2;
          physical_path[i][j].MetalRect.placedLL.y = physical_path[i][j].LinePoint[1].y;
          physical_path[i][j].MetalRect.placedUR.x = physical_path[i][j].LinePoint[0].x + physical_path[i][j].width / 2;
          physical_path[i][j].MetalRect.placedUR.y = physical_path[i][j].LinePoint[0].y;
        }
      }
    }
  }
};

void DetailRouter::ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  auto logger = spdlog::default_logger()->clone("router.DetailRouter.ConvertRect2GridPoints");

  RouterDB::point tmpP;
  int obs_l = 0;
  int obs_h = this->layerNo - 1;
  // std::cout<<"Enter converter"<<std::endl;

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
    // std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
  }
};

/*
void DetailRouter::ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  RouterDB::point tmpP;
  int obs_l=0;
  int obs_h=this->layerNo-1;
  if(drc_info.Metal_info[mIdx].direct==0) { // vertical metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_x;
    int newLLx=LLx-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    int newURx=URx+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundX=(newLLx%curlayer_unit==0) ? (newLLx+curlayer_unit) : ( (newLLx/curlayer_unit)*curlayer_unit<newLLx ? (newLLx/curlayer_unit+1)*curlayer_unit :
(newLLx/curlayer_unit)*curlayer_unit  ); for(int x=boundX; x<newURx; x+=curlayer_unit) { if(mIdx!=obs_l) { int
nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_y; int newLLy=LLy-nexlayer_unit; int newURy=URy+nexlayer_unit; int boundY=(newLLy%nexlayer_unit==0) ?
(newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit : (newLLy/nexlayer_unit)*nexlayer_unit  );
        for(int y=boundY; y<newURy; y+=nexlayer_unit) {
          if(x>=LLx && x<=URx && y>=LLy && y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_y;
        int newLLy=LLy-nexlayer_unit;
        int newURy=URy+nexlayer_unit;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit :
(newLLy/nexlayer_unit)*nexlayer_unit  ); for(int y=boundY; y<newURy; y+=nexlayer_unit) { if(x>=LLx && x<=URx && y>=LLy && y<=URy){ tmpP.x=x; tmpP.y=y;
plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else if(drc_info.Metal_info[mIdx].direct==1) { // horizontal metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_y;
    int newLLy=LLy-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    int newURy=URy+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundY=(newLLy%curlayer_unit==0) ? (newLLy+curlayer_unit) : ( (newLLy/curlayer_unit)*curlayer_unit<newLLy ? (newLLy/curlayer_unit+1)*curlayer_unit :
(newLLy/curlayer_unit)*curlayer_unit  ); for(int y=boundY; y<newURy; y+=curlayer_unit) { if(mIdx!=obs_l) { int
nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_x; int newLLx=LLx-nexlayer_unit; int newURx=URx+nexlayer_unit; int boundX=(newLLx%nexlayer_unit==0) ?
(newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit : (newLLx/nexlayer_unit)*nexlayer_unit  );
        for(int x=boundX; x<newURx; x+=nexlayer_unit) {
           if(x>=LLx && x<=URx && y>=LLy && y<=URy){
             tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
            }
           //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=obs_h) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_x;
        int newLLx=LLx-nexlayer_unit;
        int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit :
(newLLx/nexlayer_unit)*nexlayer_unit  ); for(int x=boundX; x<newURx; x+=nexlayer_unit) { if(x>=LLx && x<=URx && y>=LLy && y<=URy){ tmpP.x=x; tmpP.y=y;
plist.at(mIdx).push_back(tmpP);
            }
          //tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else {
    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
  }
}
*/

/*
void DetailRouter::ConvertRect2GridPoints(std::vector<std::vector<RouterDB::point> >& plist, int mIdx, int LLx, int LLy, int URx, int URy) {
  RouterDB::point tmpP;
  //tmpP.iterNet = Net_index;
  if(drc_info.Metal_info[mIdx].direct==0) { // vertical metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_x;
    //int newLLx=LLx-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    //int newURx=URx+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int newLLx=LLx;
    int newURx=URx;
    int boundX=(newLLx%curlayer_unit==0) ? (newLLx+curlayer_unit) : ( (newLLx/curlayer_unit)*curlayer_unit<newLLx ? (newLLx/curlayer_unit+1)*curlayer_unit :
(newLLx/curlayer_unit)*curlayer_unit  ); for(int x=boundX; x<newURx; x+=curlayer_unit) { if(mIdx!=this->lowest_metal) { int
nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_y;
        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        int newLLy=LLy;
        int newURy=URy;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit :
(newLLy/nexlayer_unit)*nexlayer_unit  ); for(int y=boundY; y<newURy; y+=nexlayer_unit) { tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=this->highest_metal) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_y;
        //int newLLy=LLy-nexlayer_unit;
        //int newURy=URy+nexlayer_unit;
        int newLLy=LLy;
        int newURy=URy;
        int boundY=(newLLy%nexlayer_unit==0) ? (newLLy+nexlayer_unit) : ( (newLLy/nexlayer_unit)*nexlayer_unit<newLLy ? (newLLy/nexlayer_unit+1)*nexlayer_unit :
(newLLy/nexlayer_unit)*nexlayer_unit  ); for(int y=boundY; y<newURy; y+=nexlayer_unit) { tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else if(drc_info.Metal_info[mIdx].direct==1) { // horizontal metal layer
    int curlayer_unit=drc_info.Metal_info.at(mIdx).grid_unit_y;
    int newLLy=LLy;
    int newURy=URy;
    //int newLLy=LLy-curlayer_unit+drc_info.Metal_info.at(mIdx).width/2;
    //int newURy=URy+curlayer_unit-drc_info.Metal_info.at(mIdx).width/2;
    int boundY=(newLLy%curlayer_unit==0) ? (newLLy+curlayer_unit) : ( (newLLy/curlayer_unit)*curlayer_unit<newLLy ? (newLLy/curlayer_unit+1)*curlayer_unit :
(newLLy/curlayer_unit)*curlayer_unit  ); for(int y=boundY; y<newURy; y+=curlayer_unit) { if(mIdx!=this->lowest_metal) { int
nexlayer_unit=drc_info.Metal_info.at(mIdx-1).grid_unit_x; int newLLx=LLx; int newURx=URx;
        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit :
(newLLx/nexlayer_unit)*nexlayer_unit  ); for(int x=boundX; x<newURx; x+=nexlayer_unit) { tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
      if(mIdx!=this->highest_metal) {
        int nexlayer_unit=drc_info.Metal_info.at(mIdx+1).grid_unit_x;
        int newLLx=LLx;
        int newURx=URx;
        //int newLLx=LLx-nexlayer_unit;
        //int newURx=URx+nexlayer_unit;
        int boundX=(newLLx%nexlayer_unit==0) ? (newLLx+nexlayer_unit) : ( (newLLx/nexlayer_unit)*nexlayer_unit<newLLx ? (newLLx/nexlayer_unit+1)*nexlayer_unit :
(newLLx/nexlayer_unit)*nexlayer_unit  ); for(int x=boundX; x<newURx; x+=nexlayer_unit) { tmpP.x=x; tmpP.y=y; plist.at(mIdx).push_back(tmpP);
        }
      }
    }
  } else {
    std::cout<<"Router-Error: incorrect routing direction"<<std::endl;
  }
};
*/

void DetailRouter::NetToNodeNet(PnRDB::hierNode& HierNode, RouterDB::Net& net, int net_index) {
  PnRDB::point tpoint;

  // including via
  // std::cout<<"Start NetToNodeNet"<<std::endl;

  for (unsigned int i = 0; i < net.path_metal.size(); i++) {
    PnRDB::Metal temp_metal;
    temp_metal.MetalIdx = net.path_metal[i].MetalIdx;
    temp_metal.width = net.path_metal[i].width;
    // std::cout<<"checkpoint 1"<<std::endl;
    tpoint.x = net.path_metal[i].LinePoint[0].x;
    tpoint.y = net.path_metal[i].LinePoint[0].y;
    temp_metal.LinePoint.push_back(tpoint);
    tpoint.x = net.path_metal[i].LinePoint[1].x;
    tpoint.y = net.path_metal[i].LinePoint[1].y;
    temp_metal.LinePoint.push_back(tpoint);
    temp_metal.MetalRect.metal = drc_info.Metal_info[net.path_metal[i].MetalRect.metal].name;
    // std::cout<<"checkpoint 2"<<std::endl;
    temp_metal.MetalRect.placedBox.LL.x = net.path_metal[i].MetalRect.placedLL.x;
    temp_metal.MetalRect.placedBox.LL.y = net.path_metal[i].MetalRect.placedLL.y;
    temp_metal.MetalRect.placedBox.UR.x = net.path_metal[i].MetalRect.placedUR.x;
    temp_metal.MetalRect.placedBox.UR.y = net.path_metal[i].MetalRect.placedUR.y;
    temp_metal.MetalRect.placedCenter.x = net.path_metal[i].MetalRect.placedCenter.x;
    temp_metal.MetalRect.placedCenter.y = net.path_metal[i].MetalRect.placedCenter.y;
    // std::cout<<"checkpoint 3"<<std::endl;
    HierNode.Nets[net_index].path_metal.push_back(temp_metal);
  }

  for (unsigned int i = 0; i < net.path_via.size(); i++) {
    PnRDB::Via temp_via;
    ConvertToViaPnRDB_Placed_Placed(temp_via, net.path_via[i]);
    HierNode.Nets[net_index].path_via.push_back(temp_via);
  }
};

void DetailRouter::NetToNodeInterMetal(PnRDB::hierNode& HierNode, RouterDB::Net& net) {
  // std::cout<<"Start NetToNodeInterMetal"<<std::endl;
  // blockspin to intermetal
  for (unsigned int i = 0; i < net.connected.size(); i++) {
    if (net.connected[i].type == RouterDB::BLOCK) {
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size(); j++) {
        PnRDB::contact temp_contact;
        ConvertToContactPnRDB_Placed_Origin(temp_contact, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
        HierNode.interMetals.push_back(temp_contact);
      }
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size(); j++) {
        PnRDB::Via temp_via;
        ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
        HierNode.interVias.push_back(temp_via);
      }
    }
  }

  // std::cout<<"Via"<<std::endl;
  // including via
  for (unsigned int i = 0; i < net.path_metal.size(); i++) {
    // std::cout<<"seg "<<i<<std::endl;
    PnRDB::contact temp_contact;
    ConvertToContactPnRDB_Placed_Origin(temp_contact, net.path_metal[i].MetalRect);
    HierNode.interMetals.push_back(temp_contact);
  }
  for (unsigned int i = 0; i < net.path_via.size(); i++) {
    // std::cout<<"vias "<<j<<std::endl;

    PnRDB::Via temp_via;
    ConvertToViaPnRDB_Placed_Origin(temp_via, net.path_via[i]);
    HierNode.interVias.push_back(temp_via);
  }

  // std::cout<<"END par"<<std::endl;
};

void DetailRouter::NetToNodeBlockPins(PnRDB::hierNode& HierNode, RouterDB::Net& net) {
  auto logger = spdlog::default_logger()->clone("router.DetailRouter.NetToNodeBlockPins");

  // std::cout<<"Start NetToNodeBlockPins"<<std::endl;
  // wbxu: when update hierNode data, all the coordinates should be stored into
  // origin fields, NOT placed fields. Because the hierNode data will be checkin back to higher nodes [fixed]
  PnRDB::pin temp_pin;
  // PnRDB::point temp_point;
  // wbxu: the name should be the name of terminal, not the net name! [fixed]
  if (net.terminal_idx == -1) {
    logger->error("Router-Warning: cannot found terminal conntecting to net");
    return;
  }
  temp_pin.name = Terminals.at(net.terminal_idx).name;

  if (this->isTop) {
    PnRDB::contact temp_contact;
    ConvertToContactPnRDB_Placed_Origin(temp_contact, Terminals.at(net.terminal_idx).termContacts[0]);
    temp_pin.pinContacts.push_back(temp_contact);
  }

  // blockspin to intermetal
  for (unsigned int i = 0; i < net.connected.size(); i++) {
    if (net.connected[i].type == RouterDB::BLOCK) {
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts.size(); j++) {
        PnRDB::contact temp_contact;
        ConvertToContactPnRDB_Placed_Origin(temp_contact, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinContacts[j]);
        temp_pin.pinContacts.push_back(temp_contact);
      }
      for (unsigned int j = 0; j < Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias.size(); j++) {
        PnRDB::Via temp_via;
        ConvertToViaPnRDB_Placed_Origin(temp_via, Blocks[net.connected[i].iter2].pins[net.connected[i].iter].pinVias[j]);
        temp_pin.pinVias.push_back(temp_via);
      }
    }
  }

  for (unsigned int i = 0; i < net.path_metal.size(); i++) {
    // wbxu: placed field -> origin field [fixed]
    PnRDB::contact temp_contact;
    ConvertToContactPnRDB_Placed_Origin(temp_contact, net.path_metal[i].MetalRect);
    temp_pin.pinContacts.push_back(temp_contact);
  }
  for (unsigned int i = 0; i < net.path_via.size(); i++) {
    // wbxu: placed field -> origin field [fixed]
    PnRDB::Via temp_via;
    ConvertToViaPnRDB_Placed_Origin(temp_via, net.path_via[i]);
    temp_pin.pinVias.push_back(temp_via);
  }

  HierNode.blockPins.push_back(temp_pin);
  // std::cout<<"END NetToNodeBlockPins"<<std::endl;
};

void DetailRouter::ReturnHierNode(PnRDB::hierNode& HierNode) {
  HierNode.blockPins.clear();
  HierNode.interMetals.clear();
  HierNode.interVias.clear();

  for (unsigned int i = 0; i < HierNode.Terminals.size(); i++) {
    HierNode.Terminals[i].termContacts.clear();
  }

  for (unsigned int i = 0; i < HierNode.Nets.size(); i++) {
    HierNode.Nets[i].path_metal.clear();
    HierNode.Nets[i].path_via.clear();
  }

  // distinguish those two net
  // std::cout<<"Start ReturnHierNode"<<std::endl;
  for (unsigned int i = 0; i < Nets.size(); i++) {
    // std::cout<<i<<" ter? "<<Nets[i].isTerminal<<std::endl;
    if (Nets[i].isTerminal) {
      // wbxu: not only nets should be put into NodeBlockPins, but also those pins connected to nets
      // should be put into NodeBlockPins
      // return blockpins
      // std::cout<<"test net to block pin: start"<<std::endl;
      NetToNodeBlockPins(HierNode, Nets[i]);
      // std::cout<<"test net to block pin: end"<<std::endl;

    } else {
      // wbxu: not only nets should be put into NodeInterMetal, but also those pins connected to nets
      // should be put into NodeInterMetal
      // HierNode.interMetals
      // std::cout<<"test net to InterMetal: start"<<std::endl;
      NetToNodeInterMetal(HierNode, Nets[i]);
      // std::cout<<"test net to InterMetal: end"<<std::endl;
    }

    for (unsigned int j = 0; j < HierNode.Nets.size(); j++) {
      if (HierNode.Nets[j].name == Nets[i].netName) {
        HierNode.Nets.at(j).path_metal.clear();
        HierNode.Nets.at(j).path_via.clear();
        // std::cout<<"test net to net: start"<<std::endl;
        NetToNodeNet(HierNode, Nets[i], j);
        // std::cout<<"test net to net: end"<<std::endl;
        break;
      }
    }
  }

  if (isTop == 1) {
    // return terminal to node terminal
    // std::cout<<"test terminal to termina: start"<<std::endl;
    TerminalToNodeTerminal(HierNode);
    // std::cout<<"test terminal to termina: end"<<std::endl;
  }
  // std::cout<<"test blockintermetal to node intermetal: start"<<std::endl;
  BlockInterMetalToNodeInterMetal(HierNode);
  // std::cout<<"test blockintermetal to node intermetal: end"<<std::endl;
  // std::cout<<"End ReturnHierNode"<<std::endl;
};
