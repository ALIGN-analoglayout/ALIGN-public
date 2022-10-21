#include "GcellGlobalRouter.h"

#include "spdlog/spdlog.h"

extern "C" {
#include <stdio.h>

#include "lp_lib.h"
// SMB
//#define LPSOLVEAPIFROMLIBDEF
//#include "lp_explicit.h"
}

GcellGlobalRouter::GcellGlobalRouter(){

};

void GcellGlobalRouter::PlotGlobalRouter() {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.PlotGlobalRouter");

  logger->debug("Global-Router-Info: create gnuplot file");
  std::ofstream fout;
  std::string outfile = "global_router.plt";
  fout.open(outfile);

  // set title
  fout << "#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)" << std::endl;
  fout << "\nset title\" global router results"
       << " \"" << std::endl;
  fout << "\nset nokey" << std::endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << std::endl;
  fout << "#   to save an EPS file for inclusion into a latex document" << std::endl;
  fout << "# set terminal postscript eps color solid 20" << std::endl;
  fout << "# set output \"result.eps\"" << std::endl << std::endl;
  fout << "#   Uncomment these two lines starting with \"set\"" << std::endl;
  fout << "#   to save a PS file for printing" << std::endl;
  fout << "set term jpeg" << std::endl;
  fout << "set output \"result.jpg\"" << std::endl << std::endl;

  // set range
  fout << "\nset xrange [" << this->LL.x - 5000 << ":" << this->UR.x + 5000 << "]" << std::endl;
  fout << "\nset yrange [" << this->LL.y - 5000 << ":" << this->UR.y + 5000 << "]" << std::endl;

  fout << "\nplot[:][:] \'-\' with lines linestyle 1,";

  for (unsigned int i = 0; i < Nets.size(); i++) {
    fout << " \'-\' with lines linestyle " << i + 2 << ",";
  }

  fout << "\nEOF" << std::endl;

  // plot connections
  auto plot_nets = [&](auto &nets) {
    for (unsigned int i = 0; i < nets.size(); i++) {
      for (unsigned int j = 0; j < nets[i].global_path.size(); j++) {
        auto first = nets[i].global_path[j].first;
        auto second = nets[i].global_path[j].second;

        auto sposx = this->Gcell.tiles_total[first].x;
        auto sposy = this->Gcell.tiles_total[first].y;
        auto eposx = this->Gcell.tiles_total[second].x;
        auto eposy = this->Gcell.tiles_total[second].y;

        fout << "\t" << sposx << "\t" << sposy << std::endl;
        fout << "\t" << eposx << "\t" << eposy << std::endl;
        fout << "\t" << sposx << "\t" << sposy << std::endl;
        fout << std::endl;
      }
      if (nets.size() > 0) fout << "\nEOF" << std::endl;
    }
  };

  plot_nets(Nets);
  fout.close();
};

void GcellGlobalRouter::AddContact(PnRDB::contact &temp_contact, json &temp_json_Contact, int unit) {
  json temp_json_contact;
  temp_json_contact["Physical Layer"] = temp_contact.metal;
  temp_json_contact["LLx"] = temp_contact.placedBox.LL.x * unit;
  temp_json_contact["LLy"] = temp_contact.placedBox.LL.y * unit;
  temp_json_contact["URx"] = temp_contact.placedBox.UR.x * unit;
  temp_json_contact["URy"] = temp_contact.placedBox.UR.y * unit;

  temp_json_Contact.push_back(temp_json_contact);
}

void GcellGlobalRouter::AddContacts(std::vector<PnRDB::contact> &temp_contact, json &temp_json_Contact, int unit) {
  for (unsigned int i = 0; i < temp_contact.size(); i++) {
    AddContact(temp_contact[i], temp_json_Contact, unit);
  }
}

void GcellGlobalRouter::PlotGlobalRouter_Json(PnRDB::hierNode &node) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.PlotGlobalRouter_Json");

  // logger->debug("JSON WRITE Global Router Results ");
  std::ofstream jsonStream;
  jsonStream.open("global_router_plt.json");
  json jsonTop;
  jsonTop["Cell Name"] = node.name;
  jsonTop["Units"] = "0.5nm";
  jsonTop["Istop"] = node.isTop;
  int unit = 1;

  json temp_box;
  temp_box["Physical Layer"] = "null";
  temp_box["LLx"] = 0 * unit;
  temp_box["LLy"] = 0 * unit;
  temp_box["URx"] = node.width * unit;
  temp_box["URy"] = node.height * unit;
  jsonTop["Cell box"] = temp_box;

  // node Blocks
  json jsonBlocks = json::array();
  for (unsigned int i = 0; i < node.Blocks.size(); i++) {
    int index = node.Blocks[i].selectedInstance;
    json temp_block;
    temp_block["Name"] = node.Blocks[i].instance.at(index).name;
    temp_block["Height"] = node.Blocks[i].instance.at(index).height;
    temp_block["Width"] = node.Blocks[i].instance.at(index).width;
    json box;
    box["Physical Layer"] = "null";
    box["LLx"] = node.Blocks[i].instance.at(index).placedBox.LL.x * unit;
    box["LLy"] = node.Blocks[i].instance.at(index).placedBox.LL.y * unit;
    box["URx"] = node.Blocks[i].instance.at(index).placedBox.UR.x * unit;
    box["URy"] = node.Blocks[i].instance.at(index).placedBox.UR.y * unit;
    temp_block["Box"] = box;

    // pins
    json block_pins = json::array();
    for (unsigned j = 0; j < node.Blocks[i].instance.at(index).blockPins.size(); j++) {
      json temp_pin;
      temp_pin["Name"] = node.Blocks[i].instance.at(index).blockPins[j].name;
      json temp_Contacts = json::array();
      json temp_Vias = json::array();
      AddContacts(node.Blocks[i].instance.at(index).blockPins[j].pinContacts, temp_Contacts, unit);
      temp_pin["Internal Metal"] = temp_Contacts;
      block_pins.push_back(temp_pin);
    }

    temp_block["Pins"] = block_pins;
    jsonBlocks.push_back(temp_block);
  }

  jsonTop["Blocks"] = jsonBlocks;

  // Gcell
  json jsonGcell = json::array();

  for (unsigned int i = 0; i < this->Gcell.tiles_total.size(); i++) {
    json temp_tile;
    temp_tile["x"] = this->Gcell.tiles_total[i].x;
    temp_tile["y"] = this->Gcell.tiles_total[i].y;
    temp_tile["Physical Layer"] = this->Gcell.tiles_total[i].metal[0];
    jsonGcell.push_back(temp_tile);
  }

  jsonTop["Gcell"] = jsonGcell;

  // GlobalRouter

  json jsonGlobalRoutes = json::array();

  for (unsigned int i = 0; i < this->Nets.size(); i++) {
    json json_temp_net;
    json_temp_net["name"] = this->Nets[i].netName;

    json json_terminals = json::array();
    for (unsigned int j = 0; j < this->Nets[i].terminals.size(); j++) {
      json json_temp_terminal;
      int tile_index = this->Nets[i].terminals[j];
      json_temp_terminal["x"] = this->Gcell.tiles_total[tile_index].x;
      json_temp_terminal["y"] = this->Gcell.tiles_total[tile_index].y;
      json_temp_terminal["Physical Layer"] = this->Gcell.tiles_total[tile_index].metal[0];
      json_terminals.push_back(json_temp_terminal);
    }
    json_temp_net["terminals"] = json_terminals;

    json json_global_path = json::array();
    for (unsigned int j = 0; j < this->Nets[i].global_path.size(); j++) {
      json json_temp_path;
      int start_index = this->Nets[i].global_path[j].first;
      int end_index = this->Nets[i].global_path[j].second;
      json_temp_path["llx"] = this->Gcell.tiles_total[start_index].x;
      json_temp_path["lly"] = this->Gcell.tiles_total[start_index].y;
      json_temp_path["Physical Layer ll"] = this->Gcell.tiles_total[start_index].metal[0];
      json_temp_path["urx"] = this->Gcell.tiles_total[end_index].x;
      json_temp_path["ury"] = this->Gcell.tiles_total[end_index].y;
      json_temp_path["Physical Layer ur"] = this->Gcell.tiles_total[end_index].metal[0];
      json_global_path.push_back(json_temp_path);
    }
    json_temp_net["global_path"] = json_global_path;
    /*
            json json_steiner_node=json::array();
            for(unsigned int j=0;j<this->Nets[i].steiner_node.size();j++){
               json json_temp_steiner_node;
               int index = this->Nets[i].steiner_node[j];
               json_temp_steiner_node["x"] = this->Gcell.tiles_total[index].x;
               json_temp_steiner_node["y"] = this->Gcell.tiles_total[index].y;
               json_temp_steiner_node["Physical Layer"]=this->Gcell.tiles_total[index].metal[0];
               json_steiner_node.push_back(json_temp_steiner_node);
            }
            json_temp_net["steiner_node"]=json_steiner_node;
    */
    jsonGlobalRoutes.push_back(json_temp_net);
  }

  jsonTop["Glbaol_Routes"] = jsonGlobalRoutes;

  jsonStream << std::setw(4) << jsonTop;
  jsonStream.close();
  // logger->debug(" JSON FINALIZE {0}", node.name);
};

void GcellGlobalRouter::AssignMetal(RouterDB::terminal &temp_Terminal, int horizontal_index, int vertical_index, int times) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.AssignMetal");

  // logger->debug("start assign metal");
  RouterDB::point temp_point;
  temp_point.x = temp_Terminal.termContacts[0].placedCenter.x;
  temp_point.y = temp_Terminal.termContacts[0].placedCenter.y;
  if (temp_point.x < 0 || temp_point.x > UR.x || temp_point.y < 0 || temp_point.y > UR.y) {
    // logger->error("Error Box {0} {1}", temp_point.x, temp_point.y);
    assert(0);
  }
  // logger->debug("terminal center {0} {1}", temp_point.x, temp_point.y);

  int h_pitches = drc_info.Metal_info[horizontal_index].grid_unit_y;
  int h_width = drc_info.Metal_info[horizontal_index].width;
  int h_minL = drc_info.Metal_info[horizontal_index].minL;
  // int h_ee = drc_info.Metal_info[horizontal_index].dist_ee;
  int h_metal = horizontal_index;
  // logger->debug("hminL {0}", times * h_minL);
  int v_pitches = drc_info.Metal_info[vertical_index].grid_unit_x;
  int v_width = drc_info.Metal_info[vertical_index].width;
  int v_minL = drc_info.Metal_info[vertical_index].minL;
  // int v_ee = drc_info.Metal_info[vertical_index].dist_ee;
  int v_metal = vertical_index;
  // logger->debug("vminL {0}", times * v_minL);
  if (temp_point.y == LL.y || temp_point.y == UR.y) {
    // assgin this terminal to horizontal metal, currently M2

    RouterDB::contact temp_contact;
    temp_contact.placedCenter = temp_point;
    temp_contact.originCenter = temp_point;
    RouterDB::point temp_LL = temp_point;
    RouterDB::point temp_UR = temp_point;
    temp_LL.x = temp_LL.x - times * h_minL / 2;
    temp_UR.x = temp_UR.x + times * h_minL / 2;
    temp_LL.y = temp_LL.y - h_width / 2;
    temp_UR.y = temp_UR.y + h_width / 2;
    temp_contact.originLL = temp_LL;
    temp_contact.originUR = temp_UR;
    temp_contact.placedLL = temp_LL;
    temp_contact.placedUR = temp_UR;
    temp_contact.metal = h_metal;
    temp_Terminal.termContacts.clear();
    temp_Terminal.termContacts.push_back(temp_contact);
    // logger->debug("Terminal box {0} {1} {2} {3}", temp_LL.x, temp_LL.y, temp_UR.x, temp_UR.y);
    // logger->debug("end assign metal");
    return;
  }

  if (temp_point.x == LL.x || temp_point.x == UR.x) {
    // assgin this terminal to verital, currenly M1

    RouterDB::contact temp_contact;
    temp_contact.placedCenter = temp_point;
    temp_contact.originCenter = temp_point;
    RouterDB::point temp_LL = temp_point;
    RouterDB::point temp_UR = temp_point;
    temp_LL.x = temp_LL.x - v_width / 2;
    temp_UR.x = temp_UR.x + v_width / 2;
    temp_LL.y = temp_LL.y - times * v_minL / 2;
    temp_UR.y = temp_UR.y + times * v_minL / 2;
    temp_contact.originLL = temp_LL;
    temp_contact.originUR = temp_UR;
    temp_contact.placedLL = temp_LL;
    temp_contact.placedUR = temp_UR;
    temp_contact.metal = v_metal;
    temp_Terminal.termContacts.clear();
    temp_Terminal.termContacts.push_back(temp_contact);
    // logger->debug("Terminal box {0} {1} {2} {3}", temp_LL.x, temp_LL.y, temp_UR.x, temp_UR.y);
    // logger->debug("end assign metal");
    return;
  }

  if (temp_point.x % v_pitches != 0 && temp_point.y % h_pitches != 0) {
    logger->error("Terminal off grid, please check the width/height of module");
    assert(0);
  }
};

void GcellGlobalRouter::Determine_Terminal_Center(int horizontal_index, int vertical_index, int times) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.Determine_Terminal_Center");

  // logger->debug("Start determine a terminal");

  int h_pitches = drc_info.Metal_info[horizontal_index].grid_unit_y;
  // int h_width = drc_info.Metal_info[horizontal_index].width;
  int h_minL = drc_info.Metal_info[horizontal_index].minL;
  int h_ee = drc_info.Metal_info[horizontal_index].dist_ee;
  // int h_metal = horizontal_index;

  int v_pitches = drc_info.Metal_info[vertical_index].grid_unit_x;
  // int v_width = drc_info.Metal_info[vertical_index].width;
  int v_minL = drc_info.Metal_info[vertical_index].minL;
  int v_ee = drc_info.Metal_info[vertical_index].dist_ee;
  // int v_metal = vertical_index;
  // int times = 2;
  int h_dist = times * h_minL + times * h_ee + 3 * h_pitches;
  int v_dist = times * v_minL + times * v_ee + 3 * v_pitches;
  int h_index = (UR.x - LL.x) / (h_dist);
  int v_index = (UR.y - LL.y) / (v_dist);
  std::vector<int> v_L;
  std::vector<int> v_U;
  std::vector<int> h_L;
  std::vector<int> h_U;

  for (int i = 0; i < h_index; i++) {
    h_L.push_back(0);
    h_U.push_back(0);
  }

  for (int i = 0; i < v_index; i++) {
    v_L.push_back(0);
    v_U.push_back(0);
  }

  for (unsigned int i = 0; i < Terminals.size(); i++) {
    RouterDB::point temp_point;
    RouterDB::point new_temp_point;
    temp_point.x = Terminals[i].termContacts[0].placedCenter.x;
    temp_point.y = Terminals[i].termContacts[0].placedCenter.y;
    int min_dist = INT_MAX;
    int min_index = -1;
    int dis = 0;
    int found_v_L = 0;
    int found_v_U = 0;
    int found_h_L = 0;
    int found_h_U = 0;

    for (int j = 1; j < int(v_L.size()); j++) {
      dis = abs(temp_point.y - j * v_dist - LL.y) + abs(temp_point.x - LL.x);
      if (dis < min_dist && v_L[j] == 0) {
        min_dist = dis;
        min_index = j;
        found_v_L = 1;
        found_v_U = 0;
        found_h_L = 0;
        found_h_U = 0;
        new_temp_point.y = j * v_dist + LL.y;
        new_temp_point.x = LL.x;
      }
    }

    for (int j = 1; j < int(v_U.size()); j++) {
      dis = abs(temp_point.y - j * v_dist - LL.y) + abs(temp_point.x - UR.x);
      if (dis < min_dist && v_U[j] == 0) {
        min_dist = dis;
        min_index = j;
        found_v_L = 0;
        found_v_U = 1;
        found_h_L = 0;
        found_h_U = 0;
        new_temp_point.y = j * v_dist + LL.y;
        new_temp_point.x = UR.x;
      }
    }

    for (int j = 1; j < int(h_L.size()); j++) {
      dis = abs(temp_point.x - j * h_dist - LL.x) + abs(temp_point.y - LL.y);
      if (dis < min_dist && h_L[j] == 0) {
        min_dist = dis;
        min_index = j;
        found_v_L = 0;
        found_v_U = 0;
        found_h_L = 1;
        found_h_U = 0;
        new_temp_point.x = j * h_dist + LL.x;
        new_temp_point.y = LL.y;
      }
    }

    for (int j = 1; j < int(h_U.size()); j++) {
      dis = abs(temp_point.x - j * h_dist - LL.x) + abs(temp_point.y - UR.y);
      if (dis < min_dist && h_U[j] == 0) {
        min_dist = dis;
        min_index = j;
        found_v_L = 0;
        found_v_U = 0;
        found_h_L = 0;
        found_h_U = 1;
        new_temp_point.x = j * h_dist + LL.x;
        new_temp_point.y = UR.y;
      }
    }

    if (found_v_L == 0 && found_v_U == 0 && found_h_L == 0 && found_h_U == 0) {
      logger->debug("Fail to determine a terminal");
    } else {
      Terminals[i].termContacts[0].placedCenter = new_temp_point;
      if (found_v_L) {
        v_L[min_index] = 1;
      }
      if (found_v_U) {
        v_U[min_index] = 1;
      }
      if (found_h_L) {
        h_L[min_index] = 1;
      }
      if (found_h_U) {
        h_U[min_index] = 1;
      }
    }
  }
  // logger->debug("Finish Determine terminal");
  return;
};

void GcellGlobalRouter::PlaceTerminal() {
  int horizontal_index = 0;
  int vertical_index = 0;

  for (unsigned int i = 0; i < this->drc_info.Metal_info.size(); i++) {
    if (drc_info.Metal_info[i].direct == 1) {
      // H
      horizontal_index = i;
      break;
    }
  }

  for (unsigned int i = 0; i < this->drc_info.Metal_info.size(); i++) {
    if (drc_info.Metal_info[i].direct == 0) {
      // V
      vertical_index = i;
      break;
    }
  }

  int times = 3;
  Determine_Terminal_Center(horizontal_index, vertical_index, times);

  for (unsigned int i = 0; i < Terminals.size(); i++) {
    AssignMetal(Terminals[i], horizontal_index, vertical_index, times);
  }
};

GcellGlobalRouter::GcellGlobalRouter(PnRDB::hierNode &node, PnRDB::Drc_info &drcData, int Lmetal, int Hmetal) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.GcellGlobalRouter");

  terminal_routing = 0;
  // 1. Initial Drcdata and design data

  getDRCdata(drcData);
  getData(node, Lmetal, Hmetal);

  if (terminal_routing == 1) {
    // logger->debug("Begin Terminal Placement");
    PlaceTerminal();
    // logger->debug("End Terminal Placement");

  } else if (node.isIntelGcellGlobalRouter == false) {
    // logger->debug("Begin Terminal");
    placeTerminals();
    // logger->debug("End Terminal");
  }

  // 2. create GcellGlobalGrid
  // CreateGrid for within the region LL, UR
  int tile_size = 0;
  int chip_size = (UR.x - LL.x) * (UR.y - LL.y);
  if (chip_size < 1000000) {
    tile_size = 20;
  } else if (chip_size < 10000000000) {
    tile_size = 100;
  } else if (chip_size < 1000000000000) {
    tile_size = 1000;
  } else if (chip_size < 100000000000000) {
    tile_size = 10000;
  } else {
    tile_size = 100000;
  }

  int tileLayerNo = 1;  // Hmetal - Lmetal + 1;
  if (node.isIntelGcellGlobalRouter == true) {
    // SMB Override for Intel router
    tileLayerNo = 1;
    tile_size = 10;
  }
  for (auto net : Nets) {
    for (auto c : net.connected) {
      if (c.type == RouterDB::BLOCK) {
        for (auto pin_contact : Blocks[c.iter2].pins[c.iter].pinContacts) {
          if (pin_contact.metal < net.min_routing_layer - 1) {
            logger->error("Block {0} pin {1} is lower than min_routing_layer {2}", Blocks[c.iter2].blockName, Blocks[c.iter2].pins[c.iter].pinName,
                          net.min_routing_layer);
            continue;
          }
          if (pin_contact.metal < net.max_routing_layer - 1) {
            logger->error("Block {0} pin {1} is higher than max_routing_layer {2}", Blocks[c.iter2].blockName, Blocks[c.iter2].pins[c.iter].pinName,
                          net.max_routing_layer);
            continue;
          }
          // same for metal higher than max_routing_layer
          Lmetal = std::min(pin_contact.metal, Lmetal);
          Hmetal = std::max(pin_contact.metal, Hmetal);
        }
      }
    }
  }

  GlobalGrid Initial_Gcell = GlobalGrid(drc_info, LL.x, LL.y, UR.x, UR.y, Lmetal, Hmetal, tileLayerNo, tile_size);
  Initial_Gcell.ConvertGlobalInternalMetal(Blocks);
  Initial_Gcell.AdjustVerticalEdgeCapacityfromInternalMetal(Blocks);
  this->Gcell = GlobalGrid(Initial_Gcell);
  // Gcell = GlobalGrid(Initial_Gcell);
  // for(int i=0;i<Nets.size();++i){
  Gcell.ConvertGlobalBlockPin(Blocks, Nets, Nets.size());
  Gcell.AdjustPlateEdgeCapacity();
  Gcell.AdjustVerticalEdgeCapacityfromBlockPin(Blocks, Nets, Nets.size());

  //}
  Gcell.SetNetSink(Blocks, Nets, Terminals, terminal_routing);
  // Gcell.CreateGridDataNCap();
  // Gcell.CreateGridDataCap(true);

  // return;
  // end of global Grid

  int ST_number = 5;
  GlobalGraph GGgraph(Gcell);

  // here create a tiles set;
  std::set<RouterDB::tile, RouterDB::tileComp> Tile_Set = CreateTileSet(Gcell);

  SymNet(Gcell, Tile_Set);

  // 3. STs generation
  for (unsigned int i = 0; i < Nets.size(); ++i) {
    // std::cout<<"Nets index "<<i<<std::endl;
    // set terminals

    GGgraph.clearPath();

    for (unsigned int j = 0; j < Nets[i].connectedTile.size(); j++) {

      if(Nets[i].connectedTile[j].size() == 0) continue;

      if (Nets[i].connectedTile[j].size() == 0) {
        // std::cout<<"Nets[i].connectedTile[j] "<<i<<" "<<j<<" size is 0"<<std::endl;
        logger->error("Format Issue ");
        logger->error("Please check the net {0} in module {1}", Nets[i].netName, node.name);
        int iter = Nets[i].connected[j].iter;
        int iter2 = Nets[i].connected[j].iter2;
        if (Nets[i].connected[j].type == RouterDB::BLOCK) {
          logger->error("Especial the pin {0} in subblock {1}", Blocks[iter2].pins[iter].pinName, Blocks[iter2].blockName);
        } else {
          logger->error("Especial the terminal", Terminals[iter].name);
          // logger->debug("Current Box {0} {1} {2} {3}", LL.x, LL.y, UR.x, UR.y);
          // logger->debug("terminal box {0} {1} {2} {3}", Terminals[iter].termContacts[0].placedLL.x, Terminals[iter].termContacts[0].placedLL.y,
          //               Terminals[iter].termContacts[0].placedUR.x, Terminals[iter].termContacts[0].placedUR.y);
        }
        assert(0);
      }
    }

    // new_added for per net metal layer setting, remove this part if an error happens
    int l_metal = Nets[i].min_routing_layer; //
    int h_metal = Nets[i].max_routing_layer; //
    // add pin metal layer check, if pin's layer < Nets[i].min_routing_layer - 1 or pin's layer > Nets[i].min_routing_layer + 1
    // Nets[i].min_routing_layer - 1 <= pin's metal layer <= Nets[i].min_routing_layer + 1
    for(auto c:Nets[i].connected){
      if(c.type==RouterDB::BLOCK){
        for(auto pin_contact:Blocks[c.iter2].pins[c.iter].pinContacts){
          //same for metal higher than max_routing_layer
          l_metal = std::min(pin_contact.metal, l_metal);
          h_metal = std::max(pin_contact.metal, h_metal);
        }
      }
    }

    if(l_metal==-1) l_metal=0; //
    if(h_metal==-1) h_metal=drc_info.Metal_info.size()-1; //
    GGgraph.CreateAdjacentList_New(Gcell, l_metal, h_metal); // 

    GGgraph.setterminals(Nets[i].terminals);
    GGgraph.setTerminals(Nets[i].connectedTile);


    std::vector<int> Pontential_Stiner_node = Get_Potential_Steiner_node(Nets[i].terminals, Tile_Set, Gcell);

    // std::cout<<"terminal size "<<Nets[i].terminals.size()<<std::endl;
    // find STs

    GGgraph.FindSTs(Gcell, ST_number, Pontential_Stiner_node);
    // return STs

    std::vector<std::vector<std::pair<int, int> > > temp_path = GGgraph.returnPath();
    RouterDB::SteinerTree temp_st;


    for (unsigned int j = 0; j < temp_path.size(); ++j) {
      temp_st.path = temp_path[j];
      Nets[i].STs.push_back(temp_st);
    }
  }

  // for (unsigned int i = 0; i < this->Nets.size(); ++i) {
  //   // logger->debug("Before mirror Nets index {0}", i);

  //   for (unsigned int j = 0; j < this->Nets.at(i).STs.size(); ++j) {
  //     logger->debug("STs path size {0}", this->Nets.at(i).STs[j].path.size());
  //   }
  // }

  // 4. LP solve Q1. Symmetry here

  MirrorSymSTs(Gcell, Tile_Set);

  // for (unsigned int i = 0; i < this->Nets.size(); ++i) {
  //   logger->debug("after mirror Nets index {0}", i);

  //   for (unsigned int j = 0; j < this->Nets.at(i).STs.size(); ++j) {
  //     logger->debug("STs path size {0}", this->Nets.at(i).STs[j].path.size());
  //   }
  // }

  // for (unsigned int i = 0; i < this->Nets.size(); ++i) {
  //   logger->debug("Nets symmetry part {0} Nets global symmetry part {1}", this->Nets.at(i).symCounterpart, this->Nets.at(i).global_sym);
  // }


  ILPSolveRouting(Gcell, GGgraph, Tile_Set);
  // 5. Return hierNode  Q2. return some to hierNode for detial router

  ReturnHierNode(node);

  PlotGlobalRouter();

  PlotGlobalRouter_Json(node);

};

std::vector<int> GcellGlobalRouter::GenerateSTsUniqueV(RouterDB::Net &temp_net) {
  std::set<int> unique_set;
  std::vector<int> unique;
  for (unsigned int i = 0; i < temp_net.STs.size(); ++i) {
    for (unsigned int j = 0; j < temp_net.STs[i].path.size(); ++j) {
      unique_set.insert(temp_net.STs[i].path[j].first);
      unique_set.insert(temp_net.STs[i].path[j].second);
    }
  }

  std::set<int>::iterator it, it_low, it_up;
  it_low = unique_set.begin();
  it_up = unique_set.end();

  for (it = it_low; it != it_up; ++it) {
    unique.push_back(*it);
  }

  return unique;
};

void GcellGlobalRouter::CopySTs(RouterDB::Net &temp_net, RouterDB::Net &sy_temp_net, std::map<int, int> &temp_map, std::map<int, int> &sy_temp_map) {
  std::vector<std::vector<std::pair<int, int> > > path;

  std::vector<std::vector<std::pair<int, int> > > sy_path;

  for (unsigned int i = 0; i < temp_net.STs.size(); ++i) {
    std::vector<std::pair<int, int> > temp_sy_path;
    int cp_flag = CopyPath(temp_net.STs[i].path, temp_map, temp_sy_path);
    if (cp_flag) {
      path.push_back(temp_net.STs[i].path);
      sy_path.push_back(temp_sy_path);
    }
  }

  for (unsigned int i = 0; i < sy_temp_net.STs.size(); ++i) {
    std::vector<std::pair<int, int> > temp_sy_path;
    int cp_flag = CopyPath(sy_temp_net.STs[i].path, sy_temp_map, temp_sy_path);
    if (cp_flag) {
      sy_path.push_back(temp_net.STs[i].path);
      path.push_back(temp_sy_path);
    }
  }

  if (path.size() > 0) {
    temp_net.STs.clear();
    for (unsigned int i = 0; i < path.size(); ++i) {
      RouterDB::SteinerTree temp_tree;
      temp_tree.path = path[i];
      temp_net.STs.push_back(temp_tree);
    }
    sy_temp_net.STs.clear();
    for (unsigned int i = 0; i < sy_path.size(); ++i) {
      RouterDB::SteinerTree sy_temp_tree;
      sy_temp_tree.path = sy_path[i];
      sy_temp_net.STs.push_back(sy_temp_tree);
    }

  } else {
    temp_net.global_sym = -1;
    sy_temp_net.global_sym = -1;
  }
};

void GcellGlobalRouter::MirrorSymSTs(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set) {
  for (unsigned int i = 0; i < this->Nets.size(); ++i) {
    if (this->Nets.at(i).global_sym != -1 && this->Nets.at(i).global_sym < (int)this->Nets.size() - 1) {
      int global_sym = this->Nets.at(i).global_sym;
      std::vector<int> temp_vector = GenerateSTsUniqueV(this->Nets.at(i));
      std::vector<int> sy_vector = GenerateSTsUniqueV(this->Nets.at(global_sym));
      std::map<int, int> temp_map = GenerateSymMap(grid, Tile_Set, temp_vector, this->Nets.at(i).sym_H, this->Nets.at(i).global_sym);
      std::map<int, int> sy_temp_map = GenerateSymMap(grid, Tile_Set, sy_vector, this->Nets.at(global_sym).sym_H, this->Nets.at(global_sym).global_sym);
      CopySTs(this->Nets.at(i), this->Nets.at(global_sym), temp_map, sy_temp_map);
    }
  }
};

std::map<int, int> GcellGlobalRouter::GenerateSymMap(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, std::vector<int> terminals,
                                                     bool H, int center) {
  std::map<int, int> sy_map;

  for (unsigned int i = 0; i < terminals.size(); ++i) {
    RouterDB::tile temp_tile;
    temp_tile = grid.tiles_total[terminals[i]];
    if (H) {
      temp_tile.y = 2 * center - temp_tile.y;
    } else {
      temp_tile.x = 2 * center - temp_tile.x;
    }
    std::set<RouterDB::tile, RouterDB::tileComp>::iterator temp_it;
    temp_it = Tile_Set.find(temp_tile);
    if (temp_it == Tile_Set.end()) {
      sy_map.insert(map<int, int>::value_type(terminals[i], -1));
    } else {
      sy_map.insert(map<int, int>::value_type(terminals[i], temp_it->index));
    }
  }

  return sy_map;
};

int GcellGlobalRouter::PrimeSetGenerate(std::vector<std::vector<int> > &connectedTiles, std::vector<std::vector<int> > &sy_connectedTiles,
                                        std::map<int, int> &net_map, std::map<int, int> &sy_net_map) {
  int unmap_flag = 0;

  for (unsigned int i = 0; i < connectedTiles.size(); ++i) {
    std::set<int> temp_sy_set;
    std::set<int> sy_set;
    std::vector<int> sy_prime;
    std::vector<int> prime;

    for (unsigned int j = 0; j < connectedTiles[i].size(); ++j) {
      temp_sy_set.insert(net_map[connectedTiles[i][j]]);
    }
    for (unsigned int j = 0; j < sy_connectedTiles[i].size(); ++j) {
      if (temp_sy_set.find(sy_connectedTiles[i][j]) != temp_sy_set.end()) {
        sy_prime.push_back(sy_connectedTiles[i][j]);
      }
    }

    for (unsigned int j = 0; j < sy_prime.size(); ++j) {
      sy_set.insert(sy_net_map[sy_prime[j]]);
    }
    for (unsigned int j = 0; j < connectedTiles[i].size(); ++j) {
      if (sy_set.find(connectedTiles[i][j]) != sy_set.end()) {
        prime.push_back(connectedTiles[i][j]);
      }
    }

    if (sy_prime.size() != 0 && prime.size() != 0) {
      connectedTiles[i] = prime;
      sy_connectedTiles[i] = sy_prime;
    } else {
      unmap_flag = 1;
    }
  }

  if (unmap_flag == 0) {
    return 1;
  } else {
    return 0;
  }
};

void GcellGlobalRouter::Update_terminals(RouterDB::Net &temp_net) {
  std::set<int> temp_set;
  std::vector<int> temp_terminals;

  for (unsigned int i = 0; i < temp_net.connectedTile.size(); ++i) {
    for (unsigned int j = 0; j < temp_net.connectedTile[i].size(); ++j) {
      temp_set.insert(temp_net.connectedTile[i][j]);
    }
  }

  std::set<int>::iterator it, it_low, it_up;

  it_low = temp_set.begin();
  it_up = temp_set.end();

  for (it = it_low; it != it_up; ++it) {
    temp_terminals.push_back(*it);
  }

  temp_net.terminals = temp_terminals;
};

void GcellGlobalRouter::transformCenter(bool H, int &center, GlobalGrid &grid) {
  int dist = INT_MAX;
  int index = -1;

  for (unsigned int i = 0; i < grid.tiles_total.size(); ++i) {
    if (H) {
      // y
      if (abs(center - grid.tiles_total[i].y) < dist) {
        dist = abs(center - grid.tiles_total[i].y);
        index = i;
      }
    } else {
      // x
      if (abs(center - grid.tiles_total[i].x) < dist) {
        dist = abs(center - grid.tiles_total[i].x);
        index = i;
      }
    }
  }
  if (index >= 0 && index < int(grid.tiles_total.size())) {
    if (H) {
      center = grid.tiles_total[index].y;
    } else {
      center = grid.tiles_total[index].x;
    }
  }
};

void GcellGlobalRouter::SymNet(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set) {
  for (unsigned int i = 0; i < this->Nets.size(); ++i) {
    if (this->Nets.at(i).symCounterpart != -1 && this->Nets.at(i).symCounterpart < (int)this->Nets.size() - 1) {
      int symCounterpart = this->Nets.at(i).symCounterpart;

      bool H = this->Nets.at(i).sym_H;
      int center = this->Nets.at(i).center;
      this->Nets.at(i).global_center = center;
      transformCenter(H, this->Nets.at(i).global_center, grid);

      int prime_flag = SymNetTerminal_PrimeSet(grid, Tile_Set, this->Nets.at(i), this->Nets.at(symCounterpart), H, center);

      if (prime_flag) {
        this->Nets.at(i).global_sym = symCounterpart;
        this->Nets.at(symCounterpart).global_sym = i;
      }
    }
  }
};

int GcellGlobalRouter::SymNetTerminal_PrimeSet(GlobalGrid &grid, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, RouterDB::Net &temp_net,
                                               RouterDB::Net &sym_net, bool H, int center) {  // H is 1 (y), then V (x)

  // sym
  // std::vector<std::pair<int,int> > sym_pair_net;
  // std::pair sym_temp_pair;

  if (temp_net.connectedTile.size() == sym_net.connectedTile.size()) {
    // create sy point
    // create prime set

    std::map<int, int> net_sy_map;
    std::map<int, int> sym_sy_map;

    net_sy_map = GenerateSymMap(grid, Tile_Set, temp_net.terminals, H, center);
    sym_sy_map = GenerateSymMap(grid, Tile_Set, sym_net.terminals, H, center);

    int prime_flag = PrimeSetGenerate(temp_net.connectedTile, sym_net.connectedTile, net_sy_map, sym_sy_map);

    Update_terminals(temp_net);
    Update_terminals(sym_net);

    if (prime_flag == 1) {
      return 1;
    } else {
      return 0;
    }

  } else {
    return 0;
  }
};

std::vector<int> GcellGlobalRouter::Get_Potential_Steiner_node(std::vector<int> t, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set, GlobalGrid &grid) {
  std::vector<RouterDB::tile> Temp_tile;
  for (unsigned int i = 0; i < t.size(); ++i) {
    for (unsigned int j = 0; j < t.size(); ++j) {
      if (i != j) {
        RouterDB::tile temp_tile;
        temp_tile = grid.tiles_total[t[i]];
        temp_tile.y = grid.tiles_total[t[j]].y;
        Temp_tile.push_back(temp_tile);
        temp_tile.y = grid.tiles_total[t[i]].y;
        temp_tile.x = grid.tiles_total[t[j]].x;
        Temp_tile.push_back(temp_tile);

        temp_tile = grid.tiles_total[t[j]];
        temp_tile.y = grid.tiles_total[t[i]].y;
        Temp_tile.push_back(temp_tile);
        temp_tile.y = grid.tiles_total[t[j]].y;
        temp_tile.x = grid.tiles_total[t[i]].x;
        Temp_tile.push_back(temp_tile);
      }
    }
  }

  std::set<int> stiner_node_set;
  std::set<int>::iterator it_stiner, it_low, it_up;

  std::set<RouterDB::tile, RouterDB::tileComp>::iterator it;

  for (unsigned int i = 0; i < Temp_tile.size(); ++i) {
    it = Tile_Set.find(Temp_tile[i]);
    if (it != Tile_Set.end()) {
      stiner_node_set.insert(it->index);
    }
  }

  std::vector<int> stiner_node;

  it_low = stiner_node_set.begin();
  it_up = stiner_node_set.end();

  for (it_stiner = it_low; it_stiner != it_up; ++it_stiner) {
    stiner_node.push_back(*it_stiner);
  }

  return stiner_node;
};

std::set<RouterDB::tile, RouterDB::tileComp> GcellGlobalRouter::CreateTileSet(GlobalGrid &grid) {
  std::set<RouterDB::tile, RouterDB::tileComp> Tile_set;

  for (unsigned int i = 0; i < grid.tiles_total.size(); ++i) {
    Tile_set.insert(grid.tiles_total[i]);
  }

  return Tile_set;
};

// added by wbxu
void GcellGlobalRouter::placeTerminals() {
  // Limitation: assume that only 1 terminal for each net
  // bool mark;
  int mj;
  for (unsigned int i = 0; i < this->Nets.size(); ++i) {
    this->Nets.at(i).isTerminal = false;
    bool mark = false;
    for (unsigned int j = 0; j < this->Nets.at(i).connected.size(); ++j) {
      if (this->Nets.at(i).connected.at(j).type == RouterDB::TERMINAL) {
        mj = j;
        mark = true;
        break;
      }
    }
    if (mark) {
      if (!this->terminal_routing) {
        this->Nets.at(i).connected.erase(this->Nets.at(i).connected.begin() + mj);
        this->Nets.at(i).degree--;
      }
      this->Nets.at(i).isTerminal = true;
    }
  }
}

long int GcellGlobalRouter::get_number(string str) {
  long int val = 0;
  for (unsigned int number = 0; number < str.length(); ++number) {
    if (isdigit(str[number])) val = (10 * val) + (str[number] - 48);
  }
  return val;
};

void GcellGlobalRouter::getData(PnRDB::hierNode &node, int Lmetal, int Hmetal) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.getData");

  // logger->debug("Router-Info: begin to import data");
  // this->isTop = node.isTop;
  this->isTop = node.isTop;
  this->topName = node.name;
  this->width = node.width;
  this->height = node.height;
  this->LL.x = node.LL.x;
  this->LL.y = node.LL.y;
  this->UR.x = node.UR.x;
  this->UR.y = node.UR.y;
  this->path_number = 5;  // number of candidates
  int max_width = node.width;
  int max_height = node.height;
  // int threshold = 10000000;
  lowest_metal = Lmetal;
  highest_metal = Hmetal;

  if (max_height * max_width <= 100000000) {
    grid_scale = 1;
  } else {
    grid_scale = 4;
  }

  // For terminals
  for (unsigned int i = 0; i < node.Terminals.size(); ++i) {
    RouterDB::terminal temp_terminal;
    temp_terminal.netIter = node.Terminals[i].netIter;
    if (1) {
      // logger->debug("Node Terminal {0} termContacts size {1}", node.Terminals[i].name, node.Terminals[i].termContacts.size());
      for (unsigned int j = 0; j < node.Terminals[i].termContacts.size(); ++j) {
        RouterDB::contact temp_contact;

        temp_contact.placedCenter.x = node.Terminals[i].termContacts[j].placedCenter.x;
        temp_contact.placedCenter.y = node.Terminals[i].termContacts[j].placedCenter.y;
        temp_contact.metal = -1;
        temp_terminal.termContacts.push_back(temp_contact);
      }
    }
    temp_terminal.name = node.Terminals[i].name;
    Terminals.push_back(temp_terminal);
  }

  int temp_type;
  for (unsigned int i = 0; i < node.Nets.size(); ++i) {
    RouterDB::Net temp_net;

    temp_net.degree = node.Nets[i].degree;
    temp_net.netName = node.Nets[i].name;
    temp_net.shielding = node.Nets[i].shielding;
    temp_net.sink2Terminal = node.Nets[i].sink2Terminal;
    temp_net.symCounterpart = node.Nets[i].symCounterpart;
    temp_net.iter2SNetLsit = node.Nets[i].iter2SNetLsit;
    temp_net.priority = node.Nets[i].priority;
    temp_net.multi_connection = node.Nets[i].multi_connection;

    if (node.Nets[i].axis_dir == PnRDB::H) {
      temp_net.sym_H = 1;
    } else if (node.Nets[i].axis_dir == PnRDB::V) {
      temp_net.sym_H = 0;
    }
    temp_net.center = node.Nets[i].axis_coor;

    for (unsigned int j = 0; j < node.Nets[i].connected.size(); ++j) {
      RouterDB::connectNode temp_connectNode;
      temp_type = RouterDB::NType(node.Nets[i].connected[j].type);  // wbxu? Not Omark, replace with NType

      if (temp_type == 0) {
        temp_connectNode.type = RouterDB::BLOCK;
      } else {
        temp_connectNode.type = RouterDB::TERMINAL;
        temp_net.isTerminal = 1;
        temp_net.terminal_idx = node.Nets[i].connected[j].iter;
      }
      // assume that at most one terminal connected to one net
      temp_connectNode.iter = node.Nets[i].connected[j].iter;
      temp_connectNode.iter2 = node.Nets[i].connected[j].iter2;
      temp_net.connected.push_back(temp_connectNode);
    }

    for(auto net_name: node.DoNotRoute){
       if(net_name==temp_net.netName){
          temp_net.DoNotRoute = true;
       }
    }

    int global_min = 0;
    int global_max = drc_info.MaxLayer;

    if(!node.Routing_Layers.global_min_layer.empty()){
      global_min = drc_info.Metalmap[node.Routing_Layers.global_min_layer];
    }

    if(!node.Routing_Layers.global_max_layer.empty()){
      global_max = drc_info.Metalmap[node.Routing_Layers.global_max_layer];
    }

    temp_net.min_routing_layer = global_min;
    temp_net.max_routing_layer = global_max;

    for(auto routing_layers: node.Routing_Layers.Routing_per_Net){
      if(routing_layers.net_name==temp_net.netName){
        int min_layer = std::max(global_min,drc_info.Metalmap[routing_layers.net_min_layer]);
        int max_layer = std::max(global_max,drc_info.Metalmap[routing_layers.net_max_layer]);
        temp_net.min_routing_layer = min_layer;
        temp_net.max_routing_layer = max_layer;
      }
    }

    Nets.push_back(temp_net);
  }

  // For RC const
  for (unsigned int i = 0; i < node.R_Constraints.size(); ++i) {
    for (unsigned int j = 0; j < Nets.size(); ++j) {
      if (node.R_Constraints[i].net_name == Nets[j].netName) {
        RouterDB::R_const temp_const;
        temp_const.start_pin = node.R_Constraints[i].start_pin;
        temp_const.end_pin = node.R_Constraints[i].end_pin;
        temp_const.R = node.R_Constraints[i].R;
        Nets[j].R_constraints.push_back(temp_const);
      }
    }
  }

  for (unsigned int i = 0; i < node.C_Constraints.size(); ++i) {
    for (unsigned int j = 0; j < Nets.size(); ++j) {
      if (node.C_Constraints[i].net_name == Nets[j].netName) {
        RouterDB::C_const temp_const;
        temp_const.start_pin = node.C_Constraints[i].start_pin;
        temp_const.end_pin = node.C_Constraints[i].end_pin;
        temp_const.C = node.C_Constraints[i].C;
        Nets[j].C_constraints.push_back(temp_const);
      }
    }
  }

  // For blocks
  for (unsigned int i = 0; i < node.Blocks.size(); ++i) {
    RouterDB::Block temp_block;
    int slcNumber = node.Blocks[i].selectedInstance;
    temp_block.blockName = node.Blocks[i].instance[slcNumber].name;
    temp_block.blockMaster = node.Blocks[i].instance[slcNumber].master;
    temp_block.gdsfile = node.Blocks[i].instance[slcNumber].gdsFile;
    temp_block.numTerminals = node.Blocks[i].instance[slcNumber].blockPins.size();
    temp_block.orient = RouterDB::Omark(node.Blocks[i].instance[slcNumber].orient);
    temp_block.isLeaf = node.Blocks[i].instance[slcNumber].isLeaf;
    temp_block.width = node.Blocks[i].instance[slcNumber].width;
    temp_block.height = node.Blocks[i].instance[slcNumber].height;
    temp_block.area = temp_block.width * temp_block.height;
    temp_block.placedLL.x = node.Blocks[i].instance[slcNumber].placedBox.LL.x;
    temp_block.placedLL.y = node.Blocks[i].instance[slcNumber].placedBox.LL.y;
    temp_block.placedUR.x = node.Blocks[i].instance[slcNumber].placedBox.UR.x;
    temp_block.placedUR.y = node.Blocks[i].instance[slcNumber].placedBox.UR.y;

    for (unsigned int j = 0; j < node.Blocks[i].instance[slcNumber].blockPins.size(); ++j) {
      RouterDB::Pin temp_pin;
      temp_pin.pinName = node.Blocks[i].instance[slcNumber].blockPins[j].name;
      temp_pin.netIter = node.Blocks[i].instance[slcNumber].blockPins[j].netIter;
      for (unsigned int k = 0; k < node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts.size(); ++k) {
        RouterDB::contact temp_contact;
        if (drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].metal) != drc_info.Metalmap.end()) {
          temp_contact.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k].metal];
        } else {
          logger->debug("Router-Error: the metal pin contact of block is not found");
        }
        AssignContact(temp_contact, node.Blocks[i].instance[slcNumber].blockPins[j].pinContacts[k]);
        temp_pin.pinContacts.push_back(temp_contact);
      }

      for (unsigned int k = 0; k < node.Blocks[i].instance[slcNumber].blockPins[j].pinVias.size(); ++k) {
        RouterDB::Via temp_via;
        temp_via.model_index = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].model_index;
        temp_via.position.x = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].placedpos.x;
        temp_via.position.y = node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].placedpos.y;
        // ViaRect

        if (drc_info.Viamap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.metal) != drc_info.Viamap.end()) {
          temp_via.ViaRect.metal = drc_info.Viamap[node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect.metal];
        } else {
          logger->debug("Router-Error: - Viamap Error");
        }
        AssignContact(temp_via.ViaRect, node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].ViaRect);
        // LowerRect //LowerMetalRect
        if (drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.metal) != drc_info.Metalmap.end()) {
          temp_via.LowerMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect.metal];
        } else {
          logger->debug("Router-Error: Metal map error");
        }
        AssignContact(temp_via.LowerMetalRect, node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].LowerMetalRect);
        // UpperRect //UpperMetalRect
        if (drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.metal) != drc_info.Metalmap.end()) {
          temp_via.UpperMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect.metal];
        } else {
          logger->debug("Router-Error: Metal map error");
        }
        AssignContact(temp_via.UpperMetalRect, node.Blocks[i].instance[slcNumber].blockPins[j].pinVias[k].UpperMetalRect);
        temp_pin.pinVias.push_back(temp_via);
      }

      temp_block.pins.push_back(temp_pin);
    }

    for (unsigned int j = 0; j < node.Blocks[i].instance[slcNumber].interMetals.size(); ++j) {
      RouterDB::contact temp_metal;
      if (drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].interMetals[j].metal) != drc_info.Metalmap.end()) {
        temp_metal.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].interMetals[j].metal];
        // temp_metal.width=drc_info.Metal_info[temp_metal.MetalIdx].width;
      } else {
        logger->debug("Router-Error: interMetal info missing metal");
      }
      RouterDB::point temp_point;
      temp_metal.placedLL.x = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.LL.x;
      temp_metal.placedLL.y = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.LL.y;
      temp_metal.placedUR.x = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.UR.x;
      temp_metal.placedUR.y = node.Blocks[i].instance[slcNumber].interMetals[j].placedBox.UR.y;
      temp_metal.placedCenter.x = (temp_metal.placedLL.x + temp_metal.placedUR.x) / 2;
      temp_metal.placedCenter.y = (temp_metal.placedLL.y + temp_metal.placedUR.y) / 2;
      temp_block.InternalMetal.push_back(temp_metal);
    }

    for (unsigned int j = 0; j < node.Blocks[i].instance[slcNumber].interVias.size(); ++j) {
      RouterDB::Via temp_via;
      temp_via.model_index = node.Blocks[i].instance[slcNumber].interVias[j].model_index;
      temp_via.position.x = node.Blocks[i].instance[slcNumber].interVias[j].placedpos.x;
      temp_via.position.y = node.Blocks[i].instance[slcNumber].interVias[j].placedpos.y;
      // ViaRect

      if (drc_info.Viamap.find(node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.metal) != drc_info.Metalmap.end()) {
        temp_via.ViaRect.metal = drc_info.Viamap[node.Blocks[i].instance[slcNumber].interVias[j].ViaRect.metal];
      } else {
        logger->debug("Router-Error: - Viamap Error");
      }
      AssignContact(temp_via.ViaRect, node.Blocks[i].instance[slcNumber].interVias[j].ViaRect);
      // LowerRect //LowerMetalRect
      if (drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.metal) != drc_info.Metalmap.end()) {
        temp_via.LowerMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect.metal];
      } else {
        logger->debug("Router-Error: Metal map error");
      }
      AssignContact(temp_via.LowerMetalRect, node.Blocks[i].instance[slcNumber].interVias[j].LowerMetalRect);
      // UpperRect //UpperMetalRect
      if (drc_info.Metalmap.find(node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.metal) != drc_info.Metalmap.end()) {
        temp_via.UpperMetalRect.metal = drc_info.Metalmap[node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect.metal];
      } else {
        logger->debug("Router-Error: Metal map error");
      }
      AssignContact(temp_via.UpperMetalRect, node.Blocks[i].instance[slcNumber].interVias[j].UpperMetalRect);

      temp_block.InternalVia.push_back(temp_via);
    }
    Blocks.push_back(temp_block);
  }
  for (std::vector<PnRDB::PowerNet>::iterator nit = node.PowerNets.begin(); nit != node.PowerNets.end(); ++nit) {
    RouterDB::PowerNet temp_power_net;
    temp_power_net.netName = nit->name;
    temp_power_net.power = nit->power;
    for (std::vector<PnRDB::pin>::iterator pit = nit->Pins.begin(); pit != nit->Pins.end(); ++pit) {
      RouterDB::Pin temp_pin;
      temp_pin.pinName = pit->name;
      temp_pin.netIter = pit->netIter;
      for (std::vector<PnRDB::contact>::iterator cit = pit->pinContacts.begin(); cit != pit->pinContacts.end(); ++cit) {
        RouterDB::contact temp_contact;
        temp_contact.metal = drc_info.Metalmap[cit->metal];
        AssignContact(temp_contact, *cit);
        temp_pin.pinContacts.push_back(temp_contact);
      }
      for (std::vector<PnRDB::Via>::iterator vit = pit->pinVias.begin(); vit != pit->pinVias.end(); ++vit) {
        RouterDB::Via temp_via;
        temp_via.model_index = vit->model_index;
        AssignContact(temp_via.ViaRect, vit->ViaRect);
        AssignContact(temp_via.LowerMetalRect, vit->LowerMetalRect);
        AssignContact(temp_via.UpperMetalRect, vit->UpperMetalRect);
        temp_pin.pinVias.push_back(temp_via);
      }
      temp_power_net.pins.push_back(temp_pin);
    }
    for (std::vector<PnRDB::Metal>::iterator mit = nit->path_metal.begin(); mit != nit->path_metal.end(); ++mit) {
      RouterDB::Metal temp_metal;
      CopyMetal(temp_metal, *mit);
      temp_power_net.path_metal.push_back(temp_metal);
    }
    for (std::vector<PnRDB::Via>::iterator vit = nit->path_via.begin(); vit != nit->path_via.end(); ++vit) {
      RouterDB::Via temp_via;
      temp_via.model_index = vit->model_index;
      AssignContact(temp_via.ViaRect, vit->ViaRect);
      AssignContact(temp_via.LowerMetalRect, vit->LowerMetalRect);
      AssignContact(temp_via.UpperMetalRect, vit->UpperMetalRect);
      temp_power_net.path_via.push_back(temp_via);
    }
    for(auto net_name: node.DoNotRoute){
       if(net_name==temp_power_net.netName){
          temp_power_net.DoNotRoute = true;
       }
    }
    PowerNets.push_back(temp_power_net);
  }
  // logger->debug("Router-Info: complete importing data");
};

void GcellGlobalRouter::CopyMetal(RouterDB::Metal &RouterDB_metal, PnRDB::Metal &PnRDB_metal) {
  RouterDB_metal.MetalIdx = PnRDB_metal.MetalIdx;
  RouterDB_metal.width = PnRDB_metal.width;
  AssignContact(RouterDB_metal.MetalRect, PnRDB_metal.MetalRect);
  for (std::vector<PnRDB::point>::iterator pit = PnRDB_metal.LinePoint.begin(); pit != PnRDB_metal.LinePoint.end(); ++pit) {
    RouterDB::point temp_point(pit->x, pit->y);
    RouterDB_metal.LinePoint.push_back(temp_point);
  }
}

void GcellGlobalRouter::AssignContact(RouterDB::contact &RouterDB_contact, PnRDB::contact &PnRDB_contact) {
  RouterDB_contact.placedLL.x = PnRDB_contact.placedBox.LL.x;
  RouterDB_contact.placedLL.y = PnRDB_contact.placedBox.LL.y;
  RouterDB_contact.placedUR.x = PnRDB_contact.placedBox.UR.x;
  RouterDB_contact.placedUR.y = PnRDB_contact.placedBox.UR.y;
  RouterDB_contact.placedCenter.x = PnRDB_contact.placedCenter.x;
  RouterDB_contact.placedCenter.y = PnRDB_contact.placedCenter.y;
  RouterDB_contact.originCenter.x = PnRDB_contact.originCenter.x;
  RouterDB_contact.originCenter.y = PnRDB_contact.originCenter.y;
  RouterDB_contact.originLL.x = PnRDB_contact.originBox.LL.x;
  RouterDB_contact.originLL.y = PnRDB_contact.originBox.LL.y;
  RouterDB_contact.originUR.x = PnRDB_contact.originBox.UR.x;
  RouterDB_contact.originUR.y = PnRDB_contact.originBox.UR.y;
};

void GcellGlobalRouter::getDRCdata(PnRDB::Drc_info &drcData) {

 drc_info = drcData; 
 cross_layer_drc_info = drcData;
};

int GcellGlobalRouter::CopyPath(std::vector<std::pair<int, int> > &path, std::map<int, int> &temp_map, std::vector<std::pair<int, int> > &sy_path) {
  // std::vector<std::pair<int,int> > sy_path;
  std::pair<int, int> temp_path;
  for (unsigned int i = 0; i < path.size(); ++i) {
    if (temp_map.find(path[i].first) != temp_map.end() && temp_map[path[i].first] != -1) {
      temp_path.first = temp_map[path[i].first];
    } else {
      return 0;
    }

    if (temp_map.find(path[i].second) != temp_map.end() && temp_map[path[i].second] != -1) {
      temp_path.second = temp_map[path[i].second];
    } else {
      return 0;
    }

    sy_path.push_back(temp_path);
  }

  return 1;
};

int GcellGlobalRouter::JudgeSymmetry(std::vector<std::pair<int, int> > &path, std::vector<std::pair<int, int> > &sy_path, std::map<int, int> &sy_map) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.JudgeSymmetry");

  // map the path
  std::vector<std::pair<int, int> > map_path;
  std::pair<int, int> temp_path;

  for (unsigned int i = 0; i < path.size(); ++i) {
    if (sy_map.find(path[i].first) == sy_map.end()) {
      logger->debug("SY map Error");
    } else {
      temp_path.first = sy_map[path[i].first];
    }

    if (sy_map.find(path[i].second) == sy_map.end()) {
      logger->debug("SY map Error");
    } else {
      temp_path.second = sy_map[path[i].second];
    }

    if (temp_path.first == -1 || temp_path.second == -1) {
      return 0;
    } else {
      map_path.push_back(temp_path);
    }
  }

  std::set<std::pair<int, int>, RouterDB::pairComp> map_path_set;
  std::set<std::pair<int, int>, RouterDB::pairComp> sy_path_set;

  std::pair<int, int> temp_pair;

  for (unsigned int i = 0; i < map_path.size(); ++i) {
    if (map_path[i].first < map_path[i].second) {
      temp_pair = map_path[i];
      map_path_set.insert(temp_pair);
    } else {
      temp_pair.first = map_path[i].second;
      temp_pair.second = map_path[i].first;
      map_path_set.insert(temp_pair);
    }
  }

  for (unsigned int i = 0; i < sy_path.size(); ++i) {
    if (sy_path[i].first < sy_path[i].second) {
      temp_pair = sy_path[i];
      sy_path_set.insert(temp_pair);
    } else {
      temp_pair.first = sy_path[i].second;
      temp_pair.second = sy_path[i].first;
      sy_path_set.insert(temp_pair);
    }
  }

  if (map_path_set.size() != sy_path_set.size()) {
    return 0;
  }

  std::set<std::pair<int, int> >::iterator map_it, sy_it;

  for (map_it = map_path_set.begin(), sy_it = sy_path_set.begin(); map_it != map_path_set.end(); ++map_it, ++sy_it) {
    if (*map_it != *sy_it) {
      return 0;
    }
  }

  return 1;
};

void GcellGlobalRouter::lpsolve_logger(lprec *lp, void *userhandle, char *buf) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.lpsolve_logger");

  // Strip leading newline
  while ((unsigned char)*buf == '\n') buf++;
  // Log non-empty lines
  if (*buf != '\0') logger->debug("GcellGlobalRouter lpsolve: {0}", buf);
}

int GcellGlobalRouter::ILPSolveRouting(GlobalGrid &grid, GlobalGraph &graph, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set) {
  auto logger = spdlog::default_logger()->clone("router.GcellGlobalRouter.ILPSolveRouting");

  // logger->debug("Status Log: ILP Solving Starts");


#if defined ERROR
#undef ERROR
#endif
#define ERROR() \
  { logger->error("Error"); }
  // logger->debug("LP test flag 1");
  // start of lp_solve
  // int majorversion, minorversion, release, build;
  // char buf[1024];

  /*
  hlpsolve lpsolve;
  # if defined WIN32
  #   define lpsolvelib "lpsolve55.dll"
  # else
  #   define lpsolvelib "liblpsolve55.so"
  # endif
  lpsolve = open_lpsolve_lib(const_cast<char*>(lpsolvelib));
  if (lpsolve == NULL) {
    fprintf(stderr, "Unable to load lpsolve shared library (%s).\nIt is probably not in the correct path.\n", lpsolvelib);
    //ERROR();
  }

  if (!init_lpsolve(lpsolve)) {
    fprintf(stderr, "Unable to initialize lpsolve shared library (%s)\n      ", lpsolvelib);
    //ERROR();
  }
  */

  // 1. collect number of STs
  int NumberOfSTs = 0;
  int NumberOfNets = 0;
  valInfo vi;
  // logger->debug("LP test flag 2");
  for (unsigned int h = 0; h < this->Nets.size(); ++h) {  //  for each net
    vi.netIter = h;
    for (unsigned int i = 0; i < this->Nets[h].STs.size(); ++i) {  // for each segment
      vi.STIter = i;
      vi.candIter = -1;
      vi.segIter = -1;
      vi.valIter = NumberOfSTs;
      this->Nets[h].STs[i].valIdx = NumberOfSTs;
      NumberOfSTs++;
      ValArray.push_back(vi);
    }
    NumberOfNets++;
  }
  // logger->debug("TotNumberOfNest {0} {1}", NumberOfNets, NumberOfSTs);
  this->NumOfVar = NumberOfSTs;  //#Variable initialization


  if ((lp = make_lp(0, NumOfVar + 1)) == NULL) {
    logger->error("Error");
  }  // ERROR();}
  // lp_solve_version(&majorversion, &minorversion, &release, &build);
  // sprintf(buf, "lp_solve %d.%d.%d.%d demo\n\n", majorversion, minorversion, release, build);//lp_solve 5.5.2.0
  // print_str(lp, buf);
  // put_logfunc(lp, NULL, 0);
  // set_outputfile(lp, const_cast<char*>("./Debug/lp_solve_result.txt"));
  set_verbose(lp, IMPORTANT);
  put_logfunc(lp, &GcellGlobalRouter::lpsolve_logger, NULL);
  set_outputfile(lp, const_cast<char *>("/dev/null"));
  // set_add_rowmode(lp, TRUE);
  // 2. Initialize matrix without constraints  Q1? A 0 is inserted to the temp_row, so the valInfo maybe not correct

  // std::cout<<"testcase 1"<<std::endl;


  // int CurNet = 0;
  // logger->debug("LP test flag 3");
  for (int i = 0; i < NumberOfNets; ++i) {
    int CurNet = i;
    // std::vector<double> temp_row;
    // temp_row.push_back(0);//0th column "0" Q2?
    std::vector<double> temp_row;
    std::vector<int> temp_index;
    for (unsigned int j = 0; j < this->Nets.size(); ++j) {
      for (unsigned int k = 0; k < this->Nets.at(j).STs.size(); ++k) {
        /*
                    if((int)j==CurNet) {
                        temp_row.push_back(1);
                       } else {
                        temp_row.push_back(0);
                       }
        */

        if ((int)j == CurNet) {
          temp_index.push_back(this->Nets.at(j).STs[k].valIdx + 1);
          temp_row.push_back(1);
        }
      }
    }

    // temp_row.push_back(0);
    if(temp_row.size()==0) continue;
    double *row = &temp_row[0];
    int *col = &temp_index[0];
    int size_element = temp_row.size();
    // if (!add_constraint(lp, row, EQ, 1)) {std::cerr << "Error" << std::endl;} //ERROR();}

    if (!add_constraintex(lp, size_element, row, col, EQ, 1)) {
      logger->error("Error");
    }  // ERROR();}
  }


  // symmetry problem
  // logger->debug("LP test flag 4");
  for (unsigned int i = 0; i < this->Nets.size(); ++i) {
    if (this->Nets.at(i).global_sym != -1 && this->Nets.at(i).global_sym < (int)this->Nets.size() - 1) {
      int global_sym = this->Nets.at(i).global_sym;
      for (unsigned int j = 0; j < this->Nets.at(i).STs.size(); ++j) {
        // std::vector<double> temp_row;
        // temp_row.push_back(0);//0th column "0" Q2?
        std::vector<double> temp_row;
        std::vector<int> temp_index;
        /*
                       for(int val_number = 0; val_number < NumberOfSTs ; ++val_number){
                              if(val_number == this->Nets.at(global_sym).STs[j].valIdx){
                                   temp_row.push_back(1);
                                }else if(val_number == this->Nets.at(i).STs[j].valIdx){
                                   temp_row.push_back(-1);
                                }else{
                                   temp_row.push_back(0);
                                }

                            }
        */

        for (int val_number = 0; val_number < NumberOfSTs; ++val_number) {
          if (val_number == this->Nets.at(global_sym).STs[j].valIdx) {
            temp_index.push_back(this->Nets.at(global_sym).STs[j].valIdx + 1);
            temp_row.push_back(1);
          } else if (val_number == this->Nets.at(i).STs[j].valIdx) {
            temp_index.push_back(this->Nets.at(i).STs[j].valIdx + 1);
            temp_row.push_back(-1);
          }
        }

        // temp_row.push_back(0);
        double *row = &temp_row[0];
        int *col = &temp_index[0];
        int size_element = temp_row.size();
        // logger->debug("Adding SYM constraints");
        // if (!add_constraint(lp, row, EQ, 0)) {std::cout << "Error" << std::endl;} //ERROR();}
        if (!add_constraintex(lp, size_element, row, col, EQ, 0)) {
          logger->error("Error");
        }  // ERROR();}
      }
    }
  }



  // CalCulated_Sym_Ax(this->Nets[i].terminals,this->Nets[j].terminals, center_x, center_y, H_or_V); //H_or_V is H if 1, else V (0);
  // 1. Based on real pin determine the center terminal position or the coordinate of ;
  // 2. Based on the STs calclated the co

  // capacity edge constraint
  // Q4?

  // std::cout<<"testcase 2"<<std::endl;

  std::vector<std::pair<int, int> > Edges;
  std::vector<int> Capacities;
  std::vector<std::vector<int> > Edges_To_Var;

  NumberOfSTs = 0;
  // logger->debug("LP test flag 5");
  for (unsigned int i = 0; i < this->Nets.size(); ++i) {
    for (unsigned int j = 0; j < this->Nets.at(i).STs.size(); ++j) {
      NumberOfSTs++;
      for (unsigned int k = 0; k < this->Nets.at(i).STs[j].path.size(); ++k) {
        int found = 0;
        int index = -1;
        for (unsigned int l = 0; l < Edges.size(); ++l) {
          if ((this->Nets.at(i).STs[j].path[k].first == Edges[l].first && this->Nets.at(i).STs[j].path[k].second == Edges[l].second) ||
              (this->Nets.at(i).STs[j].path[k].first == Edges[l].second && this->Nets.at(i).STs[j].path[k].second == Edges[l].first)) {
            found = 1;
            index = l;
            break;
          }
        }

        if (found == 1) {
          // std::cout<<"Break down"<<std::endl;
          Edges_To_Var[index].push_back(NumberOfSTs);  // push_back the var number??

        } else {
          for (unsigned int p = 0; p < graph.graph[this->Nets.at(i).STs[j].path[k].first].list.size(); ++p) {
            if (graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].dest == this->Nets.at(i).STs[j].path[k].second) {
              Capacities.push_back(graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].capacity);
              Edges.push_back(this->Nets.at(i).STs[j].path[k]);
              std::vector<int> temp_var;
              Edges_To_Var.push_back(temp_var);

              break;
            }
          }
        }
      }
    }
  }



  // std::cout<<"testcase 3"<<std::endl;
  // logger->debug("LP test flag 6");
  for (unsigned int i = 0; i < Edges_To_Var.size(); ++i) {
    // std::vector<double> temp_row;
    // temp_row.push_back(0);//0th column "0" Q2?

    std::vector<double> temp_row;
    std::vector<int> temp_index;
    /*
           for(int j=0;j<NumberOfSTs;++j){
                int found_flag = 0;
                for(unsigned int k=0;k<Edges_To_Var[i].size();++k){
                    if(Edges_To_Var[i][k]==j){found_flag=1;}
                   }
                if(found_flag==1){
                  temp_row.push_back(1);
                  }else{
                  temp_row.push_back(0);
                  }
              }
    */

    for (int j = 0; j < NumberOfSTs; ++j) {
      int found_flag = 0;
      for (unsigned int k = 0; k < Edges_To_Var[i].size(); ++k) {
        if (Edges_To_Var[i][k] == j) {
          found_flag = 1;
        }
      }
      if (found_flag == 1) {
        temp_index.push_back(j + 1);
        temp_row.push_back(1);
      }
    }
    temp_index.push_back(NumberOfSTs + 1);
    temp_row.push_back(-Capacities[i]);
    // logger->debug("Constraint Capacity {0}", Capacities[i]);

    double *row = &temp_row[0];
    int *col = &temp_index[0];
    int size_element = temp_row.size();
    // if (!add_constraint(lp, row, LE, 0)) {std::cerr << "Error" << std::endl;} //ERROR();}
    if (!add_constraintex(lp, size_element, row, col, LE, 0)) {
      logger->error("Error");
    }  // ERROR();}
  }


  // std::cout<<"testcase 4"<<std::endl;

  // print_lp(lp);
  // 4. Set binary variables (candidates + slacks)
  for (int i = 1; i <= this->NumOfVar; ++i) {
    set_binary(lp, i, TRUE);  //"TRUE": set variable to be a binary. upper bound=1, lower bound=0
  }


  set_bounds(lp, this->NumOfVar + 1, 0.0, 1.0);
  // printf("Set the objective function\n");
  // printf("set_obj_fn(lp, {nets[h].seg[i].candis[j].TotMetalWeightByLength})\n");

  // 5. Set objective function
  vector<double> temp_row;
  vector<int> temp_index;
  // temp_row.push_back(NumOfVar+1);
  /*
    for(int i=0;i<this->NumOfVar;++i){
       temp_row.push_back(0);
    }
  */

  temp_row.push_back(1);
  temp_index.push_back(NumOfVar + 1);


  double *row = &temp_row[0];
  int *col = &temp_index[0];
  if (!set_obj_fnex(lp, 1, row, col)) {
    logger->error("Router-Error: Objective insertion Error");
  }


  // std::cout<<"testcase 5"<<std::endl;
  // logger->debug("LP test flag 7");
  // 6. Solve with lp
  set_minim(lp);
  set_timeout(lp, 60);
  // logger->debug("LP test flag 8");
  // set_solutionlimit(lp, 10);
  // logger->debug("LP test flag 9");
  set_presolve(lp, PRESOLVE_PROBEFIX | PRESOLVE_ROWDOMINATE, get_presolveloops(lp));
  // logger->debug("LP test flag 10");
  // print_lp(lp);

  int ret = solve(lp);
  // logger->debug("LP test flag 11");
  if (ret == 0) {
    logger->debug("Status Log: Optimal Solution Found Success");
  } else if (ret == 2) {
    logger->debug("Status Log: Model is Infeasible");
  } else if (ret == 1) {
    logger->debug("Status Log: Suboptimal Solution Found");
  } else if (ret == -2) {
    logger->debug("Status Log: Out of memory");
  } else if (ret == 7) {
    logger->debug("Status Log: Timeout(set via set_timeout)");
  } else {
    logger->debug("Status Log: Refer Function solve in lp_solve(http://lpsolve.sourceforge.net/5.5/)");
  }
  // logger->debug("LP test flag 12");
  // logger->debug("#Constraints: lp row: {0}", lp->rows);
  // logger->debug("#Variables: lp col:  {0}", lp->columns);
  // logger->debug("LP test flag 13");
  // 7. Get results and store back to data structure
  // Q5?


  double Vars[NumOfVar];
  get_variables(lp, Vars);
  // logger->debug("LP test flag 14");
  // std::cout<<"testcase 6"<<std::endl;
  for (int i = 0; i < NumOfVar; ++i) {
    if (Vars[i] == 1) {
      this->Nets.at(ValArray[i].netIter).STindex = ValArray[i].STIter;
    }
  }


  // std::cout<<"testcase 7"<<std::endl;
  // set_add_rowmode(lp, FALSE);
  // free(row);
  // free(col);
  // logger->debug("LP test flag 15");
  delete_lp(lp);
  // logger->debug("LP test flag 16");
  return ret;
}

/*
int GcellGlobalRouter::ILPSolveRouting(GlobalGrid &grid, GlobalGraph &graph, std::set<RouterDB::tile, RouterDB::tileComp> &Tile_Set) {
  std::cout<< "Status Log: ILP Solving Starts"<<std::endl;
  # if defined ERROR
  #  undef ERROR
  # endif
  //# define ERROR() { std::cerr << "Error" << std::endl; return(1); }
  # define ERROR() { std::cerr << "Error" << std::endl; }

  // start of lp_solve
  int majorversion, minorversion, release, build;
  char buf[1024];
  hlpsolve lpsolve;
  # if defined WIN32
  #   define lpsolvelib "lpsolve55.dll"
  # else
  #   define lpsolvelib "liblpsolve55.so"
  # endif
  lpsolve = open_lpsolve_lib(const_cast<char*>(lpsolvelib));
  if (lpsolve == NULL) {
    fprintf(stderr, "Unable to load lpsolve shared library (%s).\nIt is probably not in the correct path.\n", lpsolvelib);
    //ERROR();
  }

  if (!init_lpsolve(lpsolve)) {
    fprintf(stderr, "Unable to initialize lpsolve shared library (%s)\n      ", lpsolvelib);
    //ERROR();
  }


  // 1. collect number of STs
  int NumberOfSTs = 0;
  int NumberOfNets = 0;
  valInfo vi;


  for(unsigned int h=0;h<this->Nets.size();++h) { //  for each net
    vi.netIter=h;
    for(unsigned int i=0;i<this->Nets[h].STs.size();++i) {// for each segment
      vi.STIter=i;
      vi.candIter=-1;
      vi.segIter=-1;
      vi.valIter=NumberOfSTs;
      this->Nets[h].STs[i].valIdx = NumberOfSTs;
      NumberOfSTs++;
      ValArray.push_back(vi);
    }
   NumberOfNets++;
  }
  std::cout<<"TotNumberOfNest "<<NumberOfNets<<" TotNumberOfSTs "<<NumberOfSTs<<std::endl;
  this->NumOfVar=NumberOfSTs;//#Variable initialization

  if ((lp = make_lp(0,NumOfVar+1)) == NULL) {std::cerr << "Error" << std::endl;} //ERROR();}
  lp_solve_version(&majorversion, &minorversion, &release, &build);
  sprintf(buf, "lp_solve %d.%d.%d.%d demo\n\n", majorversion, minorversion, release, build);//lp_solve 5.5.2.0
  print_str(lp, buf);
  put_logfunc(lp, NULL, 0);
  set_outputfile(lp, const_cast<char*>("./Debug/lp_solve_result.txt"));

  // 2. Initialize matrix without constraints  Q1? A 0 is inserted to the temp_row, so the valInfo maybe not correct

  //std::cout<<"testcase 1"<<std::endl;

  //int CurNet = 0;

  for(int i=0;i<NumberOfNets;++i){

      int CurNet = i;
      std::vector<double> temp_row;
      temp_row.push_back(0);//0th column "0" Q2?

      for(unsigned int j=0;j<this->Nets.size();++j){

          for(unsigned int k=0;k<this->Nets.at(j).STs.size();++k){

            if((int)j==CurNet) {
                temp_row.push_back(1);
               } else {
                temp_row.push_back(0);
               }
             }
         }

       temp_row.push_back(0);
       double* row = &temp_row[0];
       if (!add_constraint(lp, row, EQ, 1)) {std::cerr << "Error" << std::endl;} //ERROR();}

     }

  //symmetry problem

  for(unsigned int i=0;i<this->Nets.size();++i){

    if(this->Nets.at(i).global_sym!=-1 && this->Nets.at(i).global_sym < (int)this->Nets.size()-1){
          std::cout<<"net index "<<i<<" global_sym "<< this->Nets.at(i).global_sym<<std::endl;
          int global_sym = this->Nets.at(i).global_sym;
          for(unsigned int j=0;j<this->Nets.at(i).STs.size();++j){

               std::vector<double> temp_row;
               temp_row.push_back(0);//0th column "0" Q2?

               for(int val_number = 0; val_number < NumberOfSTs+1 ; ++val_number){
                      if(val_number == this->Nets.at(global_sym).STs[j].valIdx){
                           temp_row.push_back(1);
                        }else if(val_number == this->Nets.at(i).STs[j].valIdx){
                           temp_row.push_back(-1);
                        }else{
                           temp_row.push_back(0);
                        }

                    }

                double* row = &temp_row[0];
                std::cout<<"Adding SYM constraints"<<std::endl;
                if (!add_constraint(lp, row, EQ, 0)) {std::cerr << "Error" << std::endl;} //ERROR();}

             }

        }

     }

  //CalCulated_Sym_Ax(this->Nets[i].terminals,this->Nets[j].terminals, center_x, center_y, H_or_V); //H_or_V is H if 1, else V (0);
  // 1. Based on real pin determine the center terminal position or the coordinate of ;
  // 2. Based on the STs calclated the co

  //capacity edge constraint
  //Q4?

  //std::cout<<"testcase 2"<<std::endl;

  std::vector<std::pair<int,int> > Edges;
  std::vector<int> Capacities;
  std::vector<std::vector<int> > Edges_To_Var;

  NumberOfSTs = 0;

  for(unsigned int i=0;i<this->Nets.size();++i){
      for(unsigned int j=0;j<this->Nets.at(i).STs.size();++j){
          NumberOfSTs++;
          for(unsigned int k=0;k<this->Nets.at(i).STs[j].path.size();++k){

               int found = 0;
               int index = -1;
               for(unsigned int l=0;l<Edges.size();++l){

                    if((this->Nets.at(i).STs[j].path[k].first == Edges[l].first && this->Nets.at(i).STs[j].path[k].second == Edges[l].second) ||
(this->Nets.at(i).STs[j].path[k].first == Edges[l].second && this->Nets.at(i).STs[j].path[k].second == Edges[l].first ) ){ found = 1; index = l; break;
                      }

                  }

               if(found ==1){
                  //std::cout<<"Break down"<<std::endl;
                  Edges_To_Var[index].push_back(NumberOfSTs); //push_back the var number??

                 }else{

                  for(unsigned int p = 0;p<graph.graph[this->Nets.at(i).STs[j].path[k].first].list.size();++p){
                       if(graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].dest == this->Nets.at(i).STs[j].path[k].second){
                           Capacities.push_back(graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].capacity);
                           std::cout<<"Edge capacity "<<graph.graph[this->Nets.at(i).STs[j].path[k].first].list[p].capacity<<std::endl;
                           Edges.push_back(this->Nets.at(i).STs[j].path[k]);
                           std::vector<int> temp_var;
                           Edges_To_Var.push_back(temp_var);

                           break;
                         }
                     }
                 }
             }

        }
     }

  //std::cout<<"testcase 3"<<std::endl;


  for(unsigned int i=0;i<Edges_To_Var.size();++i){

      std::vector<double> temp_row;
      temp_row.push_back(0);//0th column "0" Q2?

       for(int j=0;j<NumberOfSTs;++j){
            int found_flag = 0;
            for(unsigned int k=0;k<Edges_To_Var[i].size();++k){
                if(Edges_To_Var[i][k]==j){found_flag=1;}
               }
            if(found_flag==1){
              temp_row.push_back(1);
              }else{
              temp_row.push_back(0);
              }
          }

       temp_row.push_back(-Capacities[i]);
       std::cout<<"Constraint Capacity "<<Capacities[i]<<std::endl;

       double* row = &temp_row[0];
       if (!add_constraint(lp, row, LE, 0)) {std::cerr << "Error" << std::endl;} //ERROR();}

     }

  //std::cout<<"testcase 4"<<std::endl;

  print_lp(lp);
  // 4. Set binary variables (candidates + slacks)
  for(int i=1;i<=this->NumOfVar;++i){
    set_binary(lp, i, TRUE);//"TRUE": set variable to be a binary. upper bound=1, lower bound=0
  }

  set_bounds(lp, this->NumOfVar+1, 0.0, 1.0);

  printf("Set the objective function\n");
  printf("set_obj_fn(lp, {nets[h].seg[i].candis[j].TotMetalWeightByLength})\n");

  // 5. Set objective function
  vector<double> temp_row;
  temp_row.push_back(0);
  for(int i=0;i<this->NumOfVar;++i){
     temp_row.push_back(0);
  }
  temp_row.push_back(1);
  double *row = &temp_row[0];
  if (!set_obj_fn(lp, row)){std::cout <<"Router-Error: Objective insertion Error"<<std::endl;}

  //std::cout<<"testcase 5"<<std::endl;

  // 6. Solve with lp
  set_minim(lp);
  set_timeout(lp,60);
  //set_solutionlimit(lp, 10);
  set_presolve(lp, PRESOLVE_PROBEFIX | PRESOLVE_ROWDOMINATE, get_presolveloops(lp));
  print_lp(lp);

  int ret = solve(lp);
  if(ret== 0){
          std::cout << "Status Log: Optimal Solution Found Success"<<std::endl;
  }
  else if(ret==2){
          std::cout <<"Status Log: Model is Infeasible"<<std::endl;
  }
  else if(ret==1){
          std::cout <<"Status Log: Suboptimal Solution Found"<<std::endl;
  }
  else if(ret==-2){
          std::cout <<"Status Log: Out of memory"<<std::endl;
  }
  else if(ret==7){
          std::cout <<"Status Log: Timeout(set via set_timeout)"<<std::endl;
  }
  else{
          std::cout <<"Status Log: Refer Function solve in lp_solve(http://lpsolve.sourceforge.net/5.5/)"<<std::endl;
  }

  printf("#Constraints: lp row:  %d \n", lp->rows);
  printf("#Variables: lp col:  %d \n", lp->columns);

  // 7. Get results and store back to data structure
  // Q5?
  double Vars[NumOfVar];
  get_variables(lp, Vars);

  //std::cout<<"testcase 6"<<std::endl;
  for(int i=0;i<NumOfVar;++i){
      if(Vars[i]==1){
         this->Nets.at(ValArray[i].netIter).STindex=ValArray[i].STIter;
        }
     }
  //std::cout<<"testcase 7"<<std::endl;
  delete_lp(lp);
  return ret;
}
*/

void CopyTileEdge(const RouterDB::tileEdge &it, PnRDB::tileEdge &ot) {
  ot.next = it.next;
  ot.capacity = it.capacity;
}

void CopyTile(const RouterDB::tile &it, PnRDB::tile &ot) {
  ot.x = it.x;
  ot.y = it.y;
  ot.width = it.width;
  ot.height = it.height;
  ot.metal = it.metal;
  ot.tileLayer = it.tileLayer;
  ot.index = it.index;
  ot.Yidx = it.Yidx;
  ot.Xidx = it.Xidx;
  ot.north.resize(it.north.size());
  for (unsigned i = 0; i < it.north.size(); i++) CopyTileEdge(it.north[i], ot.north[i]);
  ot.south.resize(it.south.size());
  for (unsigned i = 0; i < it.south.size(); i++) CopyTileEdge(it.south[i], ot.south[i]);
  ot.west.resize(it.west.size());
  for (unsigned i = 0; i < it.west.size(); i++) CopyTileEdge(it.west[i], ot.west[i]);
  ot.east.resize(it.east.size());
  for (unsigned i = 0; i < it.east.size(); i++) CopyTileEdge(it.east[i], ot.east[i]);
  ot.down.resize(it.down.size());
  for (unsigned i = 0; i < it.down.size(); i++) CopyTileEdge(it.down[i], ot.down[i]);
  ot.up.resize(it.up.size());
  for (unsigned i = 0; i < it.up.size(); i++) CopyTileEdge(it.up[i], ot.up[i]);
}

void GcellGlobalRouter::ReturnHierNode(PnRDB::hierNode &HierNode) {
  for (unsigned int i = 0; i < Nets.size(); ++i) {
    if(Nets[i].STindex>=0 and Nets[i].STindex<Nets[i].STs.size())
    Nets[i].global_path = Nets[i].STs[Nets[i].STindex].path;
  }

  //    HierNode.tiles_total = Gcell.tiles_total;
  HierNode.tiles_total.resize(Gcell.tiles_total.size());
  for (unsigned i = 0; i < Gcell.tiles_total.size(); i++) CopyTile(Gcell.tiles_total[i], HierNode.tiles_total[i]);

  for (vector<PnRDB::net>::iterator H_NET_it = HierNode.Nets.begin(); H_NET_it != HierNode.Nets.end(); ++H_NET_it) {
    for (vector<RouterDB::Net>::const_iterator NET_it = Nets.begin(); NET_it != Nets.end(); ++NET_it) {
      if (H_NET_it->name != NET_it->netName) {
        continue;
      } else {
        if(NET_it->STindex<0 or NET_it->STindex>=NET_it->STs.size()) continue;
        std::vector<std::pair<int, int> > path = NET_it->STs.at(NET_it->STindex).path;
        H_NET_it->GcellGlobalRouterPath = path;
        H_NET_it->connectedTile = NET_it->connectedTile;
        break;
      }
    }
  }
}
