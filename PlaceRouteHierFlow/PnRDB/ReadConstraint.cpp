#include <fstream>
#include <iomanip>
#include <iostream>

#include "PnRdatabase.h"

using namespace nlohmann;
void PnRdatabase::ReadConstraint_Json(PnRDB::hierNode& node, const string& jsonStr) {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.ReadConstraint_Json");
  json jedb = json::parse(jsonStr);
  json constraints = jedb["constraints"];
  for (auto constraint : constraints) {
    if (constraint["const_name"] == "SymmNet") {
      PnRDB::net tmpnet;
      tmpnet.name = constraint["net1"]["name"];
      for (auto pin : constraint["net1"]["blocks"]) {
        if (pin["type"] == "pin") {  // if block pin
          for (int i = 0; i < (int)node.Blocks.size(); i++) {
            if (node.Blocks.at(i).instance.back().name == pin["name"]) {
              for (int j = 0; j < (int)node.Blocks.at(i).instance.back().blockPins.size(); j++) {
                if (node.Blocks.at(i).instance.back().blockPins.at(j).name == pin["pin"]) {
                  PnRDB::connectNode newnode = {PnRDB::Block, j, i};
                  tmpnet.connected.push_back(newnode);
                  break;
                }
              }
              break;
            }
          }
        } else {  // if terminal
          for (int i = 0; i < (int)node.Terminals.size(); i++) {
            if (node.Terminals.at(i).name == pin["name"]) {
              PnRDB::connectNode newnode = {PnRDB::Terminal, i, -1};
              tmpnet.connected.push_back(newnode);
              break;
            }
          }
        }
      }
      PnRDB::net tmpnet2;
      tmpnet2.name = constraint["net2"]["name"];
      for (auto pin : constraint["net2"]["blocks"]) {
        if (pin["type"] == "pin") {  // if block pin
          for (int i = 0; i < (int)node.Blocks.size(); i++) {
            if (node.Blocks.at(i).instance.back().name == pin["name"]) {
              for (int j = 0; j < (int)node.Blocks.at(i).instance.back().blockPins.size(); j++) {
                if (node.Blocks.at(i).instance.back().blockPins.at(j).name == pin["pin"]) {
                  PnRDB::connectNode newnode = {PnRDB::Block, j, i};
                  tmpnet2.connected.push_back(newnode);
                  break;
                }
              }
              break;
            }
          }
        } else {  // if terminal
          for (int i = 0; i < (int)node.Terminals.size(); i++) {
            if (node.Terminals.at(i).name == pin["name"]) {
              PnRDB::connectNode newnode = {PnRDB::Terminal, i, -1};
              tmpnet2.connected.push_back(newnode);
              break;
            }
          }
        }
      }
      int iter1 = -1, iter2 = -1;  // iterator in Nets
      for (int i = 0; i < (int)node.Nets.size() && (iter1 == -1 || iter2 == -1); i++) {
        if (node.Nets.at(i).name.compare(tmpnet.name) == 0) {
          iter1 = i;
        }
        if (node.Nets.at(i).name.compare(tmpnet2.name) == 0) {
          iter2 = i;
        }
      }
      node.Nets.at(iter1).symCounterpart = iter2;
      node.Nets.at(iter1).axis_dir = constraint["axis_dir"] == "H" ? PnRDB::H : PnRDB::V;
      node.Nets.at(iter1).iter2SNetLsit = node.SNets.size();
      node.Nets.at(iter2).symCounterpart = iter1;
      node.Nets.at(iter2).axis_dir = constraint["axis_dir"] == "H" ? PnRDB::H : PnRDB::V;
      node.Nets.at(iter2).iter2SNetLsit = node.SNets.size();
      node.SNets.resize(node.SNets.size() + 1);
      node.SNets.back().net1 = tmpnet;
      node.SNets.back().net2 = tmpnet2;
      node.SNets.back().iter1 = iter1;
      node.SNets.back().iter2 = iter2;
      node.SNets.back().axis_dir = constraint["axis_dir"] == "H" ? PnRDB::H : PnRDB::V;
    } else if (constraint["const_name"] == "CritNet") {
      for (int i = 0; i < (int)node.Nets.size(); i++) {
        if (node.Nets.at(i).name == constraint["net_name"]) {
          node.Nets.at(i).priority = constraint["priority"];
          break;
        }
      }
    } else if (constraint["const_name"] == "Preplace") {
      /**
      string block_first = temp[2];
      string block_second = temp[3];
      int distance = atoi(temp[4].c_str());
      int horizon = atoi(temp[5].c_str());
      PnRDB::Preplace preplace_const;
      preplace_const.blockid1 = -1;
      preplace_const.blockid2 = -1;

      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_first) == 0) {
          preplace_const.blockid1 = i;
          break;
        }
      }
      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_second) == 0) {
          preplace_const.blockid2 = i;
          break;
        } else {
          preplace_const.conner = block_second;
        }
      }
      preplace_const.distance = distance;
      preplace_const.horizon = horizon;

      if (preplace_const.blockid1 == -1) {
        cout << "-E- ReadConstraint: Preplace: couldn't find block1:" << block_first << endl;
      }
      if (preplace_const.blockid2 == -1) {
        cout << "-E- ReadConstraint: Preplace: couldn't find block2:" << block_second << endl;
      }

      if (preplace_const.blockid1 != -1 && preplace_const.blockid2 != -1) {
        node.Preplace_blocks.push_back(preplace_const);
      }
    **/
    } else if (constraint["const_name"] == "Alignment") {
      /**
      string block_first = temp[2];
      string block_second = temp[3];
      int distance = atoi(temp[4].c_str());
      int horizon = atoi(temp[5].c_str());
      PnRDB::Alignment alignment_const;
      alignment_const.blockid1 = -1;
      alignment_const.blockid2 = -1;

      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_first) == 0) {
          alignment_const.blockid1 = i;
          break;
        }
      }
      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_second) == 0) {
          alignment_const.blockid2 = i;
          break;
        }
      }
      alignment_const.distance = distance;
      alignment_const.horizon = horizon;

      if (alignment_const.blockid1 == -1) {
        cout << "-E- ReadConstraint: Alignment: couldn't find block1:" << block_first << endl;
      }
      if (alignment_const.blockid2 == -1) {
        cout << "-E- ReadConstraint: Alignment: couldn't find block2:" << block_second << endl;
      }

      if (alignment_const.blockid1 != -1 && alignment_const.blockid2 != -1) {
        node.Alignment_blocks.push_back(alignment_const);
      }
      **/
    } else if (constraint["const_name"] == "Abument") {
      /**
      string block_first = temp[2];
      string block_second = temp[3];
      int distance = atoi(temp[4].c_str());
      int horizon = atoi(temp[5].c_str());

      PnRDB::Abument abument_const;
      abument_const.blockid1 = -1;
      abument_const.blockid2 = -1;

      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_first) == 0) {
          abument_const.blockid1 = i;
          break;
        }
      }
      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_second) == 0) {
          abument_const.blockid2 = i;
          break;
        }
      }
      abument_const.distance = distance;
      abument_const.horizon = horizon;

      if (abument_const.blockid1 == -1) {
        cout << "-E- ReadConstraint: Abument: couldn't find block1:" << block_first << endl;
      }
      if (abument_const.blockid2 == -1) {
        cout << "-E- ReadConstraint: Abument: couldn't find block2:" << block_second << endl;
      }

      if (abument_const.blockid1 != -1 && abument_const.blockid2 != -1) {
        node.Abument_blocks.push_back(abument_const);
      }
      **/
    } else if (constraint["const_name"] == "MatchBlock") {
      string block_first = constraint["block1"];
      string block_second = constraint["block2"];

      PnRDB::MatchBlock match_const;
      match_const.blockid1 = -1;
      match_const.blockid2 = -1;

      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_first) == 0) {
          match_const.blockid1 = i;
          break;
        }
      }
      for (int i = 0; i < (int)node.Blocks.size(); i++) {
        if (node.Blocks.at(i).instance.back().name.compare(block_second) == 0) {
          match_const.blockid2 = i;
          break;
        }
      }

      if (match_const.blockid1 == -1) logger->error("ReadConstraint: MatchBlock: couldn't find block1: {0}", block_first);
      if (match_const.blockid2 == -1) logger->error("ReadConstraint: MatchBlock: couldn't find block2: {0}", block_second);
      if (match_const.blockid1 != -1 && match_const.blockid2 != -1) node.Match_blocks.push_back(match_const);
    } else if (constraint["const_name"] == "bias_graph") {
      int distance = constraint["distance"];
      node.bias_Hgraph = distance;
      node.bias_Vgraph = distance;
    } else if (constraint["const_name"] == "bias_Hgraph") {
      int distance = constraint["distance"];
      node.bias_Hgraph = distance;
    } else if (constraint["const_name"] == "bias_Vgraph") {
      int distance = constraint["distance"];
      node.bias_Vgraph = distance;
    } else if (constraint["const_name"] == "ShieldNet") {
      string shield_net = constraint["net_name"];
      for (int i = 0; i < (int)node.Nets.size(); i++) {
        if (node.Nets.at(i).name.compare(shield_net) == 0) {
          node.Nets.at(i).shielding = true;
          break;
        }
      }
    } else if (constraint["const_name"] == "SymmBlock") {
      PnRDB::SymmPairBlock temp_SymmPairBlock;
      temp_SymmPairBlock.axis_dir = constraint["axis_dir"] == "H" ? PnRDB::H : PnRDB::V;
      pair<int, int> temp_pair;
      pair<int, PnRDB::Smark> temp_selfsym;
      for (auto pair : constraint["pairs"]) {
        if (pair["type"] == "sympair") {  // sympair
          temp_pair.first = -1;
          temp_pair.second = -1;
          for (int k = 0; k < (int)node.Blocks.size(); k++) {
            if (node.Blocks.at(k).instance.back().name.compare(pair["block1"]) == 0) {
              temp_pair.first = k;
            }
            if (node.Blocks.at(k).instance.back().name.compare(pair["block2"]) == 0) {
              temp_pair.second = k;
            }
          }
          if (temp_pair.first == -1) logger->error("Block {0} not found", pair["block1"]);
          if (temp_pair.second == -1) logger->error("Block {0} not found", pair["block2"]);
          int temp_int;
          if (temp_pair.first > temp_pair.second) {
            temp_int = temp_pair.second;
            temp_pair.second = temp_pair.first;
            temp_pair.first = temp_int;
          } else if (temp_pair.first == temp_pair.second) {
            logger->error("PnRDB-Error: same block in paired symmetry group");
          }
          temp_SymmPairBlock.sympair.push_back(temp_pair);
        } else {  // selfsym
          for (int j = 0; j < (int)node.Blocks.size(); j++) {
            if (node.Blocks.at(j).instance.back().name.compare(pair["block"]) == 0) {
              temp_selfsym.first = j;
              temp_selfsym.second = constraint["axis_dir"] == "H" ? PnRDB::H : PnRDB::V;
              temp_SymmPairBlock.selfsym.push_back(temp_selfsym);
              break;
            }
          }
        }
      }
      for (unsigned int sym_index = 0; sym_index < temp_SymmPairBlock.selfsym.size(); sym_index++) {
        temp_SymmPairBlock.selfsym[sym_index].second = constraint["axis_dir"] == "H" ? PnRDB::H : PnRDB::V;
      }
      node.SPBlocks.push_back(temp_SymmPairBlock);
    } else if (constraint["const_name"] == "Ordering") {
      // PnRDB::Smark axis_dir = PnRDB::V;
      pair<vector<int>, PnRDB::Smark> temp_order;
      if (constraint["direction"] == "H") {
        temp_order.second = PnRDB::H;
      } else {
        temp_order.second = PnRDB::V;
      }
      for (auto block : constraint["blocks"]) {
        for (int k = 0; k < (int)node.Blocks.size(); k++) {
          if (node.Blocks.at(k).instance.back().name.compare(block) == 0) {
            temp_order.first.push_back(k);
            break;
          }
        }
      }
      if (constraint["abut"]) node.Abut_Constraints.push_back(temp_order);
      node.Ordering_Constraints.push_back(temp_order);
    } else if (constraint["const_name"] == "CC") {
      PnRDB::CCCap temp_cccap;
      temp_cccap.CCCap_name = constraint["cap_name"];
      temp_cccap.Unit_capacitor = constraint["unit_capacitor"];
      for (auto s : constraint["size"]) {
        temp_cccap.size.push_back(s);
      }
      temp_cccap.dummy_flag = !constraint["nodummy"];
      if (temp_cccap.dummy_flag) {
        temp_cccap.cap_ratio = 1;
        temp_cccap.cap_r = constraint["cap_r"];
        temp_cccap.cap_s = constraint["cap_s"];
      }
      node.CC_Caps.push_back(temp_cccap);
    } else if (constraint["const_name"] == "AlignBlock") {
      PnRDB::AlignBlock alignment_unit;
      size_t found;
      if (constraint["line"] == "h_bottom") {
        alignment_unit.horizon = 1;
        alignment_unit.line = 0;
      } else if (constraint["line"] == "h_center") {
        alignment_unit.horizon = 1;
        alignment_unit.line = 1;
      } else if (constraint["line"] == "h_top") {
        alignment_unit.horizon = 1;
        alignment_unit.line = 2;
      } else if (constraint["line"] == "v_left") {
        alignment_unit.horizon = 0;
        alignment_unit.line = 0;
      } else if (constraint["line"] == "v_center") {
        alignment_unit.horizon = 0;
        alignment_unit.line = 1;
      } else if (constraint["line"] == "v_right") {
        alignment_unit.horizon = 0;
        alignment_unit.line = 2;
      } else {
        logger->error("PnRDB-Error: wrong AlignBlock constraint: line {0}", constraint["line"]);
      }
      for (auto block : constraint["blocks"]) {
        bool found = false;
        for (int i = 0; i < (int)node.Blocks.size(); i++) {
          if (node.Blocks.at(i).instance.back().name.compare(block) == 0) {
            alignment_unit.blocks.push_back(i);
            found = true;
            break;
          }
        }
        if (!found) logger->error("Block {0} in AlignBlock not found in netlist", block);
      }
      node.Align_blocks.push_back(alignment_unit);
    } else if (constraint["const_name"] == "PortLocation") {
      // PortLocation(X,L)
      // This constraint indicates the location of the port ‘X’
      // Considering the block as a rectangle, the edges can be divided into 12 sections as shown in the figure below.
      //  L indicates the approximate position of the port. Value of L should be taken from the set
      // {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT, }
      PnRDB::PortPos tmp_portpos;
      if (constraint["location"] == "TL")
        tmp_portpos.pos = PnRDB::TL;
      else if (constraint["location"] == "TC")
        tmp_portpos.pos = PnRDB::TC;
      else if (constraint["location"] == "TR")
        tmp_portpos.pos = PnRDB::TR;
      else if (constraint["location"] == "RT")
        tmp_portpos.pos = PnRDB::RT;
      else if (constraint["location"] == "RC")
        tmp_portpos.pos = PnRDB::RC;
      else if (constraint["location"] == "RB")
        tmp_portpos.pos = PnRDB::RB;
      else if (constraint["location"] == "BL")
        tmp_portpos.pos = PnRDB::BL;
      else if (constraint["location"] == "BC")
        tmp_portpos.pos = PnRDB::BC;
      else if (constraint["location"] == "BR")
        tmp_portpos.pos = PnRDB::BR;
      else if (constraint["location"] == "LB")
        tmp_portpos.pos = PnRDB::LB;
      else if (constraint["location"] == "LC")
        tmp_portpos.pos = PnRDB::LC;
      else if (constraint["location"] == "LT")
        tmp_portpos.pos = PnRDB::LT;
      string name = constraint["terminal_name"];
      for (int k = 0; k < (int)node.Terminals.size(); ++k) {
        if (node.Terminals.at(k).name.compare(name) == 0) {
          tmp_portpos.tid = k;
          break;
        }
      }
      node.Port_Location.push_back(tmp_portpos);
    } else if (constraint["const_name"] == "R_Const") {
      PnRDB::R_const temp_r_const;
      temp_r_const.net_name = constraint["net_name"];
      for (auto pair : constraint["constraints"]) {
        std::pair<int, int> temp_start_pin;
        std::pair<int, int> temp_end_pin;
        vector<string> pins;
        if (pair["pin1"]["type"] == "pin") {
          for (unsigned int j = 0; j < node.Blocks.size(); j++) {
            if (node.Blocks.at(j).instance.back().name.compare(pair["pin1"]["block_name"]) == 0) {
              for (unsigned int k = 0; k < node.Blocks.at(j).instance.back().blockPins.size(); k++) {
                if (node.Blocks.at(j).instance.back().blockPins[k].name.compare(pair["pin1"]["pin_name"]) == 0) {
                  temp_start_pin.first = j;
                  temp_start_pin.second = k;
                  temp_r_const.start_pin.push_back(temp_start_pin);
                  break;
                }
              }
            }
          }
        } else if (pair["pin1"]["type"] == "terminal") {
          for (unsigned int j = 0; j < node.Terminals.size(); j++) {
            if (node.Terminals.at(j).name.compare(pair["pin1"]["terminal_name"]) == 0) {
              temp_start_pin.first = -1;
              temp_start_pin.second = j;
              temp_r_const.start_pin.push_back(temp_start_pin);
              break;
            }
          }
        }
        if (pair["pin2"]["type"] == "pin") {
          for (unsigned int j = 0; j < node.Blocks.size(); j++) {
            if (node.Blocks.at(j).instance.back().name.compare(pair["pin2"]["block_name"]) == 0) {
              for (unsigned int k = 0; k < node.Blocks.at(j).instance.back().blockPins.size(); k++) {
                if (node.Blocks.at(j).instance.back().blockPins[k].name.compare(pair["pin2"]["pin_name"]) == 0) {
                  temp_end_pin.first = j;
                  temp_end_pin.second = k;
                  temp_r_const.end_pin.push_back(temp_end_pin);
                  break;
                }
              }
            }
          }
        } else if (pair["pin2"]["type"] == "terminal") {
          for (unsigned int j = 0; j < node.Terminals.size(); j++) {
            if (node.Terminals.at(j).name.compare(pair["pin2"]["terminal_name"]) == 0) {
              temp_end_pin.first = -1;
              temp_end_pin.second = j;
              temp_r_const.end_pin.push_back(temp_end_pin);
              break;
            }
          }
        }
        temp_r_const.R.push_back(pair["R"]);
      }
      node.R_Constraints.push_back(temp_r_const);
    } else if (constraint["const_name"] == "LinearConst") {
      PnRDB::LinearConst temp_LinearConst;
      temp_LinearConst.net_name = constraint["net_name"];

      for (auto pin : constraint["constraints"]) {
        std::pair<int, int> temp_pin;
        vector<string> pins;
        if (pin["type"] == "pin") {
          for (unsigned int j = 0; j < node.Blocks.size(); j++) {
            if (node.Blocks.at(j).instance.back().name.compare(pin["block_name"]) == 0) {
              for (unsigned int k = 0; k < node.Blocks.at(j).instance.back().blockPins.size(); k++) {
                if (node.Blocks.at(j).instance.back().blockPins[k].name.compare(pin["pin_name"]) == 0) {
                  temp_pin.first = j;
                  temp_pin.second = k;
                  temp_LinearConst.pins.push_back(temp_pin);
                  break;
                }
              }
            }
          }
        } else if (pin["type"] == "terminal") {
          for (unsigned int j = 0; j < node.Terminals.size(); j++) {
            if (node.Terminals.at(j).name.compare(pin["terminal_name"]) == 0) {
              temp_pin.first = -1;
              temp_pin.second = j;
              temp_LinearConst.pins.push_back(temp_pin);
              break;
            }
          }
        }
        temp_LinearConst.alpha.push_back(pin["alpha"]);
      }
      temp_LinearConst.upperBound = constraint["upperBound"];
      node.L_Constraints.push_back(temp_LinearConst);
    } else if (constraint["const_name"] == "Multi_LinearConst") {
      PnRDB::Multi_LinearConst temp_Multi_LinearConst;
      for (auto c : constraint["constraints"]) {
        PnRDB::LinearConst temp_LinearConst;
        temp_LinearConst.net_name = c["net_name"];
        for (auto pin : c["pins"]) {
          std::pair<int, int> temp_pin;
          if (pin["type"] == "pin") {
            for (unsigned int j = 0; j < node.Blocks.size(); j++) {
              if (node.Blocks.at(j).instance.back().name.compare(pin["block_name"]) == 0) {
                for (unsigned int k = 0; k < node.Blocks.at(j).instance.back().blockPins.size(); k++) {
                  if (node.Blocks.at(j).instance.back().blockPins[k].name.compare(pin["pin_name"]) == 0) {
                    temp_pin.first = j;
                    temp_pin.second = k;
                    temp_LinearConst.pins.push_back(temp_pin);
                    temp_LinearConst.alpha.push_back(pin["alpha"]);
                    break;
                  }
                }
              }
            }
          } else if (pin["type"] == "terminal") {
            for (unsigned int j = 0; j < node.Terminals.size(); j++) {
              if (node.Terminals.at(j).name.compare(pin["terminal_name"]) == 0) {
                temp_pin.first = -1;
                temp_pin.second = j;
                temp_LinearConst.pins.push_back(temp_pin);
                temp_LinearConst.alpha.push_back(pin["alpha"]);
                break;
              }
            }
          }
        }

        temp_Multi_LinearConst.Multi_linearConst.push_back(temp_LinearConst);
      }
      temp_Multi_LinearConst.upperBound = constraint["upperBound"];
      node.ML_Constraints.push_back(temp_Multi_LinearConst);
    } else if (constraint["const_name"] == "Aspect_Ratio") {
      node.Aspect_Ratio_weight = constraint["weight"];
      node.Aspect_Ratio[0] = constraint["ratio_low"];
      node.Aspect_Ratio[1] = constraint["ratio_high"];
      if (node.Aspect_Ratio[0] > node.Aspect_Ratio[1]) logger->error("Aspect ratio lower bound should be smaller than upper bound.");
    } else if (constraint["const_name"] == "Multi_Connection") {
      PnRDB::Multi_connection temp_multi_Connection;
      temp_multi_Connection.net_name = constraint["net_name"];
      temp_multi_Connection.multi_number = constraint["multi_number"];
      node.Multi_connections.push_back(temp_multi_Connection);
      for (unsigned int j = 0; j < node.Nets.size(); j++) {
        if (node.Nets[j].name == constraint["net_name"]) {
          node.Nets[j].multi_connection = constraint["multi_number"];
          break;
        }
      }
    } else if (constraint["const_name"] == "C_Const") {
      PnRDB::C_const temp_c_const;
      temp_c_const.net_name = constraint["net_name"];

      for (auto pair : constraint["constraints"]) {
        std::pair<int, int> temp_start_pin;
        std::pair<int, int> temp_end_pin;
        if (pair["pin1"]["type"] == "pin") {
          for (unsigned int j = 0; j < node.Blocks.size(); j++) {
            if (node.Blocks.at(j).instance.back().name.compare(pair["pin1"]["block_name"]) == 0) {
              for (unsigned int k = 0; k < node.Blocks.at(j).instance.back().blockPins.size(); k++) {
                if (node.Blocks.at(j).instance.back().blockPins[k].name.compare(pair["pin1"]["pin_name"]) == 0) {
                  temp_start_pin.first = j;
                  temp_start_pin.second = k;
                  temp_c_const.start_pin.push_back(temp_start_pin);
                  break;
                }
              }
            }
          }
        } else if (pair["pin1"]["type"] == "terminal") {
          for (unsigned int j = 0; j < node.Terminals.size(); j++) {
            if (node.Terminals.at(j).name.compare(pair["pin1"]["terminal_name"]) == 0) {
              temp_start_pin.first = -1;
              temp_start_pin.second = j;
              temp_c_const.start_pin.push_back(temp_start_pin);
              break;
            }
          }
        }

        if (pair["pin2"]["type"] == "pin") {
          for (unsigned int j = 0; j < node.Blocks.size(); j++) {
            if (node.Blocks.at(j).instance.back().name.compare(pair["pin2"]["block_name"]) == 0) {
              for (unsigned int k = 0; k < node.Blocks.at(j).instance.back().blockPins.size(); k++) {
                if (node.Blocks.at(j).instance.back().blockPins[k].name.compare(pair["pin2"]["pin_name"]) == 0) {
                  temp_end_pin.first = j;
                  temp_end_pin.second = k;
                  temp_c_const.end_pin.push_back(temp_end_pin);
                  break;
                }
              }
            }
          }
        } else if (pair["pin2"]["type"] == "terminal") {
          for (unsigned int j = 0; j < node.Terminals.size(); j++) {
            if (node.Terminals.at(j).name.compare(pair["pin2"]["terminal_name"]) == 0) {
              temp_end_pin.first = -1;
              temp_end_pin.second = j;
              temp_c_const.end_pin.push_back(temp_end_pin);
              break;
            }
          }
        }
        temp_c_const.C.push_back(pair["C"]);
      }
      node.C_Constraints.push_back(temp_c_const);
    } else if (constraint["const_name"] == "GuardRing") {
      PnRDB::Guardring_Const temp_Guardring_Const;
      temp_Guardring_Const.block_name = constraint["block_name"];
      temp_Guardring_Const.guard_ring_primitives = constraint["guard_ring_primitives"];
      temp_Guardring_Const.global_pin = constraint["global_pin"];
      node.Guardring_Consts.push_back(temp_Guardring_Const);
    } else if (constraint["const_name"] == "Boundary") {
      node.placement_box[0] = constraint["max_width"];
      node.placement_box[1] = constraint["max_height"];
      if (node.placement_box[0] <= 0 || node.placement_box[1] <= 0)
        logger->error("Wrong placement bounding box, width {0}, height {1}", node.placement_box[0], node.placement_box[1]);
      node.placement_box[0] *= unitScale;
      node.placement_box[1] *= unitScale;
    } else if (constraint["const_name"] == "SameTemplate") {
      set<int> temp_const;
      for (auto b : constraint["blocks"]) {
        temp_const.insert(node.Block_name_map[b]);
      }
      node.Same_Template_Constraints.push_back(temp_const);
    } else if (constraint["const_name"] == "CompactPlacement") {
      node.compact_style = constraint["style"];
    } else if(constraint["const_name"] == "DoNotRoute"){
      vector<string> DoNotRoute;
      for(auto net : constraint["nets"]){
         DoNotRoute.push_back(net);
      }
      node.DoNotRoute = DoNotRoute;
    }
  }
}

void PnRdatabase::ReadPrimitiveOffsetPitch(vector<PnRDB::lefMacro> &primitive, const string &jsonStr){
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.ReadLeafOffsetPitch");
  auto &b = lefData[primitive.front().name].front();
  json jedb = json::parse(jsonStr);
  if(jedb.contains("metadata")){
    json constraints = jedb["metadata"]["constraints"];
    for (auto constraint : constraints) {
      if (constraint["constraint"] == "place_on_grid"){
        string s = constraint["direction"];
        if (constraint["direction"] == "H") {  // horizontal metal
          for(auto offset:constraint["ored_terms"][0]["offsets"]){
            b.yoffset.push_back(offset);
            b.yoffset.back() = b.yoffset.back() * 2 / ScaleFactor;
          }
          b.ypitch = constraint["pitch"];
          b.ypitch = b.ypitch * 2 / ScaleFactor;
        } else if (constraint["direction"] == "V") {  // vertical metal
          for(auto offset:constraint["ored_terms"][0]["offsets"]){
            b.xoffset.push_back(offset);
            b.xoffset.back() = b.xoffset.back() * 2 / ScaleFactor;
          }
          b.xpitch = constraint["pitch"];
          b.xpitch = b.xpitch * 2 / ScaleFactor;
        }
      }
    }
  }
}
