#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>

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
        std::cout<<"Reading Const symCounterpart"<<iter1<<"@"<<iter2<<" "<<iter2<<"@"<<iter1<<std::endl;
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

        if (match_const.blockid1 == -1)cout << "-E- ReadConstraint: MatchBlock: couldn't find block1:" << block_first << endl;
        if (match_const.blockid2 == -1)cout << "-E- ReadConstraint: MatchBlock: couldn't find block2:" << block_second << endl;
        if (match_const.blockid1 != -1 && match_const.blockid2 != -1)node.Match_blocks.push_back(match_const);
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
        temp_SymmPairBlock.axis_dir = constraint["axis_dir"]=="H"?PnRDB::H:PnRDB::V;
        pair<int, int> temp_pair;
        pair<int, PnRDB::Smark> temp_selfsym;
        for (auto pair : constraint["pairs"]) {
          if (pair["type"] == "sympair") {  // sympair
            for (int k = 0; k < (int)node.Blocks.size(); k++) {
              if (node.Blocks.at(k).instance.back().name.compare(pair["block1"]) == 0) {
                temp_pair.first = k;
              }
              if (node.Blocks.at(k).instance.back().name.compare(pair["block2"]) == 0) {
                temp_pair.second = k;
              }
            }
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
                temp_selfsym.second = constraint["axis_dir"]=="H"?PnRDB::H:PnRDB::V;
                temp_SymmPairBlock.selfsym.push_back(temp_selfsym);
                break;
              }
            }
          }
        }
        for (unsigned int sym_index = 0; sym_index < temp_SymmPairBlock.selfsym.size(); sym_index++) {
          temp_SymmPairBlock.selfsym[sym_index].second = constraint["axis_dir"]=="H"?PnRDB::H:PnRDB::V;
        }
        node.SPBlocks.push_back(temp_SymmPairBlock);
      } else if (constraint["const_name"] == "Ordering") {
        //PnRDB::Smark axis_dir = PnRDB::V;
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
        if (constraint["direction"] == "H") {
          alignment_unit.horizon = 1;
        } else {
          alignment_unit.horizon = 0;
        }
        for (auto block : constraint["blocks"]) {
          for (int i = 0; i < (int)node.Blocks.size(); i++) {
            if (node.Blocks.at(i).instance.back().name.compare(block) == 0) {
              alignment_unit.blocks.push_back(i);
              break;
            }
          }
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
                std::cout << "Test C end pin " << temp_end_pin.first << " " << temp_end_pin.second << std::endl;
                break;
              }
            }
          }
          temp_c_const.C.push_back(pair["C"]);
        }
        node.C_Constraints.push_back(temp_c_const);
      }
    }
}

bool PnRdatabase::ReadConstraint(PnRDB::hierNode& node, string fpath, string suffix) {
  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.ReadConstraint");

  ifstream fin;
  string def;
  vector<string> temp, tempsec;
  size_t found;
  string cfile=fpath+"/"+node.name+"."+suffix;
  logger->info("start to read const file {0}",cfile);
  // constraint format issues(comma): Alignment, Preplace, MatchBlock, Abutment
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(cfile.c_str());
    while(fin.peek()!=EOF) {
      getline(fin, def);
      //std::cout<<"line "<<def<<std::endl;
      if(def.compare("")==0) {continue;}
      temp=split_by_spaces(def);
      //for(int i=0;i<temp.size();i++) {cout<<" ? "<<temp[i];}
      //cout<<endl;
      if(temp[0].compare("SymmNet")==0) {
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        //cout<<word<<endl;
        tempsec=StringSplitbyChar(word, ',');
        //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
        PnRDB::net tmpnet;
        for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
          if(it==tempsec.begin()) {
            tmpnet.name=*it;
          } else {
            if(it->find("/")!=string::npos) { // if block pin
              vector<string> tempthd=StringSplitbyChar(*it, '/');
              for(int i=0;i<(int)node.Blocks.size();i++) {
                if(node.Blocks.at(i).instance.back().name.compare(tempthd[0])==0) {
                  for(int j=0;j<(int)node.Blocks.at(i).instance.back().blockPins.size();j++) {
                    if(node.Blocks.at(i).instance.back().blockPins.at(j).name.compare(tempthd[1])==0) {
                      //cout<<j<<" "<<i<<endl;
                      PnRDB::connectNode newnode={PnRDB::Block, j, i};
                      tmpnet.connected.push_back(newnode);
                      break;
                    }
                  }
                  break;
                }
              }
              //cout<<*it<<" is pin"<<tempthd[0]<<"/"<<tempthd[1]<<endl;
            } else { // if terminal
              for(int i=0;i<(int)node.Terminals.size();i++) {
                if(node.Terminals.at(i).name.compare(*it)==0) {
                  PnRDB::connectNode newnode={PnRDB::Terminal, i, -1};
                  tmpnet.connected.push_back(newnode);
                  break;
                }
              }
              //cout<<*it<<" is terminal"<<endl;
            }
          }
        }
        word=temp[4];
        //cout<<word<<endl;
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        tempsec=StringSplitbyChar(word, ',');
        //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
        PnRDB::net tmpnet2;
        for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); it++) {
          if(it==tempsec.begin()) {
            tmpnet2.name=*it;
          } else {
            if(it->find("/")!=string::npos) { // if block pin
              vector<string> tempthd=StringSplitbyChar(*it, '/');
              for(int i=0;i<(int)node.Blocks.size();i++) {
                //std::cout<<"block "<<node.Blocks.at(i).instance.back().name<<std::endl;
                if(node.Blocks.at(i).instance.back().name.compare(tempthd[0])==0) {
                  for(int j=0;j<(int)node.Blocks.at(i).instance.back().blockPins.size();j++) {
                    //std::cout<<"\t pin "<<node.Blocks.at(i).instance.back().blockPins.at(j).name<<std::endl;
                    if(node.Blocks.at(i).instance.back().blockPins.at(j).name.compare(tempthd[1])==0) {
                      //cout<<j<<" "<<i<<endl;
                      PnRDB::connectNode newnode={PnRDB::Block, j, i};
                      tmpnet2.connected.push_back(newnode);
                      break;
                    }
                  }
                  break;
                }
              }
              //cout<<*it<<" is pin"<<tempthd[0]<<"/"<<tempthd[1]<<endl;
            } else { // if terminal
              for(int i=0;i<(int)node.Terminals.size();i++) {
                if(node.Terminals.at(i).name.compare(*it)==0) {
                  PnRDB::connectNode newnode={PnRDB::Terminal, i, -1};
                  tmpnet2.connected.push_back(newnode);
                  break;
                }
              }
              //cout<<*it<<" is terminal"<<endl;
            }
          }
        }
        
        PnRDB::Smark axis_dir=PnRDB::V;
        if(temp.size()>=8){
          word=temp[6];
          //cout<<word<<endl;
          word=word.substr(1);
          word=word.substr(0, word.length()-1);  
          if(word=="H"){axis_dir=PnRDB::H;}
          else if(word=="V"){axis_dir=PnRDB::V;}        
        }

        int iter1=-1, iter2=-1; // iterator in Nets
        for(int i=0;i<(int)node.Nets.size()&&(iter1==-1||iter2==-1);i++) {
          if(node.Nets.at(i).name.compare(tmpnet.name)==0) {iter1=i;}
          if(node.Nets.at(i).name.compare(tmpnet2.name)==0) {iter2=i;}
        }
        if (tmpnet.connected.size() != tmpnet2.connected.size()) continue;
        node.Nets.at(iter1).symCounterpart = iter2;
        node.Nets.at(iter1).iter2SNetLsit=node.SNets.size();
        node.Nets.at(iter2).symCounterpart=iter1;
        node.Nets.at(iter2).iter2SNetLsit=node.SNets.size();
        node.SNets.resize(node.SNets.size()+1);
        node.SNets.back().net1=tmpnet;
        node.SNets.back().net2=tmpnet2;
        node.SNets.back().iter1=iter1;
        node.SNets.back().iter2=iter2;
        node.SNets.back().axis_dir=axis_dir;
      } else if (temp[0].compare("CritNet")==0) {
        for(int i=0;i<(int)node.Nets.size();i++) {
          if(node.Nets.at(i).name.compare(temp[2])==0) {
            node.Nets.at(i).priority=temp[4];
            break;
          }
        }
      } else if(temp[0].compare("Preplace")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
        PnRDB::Preplace preplace_const;
	preplace_const.blockid1 = -1;
	preplace_const.blockid2 = -1;


        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            preplace_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            preplace_const.blockid2 = i;
            break;
          } else {
            preplace_const.conner = block_second;
          }
        }
        preplace_const.distance = distance;
        preplace_const.horizon = horizon;


	if ( preplace_const.blockid1 == -1) {
	  logger->error("-E- ReadConstraint: Preplace: couldn't find block1: {0}" , block_first);
	}
	if ( preplace_const.blockid2 == -1) {
	  logger->error("-E- ReadConstraint: Preplace: couldn't find block2: {0}" , block_second);
	}

	if ( preplace_const.blockid1 != -1 && preplace_const.blockid2!= -1) {
	  node.Preplace_blocks.push_back(preplace_const);
	}



      } else if(temp[0].compare("Alignment")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
        PnRDB::Alignment alignment_const;
	alignment_const.blockid1 = -1;
	alignment_const.blockid2 = -1;


        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            alignment_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            alignment_const.blockid2 = i;
            break;
          }
        }
        alignment_const.distance = distance;
        alignment_const.horizon = horizon;

	if ( alignment_const.blockid1 == -1) {
	  logger->error("-E- ReadConstraint: Alignment: couldn't find block1: {0}", block_first );
	}
	if ( alignment_const.blockid2 == -1) {
	  logger->error("-E- ReadConstraint: Alignment: couldn't find block2: {0}" ,block_second);
	}

	if ( alignment_const.blockid1 != -1 && alignment_const.blockid2!= -1) {
	  node.Alignment_blocks.push_back(alignment_const);
	}


      } else if(temp[0].compare("Abument")==0){
        string block_first=temp[2];
        string block_second=temp[3];
        int distance= atoi(temp[4].c_str());
        int horizon = atoi(temp[5].c_str());
      
        PnRDB::Abument abument_const;
	abument_const.blockid1 = -1;
	abument_const.blockid2 = -1;
      
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            abument_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            abument_const.blockid2 = i;
            break;
          }
        }
        abument_const.distance = distance;
        abument_const.horizon = horizon;

	if ( abument_const.blockid1 == -1) {
	  logger->error( "-E- ReadConstraint: Abument: couldn't find block1: {0}", block_first);
	}
	if ( abument_const.blockid2 == -1) {
	  logger->error( "-E- ReadConstraint: Abument: couldn't find block2: {0}" , block_second);
	}

	if ( abument_const.blockid1 != -1 && abument_const.blockid2!= -1) {
	  node.Abument_blocks.push_back(abument_const);
	}
      } else if(temp[0].compare("MatchBlock")==0){
        string block_first=temp[2];
        string block_second=temp[4];
        //int distance= atoi(temp[4].c_str());
        //int horizon = atoi(temp[5].c_str());
      
        PnRDB::MatchBlock match_const;
	match_const.blockid1 = -1;
	match_const.blockid2 = -1;
      
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_first)==0) {
            match_const.blockid1 = i;
            break;
          }
        }
        for(int i=0;i<(int)node.Blocks.size();i++) {
          if(node.Blocks.at(i).instance.back().name.compare(block_second)==0) {
            match_const.blockid2 = i;
            break;
          }
        }

	if ( match_const.blockid1 == -1) {
	  logger->error( "-E- ReadConstraint: MatchBlock: couldn't find block1: {0} " , block_first );
	}
	if ( match_const.blockid2 == -1) {
	  logger->error( "-E- ReadConstraint: MatchBlock: couldn't find block2: {0} " , block_second);
	}

        //match_const.distance = distance;
        //match_const.horizon = horizon;
	if ( match_const.blockid1 != -1 && match_const.blockid2!= -1) {
	  node.Match_blocks.push_back(match_const);
	}
      } else if(temp[0].compare("bias_graph")==0){
        int distance= atoi(temp[2].c_str());
        node.bias_Hgraph = 2*distance;
        node.bias_Vgraph = 2*distance;
      } else if(temp[0].compare("bias_Hgraph")==0 ) {
        int distance= atoi(temp[2].c_str());
        node.bias_Hgraph = 2*distance;
      } else if(temp[0].compare("bias_Vgraph")==0 ) {
        int distance= atoi(temp[2].c_str());
        node.bias_Vgraph = 2*distance;
      } else if (temp[0].compare("ShieldNet")==0) {
        string shield_net=temp[2];
        for(int i=0;i<(int)node.Nets.size();i++) {
          if(node.Nets.at(i).name.compare(shield_net)==0) {
            node.Nets.at(i).shielding=true; break;
          }
        }
      } else if (temp[0].compare("SymmBlock")==0) { 
        PnRDB::SymmPairBlock temp_SymmPairBlock;
        pair<int,int> temp_pair={-1,-1};
        pair<int,PnRDB::Smark> temp_selfsym;
        PnRDB::Smark axis_dir=PnRDB::V;
        for(unsigned int i=2;i<temp.size();i=i+2){
          string word=temp[i];
          word=word.substr(1);
          word=word.substr(0, word.length()-1);
          tempsec=StringSplitbyChar(word, ',');
          if((found=temp[i].find(","))!=string::npos) { // sympair
            for(int k=0;k<(int)node.Blocks.size();k++) {
              if(node.Blocks.at(k).instance.back().name.compare(tempsec[0])==0) {temp_pair.first = k;}
              if(node.Blocks.at(k).instance.back().name.compare(tempsec[1])==0) {temp_pair.second = k;}
            }
            int temp_int;
            if(temp_pair.first>temp_pair.second){
              temp_int = temp_pair.second;
              temp_pair.second = temp_pair.first;
              temp_pair.first = temp_int;
            } else if (temp_pair.first==temp_pair.second) {
              logger->error("PnRDB-Error: same block in paired symmetry group");
            }
            if (temp_pair.first >= 0 && temp_pair.second >= 0) temp_SymmPairBlock.sympair.push_back(temp_pair);
          } else if (word == "H") {
            axis_dir = PnRDB::H;
          } else if (word == "V") {
            axis_dir = PnRDB::V;
          } else {  // selfsym
            for(int j=0;j<(int)node.Blocks.size();j++) {
              if(node.Blocks.at(j).instance.back().name.compare(word)==0) {
                temp_selfsym.first =  j;
                temp_selfsym.second = axis_dir;
                //temp_selfsym.second = PnRDB::H;
                temp_SymmPairBlock.selfsym.push_back(temp_selfsym);
                break;
              }
            }
          }
        }
        temp_SymmPairBlock.axis_dir = axis_dir;
        
        for(unsigned int sym_index=0;sym_index<temp_SymmPairBlock.selfsym.size();sym_index++){
           temp_SymmPairBlock.selfsym[sym_index].second=axis_dir;
        }

        node.SPBlocks.push_back(temp_SymmPairBlock);
      }else if (temp[0].compare("Ordering")==0) {
        //PnRDB::Smark axis_dir = PnRDB::V;
        pair<vector<int>, PnRDB::Smark> temp_order;
        for (unsigned int i = 2; i < temp.size(); i = i + 2) {
          string word = temp[i];
          if (word == "H")
            temp_order.second = PnRDB::H;
          else if (word == "V")
            temp_order.second = PnRDB::V;
          else {
            for (int k = 0; k < (int)node.Blocks.size(); k++) {
              if (node.Blocks.at(k).instance.back().name.compare(word) == 0) {
                temp_order.first.push_back(k);
                break;
              }
            }
          }
        }
        node.Ordering_Constraints.push_back(temp_order);
      }else if(temp[0].compare("CC")==0){
        PnRDB::CCCap temp_cccap;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_cccap.CCCap_name = word;
        word = temp[6];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_cccap.Unit_capacitor = word;
        word=temp[4];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        //cout<<word<<endl;
        tempsec=StringSplitbyChar(word, ',');
        for(unsigned int p=0;p<tempsec.size();p++){ 
            temp_cccap.size.push_back(atoi(tempsec[p].c_str()));
           }

        if(temp.size()>9){
            word=temp[8];
            word=word.substr(1);
            word=word.substr(0, word.length()-1);
            if(word=="nodummy"){
              temp_cccap.dummy_flag=0;
            }else{

              temp_cccap.cap_ratio = 1;
              tempsec=StringSplitbyChar(word, ',');
              temp_cccap.cap_r = atoi(tempsec[0].c_str());
              temp_cccap.cap_s = atoi(tempsec[1].c_str());

            }
            
           }

        if(temp.size()>11){
          temp_cccap.cap_ratio = 1;
          word=temp[10];
          word=word.substr(1);
          word=word.substr(0, word.length()-1);
          //cout<<word<<endl;
          if(word=="nodummy"){
              temp_cccap.dummy_flag=0;
            }else{

              temp_cccap.cap_ratio = 1;
              tempsec=StringSplitbyChar(word, ',');
              temp_cccap.cap_r = atoi(tempsec[0].c_str());
              temp_cccap.cap_s = atoi(tempsec[1].c_str());

            }
          }
        //temp_cccap.size = temp[4]; //size?
        
        node.CC_Caps.push_back(temp_cccap);
      } else if(temp[0].compare("GuardRing")==0) {
        PnRDB::Guardring_Const temp_Guardring_Const;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_Guardring_Const.block_name = word;
        word = temp[4];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_Guardring_Const.guard_ring_perimitives = word;
        word=temp[6];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_Guardring_Const.global_pin = word;
        node.Guardring_Consts.push_back(temp_Guardring_Const);

      }else if (temp[0].compare("AlignBlock")==0) {
        PnRDB::AlignBlock alignment_unit;
        if(temp[2].compare("H")==0) {
          alignment_unit.horizon=1;
        } else {
          alignment_unit.horizon=0;
        }
        for(int j=4;j<(int)temp.size();j+=2) {
          for(int i=0;i<(int)node.Blocks.size();i++) {
            if(node.Blocks.at(i).instance.back().name.compare(temp[j])==0) {
              alignment_unit.blocks.push_back(i);
              break;
            }
          }
        }
        //std::cout<<"AlignBlock "<<alignment_unit.horizon<<" @ ";
        for(unsigned int i=0;i<alignment_unit.blocks.size();i++) {std::cout<<alignment_unit.blocks[i]<<" ";}
        //std::cout<<std::endl;
        node.Align_blocks.push_back(alignment_unit);
      } else if (temp[0].compare("PortLocation")==0) {
        // PortLocation(X,L) 
        // This constraint indicates the location of the port ‘X’
        // Considering the block as a rectangle, the edges can be divided into 12 sections as shown in the figure below.
        //  L indicates the approximate position of the port. Value of L should be taken from the set
        // {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT, }
        PnRDB::PortPos tmp_portpos;
        //std::cout<<temp[4]<<temp[2]<<std::endl;
        if(temp[4].compare("TL")==0) {
          tmp_portpos.pos=PnRDB::TL;
          //std::cout<<"TL\n";
        } else if(temp[4].compare("TC")==0) {
	  //std::cout<<"TC\n";
          tmp_portpos.pos=PnRDB::TC;
        } else if(temp[4].compare("TR")==0) {
          //std::cout<<"TR\n";
          tmp_portpos.pos=PnRDB::TR;
        } else if(temp[4].compare("RT")==0) {
          //std::cout<<"RT\n";
          tmp_portpos.pos=PnRDB::RT;
        } else if(temp[4].compare("RC")==0) {
          //std::cout<<"RC\n";
          tmp_portpos.pos=PnRDB::RC;
        } else if(temp[4].compare("RB")==0) {
          //std::cout<<"RB\n";
          tmp_portpos.pos=PnRDB::RB;
        } else if(temp[4].compare("BL")==0) {
          //std::cout<<"BL\n";
          tmp_portpos.pos=PnRDB::BL;
        } else if(temp[4].compare("BC")==0) {
          //std::cout<<"BC\n";
          tmp_portpos.pos=PnRDB::BC;
        } else if(temp[4].compare("BR")==0) {
          //std::cout<<"BR\n";
          tmp_portpos.pos=PnRDB::BR;
        } else if(temp[4].compare("LB")==0) {
          //std::cout<<"LB\n";
          tmp_portpos.pos=PnRDB::LB;
        } else if(temp[4].compare("LC")==0) {
          //std::cout<<"LC\n";
          tmp_portpos.pos=PnRDB::LC;
        } else if(temp[4].compare("LT")==0) {
          //std::cout<<"LT\n";
          tmp_portpos.pos=PnRDB::LT;
        }
        string name=temp[2];
        for(int k=0;k<(int)node.Terminals.size();++k) {
          //std::cout<<name<<" vs "<<node.Terminals.at(k).name<<std::endl;
          if(node.Terminals.at(k).name.compare(name)==0) {
            tmp_portpos.tid=k;
            break;
          }
        }
        //std::cout<<"PortLocation "<<tmp_portpos.tid<<" @ "<<tmp_portpos.pos<<std::endl;
        node.Port_Location.push_back(tmp_portpos);
      } else if (temp[0].compare("R_Const")==0){
        PnRDB::R_const temp_r_const;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_r_const.net_name=word;

        for(unsigned int i=4;i<temp.size()-1;i+=2){

           word=temp[i];
           word=word.substr(1);
           word=word.substr(0, word.length()-1);
           //cout<<word<<endl;
           tempsec=StringSplitbyChar(word, ',');
           //std::cout<<"Test R "<<std::endl;
           //for(unsigned int j=0;j<tempsec.size();j++){std::cout<<tempsec[j]<<std::endl;}
           //std::cout<<"End Test R "<<std::endl;
           std::pair<int,int> temp_start_pin;
           std::pair<int,int> temp_end_pin;
           vector<string> pins;

           pins = StringSplitbyChar(tempsec[0], '/');
           if(pins.size()>1){
              for(unsigned int j=0;j<node.Blocks.size();j++){
                 if(node.Blocks.at(j).instance.back().name.compare(pins[0])==0){
                    for(unsigned int k=0;k<node.Blocks.at(j).instance.back().blockPins.size();k++){
                       if(node.Blocks.at(j).instance.back().blockPins[k].name.compare(pins[1])==0){
                         temp_start_pin.first = j;
                         temp_start_pin.second = k;
                         temp_r_const.start_pin.push_back(temp_start_pin);
                         //std::cout<<"Test R start pin "<<temp_start_pin.first<<" "<<temp_start_pin.second<<std::endl;
                         break; 
                       }
                    }
                 }
              }
           }else if(pins.size()==1){
              for(unsigned int j=0;j<node.Terminals.size();j++){
                 if(node.Terminals.at(j).name.compare(pins[0])==0){
                    temp_start_pin.first = -1;
                    temp_start_pin.second = j;
                    temp_r_const.start_pin.push_back(temp_start_pin);
                    //std::cout<<"Test R start pin "<<temp_start_pin.first<<" "<<temp_start_pin.second<<std::endl;
                    break; 
                 }
              }
           }

           pins = StringSplitbyChar(tempsec[1], '/');
           if(pins.size()>1){
              for(unsigned int j=0;j<node.Blocks.size();j++){
                 if(node.Blocks.at(j).instance.back().name.compare(pins[0])==0){
                    for(unsigned int k=0;k<node.Blocks.at(j).instance.back().blockPins.size();k++){
                       if(node.Blocks.at(j).instance.back().blockPins[k].name.compare(pins[1])==0){
                         temp_end_pin.first = j;
                         temp_end_pin.second = k;
                         temp_r_const.end_pin.push_back(temp_end_pin);
                         //std::cout<<"Test R end pin "<<temp_end_pin.first<<" "<<temp_end_pin.second<<std::endl;
                         break; 
                       }
                    }
                 }
              }
           }else if(pins.size()==1){
              for(unsigned int j=0;j<node.Terminals.size();j++){
                 if(node.Terminals.at(j).name.compare(pins[0])==0){
                    temp_end_pin.first = -1;
                    temp_end_pin.second = j;
                    temp_r_const.end_pin.push_back(temp_end_pin);
                    //std::cout<<"Test R end pin "<<temp_end_pin.first<<" "<<temp_end_pin.second<<std::endl;
                    break; 
                 }
              }
           }

           temp_r_const.R.push_back(atoi(tempsec[2].c_str()));
        }
        node.R_Constraints.push_back(temp_r_const);
      }else if(temp[0].compare("LinearConst")==0){
        PnRDB::LinearConst temp_LinearConst;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_LinearConst.net_name=word;

        for(unsigned int i=4;i<temp.size()-3;i+=2){

           word=temp[i];
           word=word.substr(1);
           word=word.substr(0, word.length()-1);
           //cout<<word<<endl;
           tempsec=StringSplitbyChar(word, ',');
           std::pair<int,int> temp_pin;
           vector<string> pins;

           pins = StringSplitbyChar(tempsec[0], '/');
           if(pins.size()>1){
              for(unsigned int j=0;j<node.Blocks.size();j++){
                 if(node.Blocks.at(j).instance.back().name.compare(pins[0])==0){
                    for(unsigned int k=0;k<node.Blocks.at(j).instance.back().blockPins.size();k++){
                       if(node.Blocks.at(j).instance.back().blockPins[k].name.compare(pins[1])==0){
                         temp_pin.first = j;
                         temp_pin.second = k;
                         temp_LinearConst.pins.push_back(temp_pin);
                         //std::cout<<"Test Linear pin "<<pins[0]<<" "<<pins[1]<<" "<<temp_pin.first<<" "<<temp_pin.second<<std::endl;
                         break; 
                       }
                    }
                 }
              }
           }else if(pins.size()==1){
              for(unsigned int j=0;j<node.Terminals.size();j++){
                 if(node.Terminals.at(j).name.compare(pins[0])==0){
                    temp_pin.first = -1;
                    temp_pin.second = j;
                    temp_LinearConst.pins.push_back(temp_pin);
                    //std::cout<<"Test Linear pin "<<pins[0]<<" "<<temp_pin.first<<" "<<temp_pin.second<<std::endl;
                    break; 
                 }
              }
           }
           temp_LinearConst.alpha.push_back(atof(tempsec[1].c_str()));
           //std::cout<<"Test Linear pin alpha "<<tempsec[1]<<" "<<atof(tempsec[1].c_str())<<std::endl;
        }
        int temp_size = temp.size();
        temp_LinearConst.upperBound = atof(temp[temp_size-3].c_str())*2000;
        //std::cout<<"Test Linear pin upperBound "<<temp[temp_size-3]<<" "<<atof(temp[temp_size-3].c_str())<<std::endl;
        node.L_Constraints.push_back(temp_LinearConst);
/*
        for(int i=0;i<node.Nets.size();i++){
           if(node.Nets[i].name == temp_LinearConst.net_name){
             for(int j=0;j<node.Nets[i].connected.size();j++){
                for(int k=0;k<temp_LinearConst.pins.size();k++){
                  if(node.Nets[i].connected[j].type == PnRDB::Block && node.Nets[i].connected[j].iter == temp_LinearConst.pins[k].first && node.Nets[i].connected[j].iter2 == temp_LinearConst.pins[k].second){
                    node.Nets[i].connected[j].alpha = temp_LinearConst.alpha[k];
                  }else if(node.Nets[i].connected[j].type == PnRDB::Terminal && temp_LinearConst.pins[k].first==-1 && node.Nets[i].connected[j].iter2 == temp_LinearConst.pins[k].second){
                    node.Nets[i].connected[j].alpha = temp_LinearConst.alpha[k];
                  }
                 }
             }
           }
        }
*/

      }else if(temp[0].compare("Multi_LinearConst")==0){
        //std::cout<<"Enter ML Linear Const"<<std::endl;
        PnRDB::Multi_LinearConst temp_Multi_LinearConst;
        for(unsigned int i=2;i<temp.size()-3;i=i+2){
           PnRDB::LinearConst temp_LinearConst;

           string word=temp[i];
           word=word.substr(1);
           word=word.substr(0, word.length()-1);
           tempsec=StringSplitbyChar(word, ',');
           
           for(unsigned int p=1;p<tempsec.size();p++){
              std::pair<int,int> temp_pin;
              vector<string> pins;
              pins = StringSplitbyChar(tempsec[p], '/');
              if(pins.size()>2){
                 for(unsigned int j=0;j<node.Blocks.size();j++){
                    if(node.Blocks.at(j).instance.back().name.compare(pins[0])==0){
                       for(unsigned int k=0;k<node.Blocks.at(j).instance.back().blockPins.size();k++){
                          if(node.Blocks.at(j).instance.back().blockPins[k].name.compare(pins[1])==0){
                            temp_pin.first = j;
                            temp_pin.second = k;
                            temp_LinearConst.pins.push_back(temp_pin);
                            temp_LinearConst.alpha.push_back(atof(pins[2].c_str()));
                            //std::cout<<"ML Test Linear pin "<<pins[0]<<" "<<pins[1]<<" "<<temp_pin.first<<" "<<temp_pin.second<<" "<<pins[2]<<std::endl;
                            break; 
                         }
                      }
                   }
                }
             }else if(pins.size()==2){
                 for(unsigned int j=0;j<node.Terminals.size();j++){
                    if(node.Terminals.at(j).name.compare(pins[0])==0){
                       temp_pin.first = -1;
                       temp_pin.second = j;
                       temp_LinearConst.pins.push_back(temp_pin);
                       temp_LinearConst.alpha.push_back(atof(pins[2].c_str()));
                       //std::cout<<"ML Test Linear pin "<<pins[0]<<" "<<temp_pin.first<<" "<<temp_pin.second<<" "<<pins[2]<<std::endl;
                       break; 
                   }
                }
             }  
           }

           temp_Multi_LinearConst.Multi_linearConst.push_back(temp_LinearConst);
        }
        int temp_size = temp.size();
        temp_Multi_LinearConst.upperBound = atof(temp[temp_size-3].c_str())*2000;
        node.ML_Constraints.push_back(temp_Multi_LinearConst);
        //std::cout<<"Left ML Linear Const"<<" "<<temp[temp_size-3]<<std::endl;
      }else if (temp[0].compare("Multi_Connection")==0){
        //PnRDB::Multi_Connection temp_multi_connection;
        PnRDB:: Multi_connection temp_multi_Connection;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        //temp_multi_connection.net_name=word;
        string multi_number = temp[4];
        multi_number=multi_number.substr(1);
        multi_number=multi_number.substr(0, word.length()-1);
        //temp_multi_connection.multi_connection = atoi(multi_number.c_str());
        temp_multi_Connection.net_name=word;
        temp_multi_Connection.multi_number=atoi(multi_number.c_str());
        node.Multi_connections.push_back(temp_multi_Connection);
        for(unsigned int j=0;j<node.Nets.size();j++){
           if(node.Nets[j].name==word){
              node.Nets[j].multi_connection = atoi(multi_number.c_str());
            }
        }
      }else if (temp[0].compare("C_Const")==0){
        PnRDB::C_const temp_c_const;
        string word=temp[2];
        word=word.substr(1);
        word=word.substr(0, word.length()-1);
        temp_c_const.net_name=word;

        for(unsigned int i=4;i<temp.size()-1;i+=2){

           word=temp[i];
           word=word.substr(1);
           word=word.substr(0, word.length()-1);
           //cout<<word<<endl;
           tempsec=StringSplitbyChar(word, ',');
           std::pair<int,int> temp_start_pin;
           std::pair<int,int> temp_end_pin;
           vector<string> pins;

           pins = StringSplitbyChar(tempsec[0], '/');
           if(pins.size()>1){
              for(unsigned int j=0;j<node.Blocks.size();j++){
                 if(node.Blocks.at(j).instance.back().name.compare(pins[0])==0){
                    for(unsigned int k=0;k<node.Blocks.at(j).instance.back().blockPins.size();k++){
                       if(node.Blocks.at(j).instance.back().blockPins[k].name.compare(pins[1])==0){
                         temp_start_pin.first = j;
                         temp_start_pin.second = k;
                         temp_c_const.start_pin.push_back(temp_start_pin);
                         //std::cout<<"Test C start pin "<<temp_start_pin.first<<" "<<temp_start_pin.second<<std::endl;
                         break; 
                       }
                    }
                 }
              }
           }else if(pins.size()==1){
              for(unsigned int j=0;j<node.Terminals.size();j++){
                 if(node.Terminals.at(j).name.compare(pins[0])==0){
                    temp_start_pin.first = -1;
                    temp_start_pin.second = j;
                    temp_c_const.start_pin.push_back(temp_start_pin);
                    //std::cout<<"Test C start pin "<<temp_start_pin.first<<" "<<temp_start_pin.second<<std::endl;
                    break; 
                 }
              }
           }

           pins = StringSplitbyChar(tempsec[1], '/');
           if(pins.size()>1){
              for(unsigned int j=0;j<node.Blocks.size();j++){
                 if(node.Blocks.at(j).instance.back().name.compare(pins[0])==0){
                    for(unsigned int k=0;k<node.Blocks.at(j).instance.back().blockPins.size();k++){
                       if(node.Blocks.at(j).instance.back().blockPins[k].name.compare(pins[1])==0){
                         temp_end_pin.first = j;
                         temp_end_pin.second = k;
                         temp_c_const.end_pin.push_back(temp_end_pin);
                         //std::cout<<"Test C end pin "<<temp_end_pin.first<<" "<<temp_end_pin.second<<std::endl;
                         break; 
                       }
                    }
                 }
              }
           }else if(pins.size()==1){
              for(unsigned int j=0;j<node.Terminals.size();j++){
                 if(node.Terminals.at(j).name.compare(pins[0])==0){
                    temp_end_pin.first = -1;
                    temp_end_pin.second = j;
                    temp_c_const.end_pin.push_back(temp_end_pin);
                    //std::cout<<"Test C end pin "<<temp_end_pin.first<<" "<<temp_end_pin.second<<std::endl;
                    break; 
                 }
              }
           }
           temp_c_const.C.push_back(atoi(tempsec[2].c_str()));
        }
        node.C_Constraints.push_back(temp_c_const);
      }
    }
    fin.close();
    //std::cout<<"end read const file "<<cfile<<std::endl;
    return true;
  } catch(ifstream::failure e) {
    //logger->warn("PnRDB-Warn: fail to read constraint file ");
  }
  return false;
}
