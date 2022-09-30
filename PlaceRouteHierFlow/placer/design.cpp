#include "design.h"

#include <cassert>

#include "spdlog/spdlog.h"

std::mt19937_64 design::_rng{0};

design::design() {
  bias_Hgraph = 92;
  bias_Vgraph = 92;
  hasAsymBlock = true;
  hasSymGroup = false;
  mixFlag = false;
  noBlock4Move = 0;
  noAsymBlock4Move = 0;
  noSymGroup4PartMove = 0;
  noSymGroup4FullMove = 0;
}

design::design(PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo, const int seed) {
  auto logger = spdlog::default_logger()->clone("placer.design.design");
  _rng.seed(seed);
  is_first_ILP = node.isFirstILP;
  name = node.name;
  placement_id = node.placement_id;
  bias_Vgraph = node.bias_Vgraph;  // from node
  bias_Hgraph = node.bias_Hgraph;  // from node
  Aspect_Ratio_weight = node.Aspect_Ratio_weight;
  memcpy(Aspect_Ratio, node.Aspect_Ratio, sizeof(node.Aspect_Ratio));
  memcpy(placement_box, node.placement_box, sizeof(node.placement_box));
  Same_Template_Constraints = node.Same_Template_Constraints;
  grid_unit_x = drcInfo.Metal_info[0].grid_unit_x;
  grid_unit_y = drcInfo.Metal_info[1].grid_unit_y;
  mixFlag = false;
  double averageWL = 0;
  double macroThreshold = 0.5;  // threshold to filter out small blocks
  name = node.name;
  // Add blocks
  if (getenv("ALIGN_SKIP_SEQ_PAIR_CACHE") == nullptr || !std::atoi(getenv("ALIGN_SKIP_SEQ_PAIR_CACHE"))) {
    _useCache = true;
  }

  bool offsetpresent{false};
  for (vector<PnRDB::blockComplex>::iterator it = node.Blocks.begin(); it != node.Blocks.end(); ++it) {
    for (int bb = 0; bb < it->instNum; ++bb) {
      if ((it->instance).at(bb).xoffset.size() > 0 || (it->instance).at(bb).yoffset.size() > 0
          || ((it->instance).at(bb).width % drcInfo.Metal_info[0].grid_unit_x != 0)
          || ((it->instance).at(bb).height % drcInfo.Metal_info[1].grid_unit_y != 0)) {
        offsetpresent = true;
        break;
      }
    }
    if (offsetpresent) break;
  }
  for (vector<PnRDB::blockComplex>::iterator it = node.Blocks.begin(); it != node.Blocks.end(); ++it) {
    this->Blocks.resize(this->Blocks.size() + 1);
    int WL = 0;
    for (int bb = 0; bb < it->instNum; ++bb) {
      block tmpblock;
      tmpblock.name = (it->instance).at(bb).name;
      // cout<<tmpblock.name<<endl;
      /*
      for(vector<PnRDB::point>::iterator pit=(it->instance).at(bb).originBox.polygon.begin(); pit!=(it->instance).at(bb).originBox.polygon.end();++pit) {
        placerDB::point tmppoint={pit->x, pit->y};
        tmpblock.boundary.polygon.push_back(tmppoint);
      }
      */
      const auto& pit = (it->instance).at(bb).originBox;
      tmpblock.boundary.polygon.push_back({pit.LL.x, pit.LL.y});
      tmpblock.boundary.polygon.push_back({pit.LL.x, pit.UR.y});
      tmpblock.boundary.polygon.push_back({pit.UR.x, pit.UR.y});
      tmpblock.boundary.polygon.push_back({pit.UR.x, pit.LL.y});

      tmpblock.type = (it->instance).at(bb).type;
      tmpblock.width = (it->instance).at(bb).width;
      tmpblock.height = (it->instance).at(bb).height;
      tmpblock.xoffset = (it->instance).at(bb).xoffset;
      if (offsetpresent && tmpblock.xoffset.size() == 0) tmpblock.xoffset.push_back(0);
      tmpblock.xpitch = (it->instance).at(bb).xpitch;
      if (tmpblock.xpitch == 1) tmpblock.xpitch = drcInfo.Metal_info[0].grid_unit_x;
      tmpblock.xflip = (it->instance).at(bb).xflip;
      tmpblock.yoffset = (it->instance).at(bb).yoffset;
      if (offsetpresent && tmpblock.yoffset.size() == 0) tmpblock.yoffset.push_back(0);
      tmpblock.ypitch = (it->instance).at(bb).ypitch;
      if (tmpblock.ypitch == 1) tmpblock.ypitch = drcInfo.Metal_info[1].grid_unit_y;
      tmpblock.yflip = (it->instance).at(bb).yflip;
      // cout<<tmpblock.height<<endl;
      // [wbxu] Following lines have be updated to support multi contacts
      for (vector<PnRDB::pin>::iterator pit = (it->instance).at(bb).blockPins.begin(); pit != (it->instance).at(bb).blockPins.end(); ++pit) {
        block::pin tmppin;
        placerDB::point tpoint;
        tmppin.name = pit->name;
        tmppin.type = pit->type;
        tmppin.netIter = pit->netIter;
        // cout<<tmppin.name<<endl;
        tmppin.bbox = PnRDB::bbox(INT_MAX, INT_MAX, INT_MIN, INT_MIN);
        for (vector<PnRDB::contact>::iterator cit = pit->pinContacts.begin(); cit != pit->pinContacts.end(); ++cit) {
          tpoint = {cit->originCenter.x, cit->originCenter.y};
          tmppin.center.push_back(tpoint);
          tmppin.boundary.resize(tmppin.boundary.size() + 1);
          /*
          for(vector<PnRDB::point>::iterator qit=cit->originBox.polygon.begin(); qit!=cit->originBox.polygon.end(); ++qit) {
            tpoint={qit->x, qit->y};
            tmppin.boundary.back().polygon.push_back(tpoint);
          }
          */
          const auto& qit = cit->originBox;
          tmppin.boundary.back().polygon.push_back({qit.LL.x, qit.LL.y});
          tmppin.boundary.back().polygon.push_back({qit.LL.x, qit.UR.y});
          tmppin.boundary.back().polygon.push_back({qit.UR.x, qit.UR.y});
          tmppin.boundary.back().polygon.push_back({qit.UR.x, qit.LL.y});
          tmppin.bbox.LL.x = std::min(tmppin.bbox.LL.x, qit.LL.x);
          tmppin.bbox.LL.y = std::min(tmppin.bbox.LL.y, qit.LL.y);
          tmppin.bbox.UR.x = std::max(tmppin.bbox.UR.x, qit.UR.x);
          tmppin.bbox.UR.y = std::max(tmppin.bbox.UR.y, qit.UR.y);
        }
        tmpblock.blockPins.push_back(tmppin);
      }
      this->Blocks.back().push_back(tmpblock);
      if (WL < tmpblock.height + tmpblock.width) {
        WL = tmpblock.height + tmpblock.width;
      }
    }
    // it->instance.
    averageWL += WL;
    // averageWL+=(this->Blocks.back().width+this->Blocks.back().height);
  }
  averageWL /= this->Blocks.size();
  averageWL *= macroThreshold;
  for (std::vector<std::vector<block>>::iterator oit = this->Blocks.begin(); oit != this->Blocks.end(); ++oit) {
    int WL = 0;
    for (std::vector<block>::iterator it = oit->begin(); it != oit->end(); ++it) {
      if (it->width + it->height > WL) {
        WL = it->width + it->height;
      }
    }
    for (std::vector<block>::iterator it = oit->begin(); it != oit->end(); ++it) {
      if (WL < averageWL) {
        it->bigMacro = false;
      } else {
        it->bigMacro = true;
      }
    }
  }
  // Add terminals
  for (vector<PnRDB::terminal>::iterator it = node.Terminals.begin(); it != node.Terminals.end(); ++it) {
    terminal tmpter;
    tmpter.name = it->name;
    tmpter.netIter = it->netIter;
    this->Terminals.push_back(tmpter);
  }
  // Add nets
  for (vector<PnRDB::net>::iterator it = node.Nets.begin(); it != node.Nets.end(); ++it) {
    placerDB::net tmpnet;
    tmpnet.name = it->name;
    tmpnet.priority = it->priority;
    tmpnet.weight = it->weight;
    tmpnet.upperBound = it->upperBound;
    tmpnet.lowerBound = it->lowerBound;
    bool floating_pin = true;
    for (vector<PnRDB::connectNode>::iterator nit = it->connected.begin(); nit != it->connected.end(); ++nit) {
      placerDB::NType tmptype = placerDB::Block;
      if (nit->type == PnRDB::Block) {
        tmptype = placerDB::Block;
        if (Blocks[nit->iter2][0].blockPins[nit->iter].center.size()) floating_pin = false;
      } else if (nit->type == PnRDB::Terminal) {
        tmptype = placerDB::Terminal;
      } else {
        logger->error("Placer-Error: incorrect connected node type");
        assert(0);
      }
      placerDB::Node tmpnode = {tmptype, nit->iter, nit->iter2, nit->alpha};
      tmpnet.connected.push_back(tmpnode);
    }
    if (floating_pin == true) tmpnet.floating_pin = true;
    this->Nets.push_back(tmpnet);
  }

  // Add symmetry block constraint, axis direction is determined by user
  for (vector<PnRDB::SymmPairBlock>::iterator it = node.SPBlocks.begin(); it != node.SPBlocks.end(); ++it) {
    this->SPBlocks.resize(SPBlocks.size() + 1);
    // vector< pair<int,int> > sympair;
    // vector< pair<int,placerDB::Smark> > selfsym;
    for (vector<pair<int, int>>::iterator sit = it->sympair.begin(); sit != it->sympair.end(); ++sit) {
      this->SPBlocks.back().sympair.push_back(make_pair(sit->first, sit->second));
    }
    for (vector<pair<int, PnRDB::Smark>>::iterator sit = it->selfsym.begin(); sit != it->selfsym.end(); ++sit) {
      placerDB::Smark axis;
      if (sit->second == PnRDB::H) {
        axis = placerDB::H;
      } else if (sit->second == PnRDB::V) {
        axis = placerDB::V;
      } else {
        logger->debug("Placer-Error: incorrect Smark");
        continue;
      }
      this->SPBlocks.back().selfsym.push_back(make_pair(sit->first, axis));
    }
    // added by YG: 10/22/2020
    if (it->axis_dir == PnRDB::H) {
      this->SPBlocks.back().axis_dir = placerDB::H;
    } else if (it->axis_dir == PnRDB::V) {
      this->SPBlocks.back().axis_dir = placerDB::V;
    }
    // end add
  }
  // Add symmetry net constraints
  for (vector<PnRDB::SymmNet>::iterator it = node.SNets.begin(); it != node.SNets.end(); ++it) {
    placerDB::net tmpnet1, tmpnet2;
    tmpnet1.name = it->net1.name;
    // tmpnet1.priority=it->net1.priority;
    for (vector<PnRDB::connectNode>::iterator nit = it->net1.connected.begin(); nit != it->net1.connected.end(); ++nit) {
      placerDB::NType tmptype = placerDB::Block;
      if (nit->type == PnRDB::Block) {
        tmptype = placerDB::Block;
      } else if (nit->type == PnRDB::Terminal) {
        tmptype = placerDB::Terminal;
      } else {
        logger->error("Placer-Error: incorrect connected node type");
        assert(0);
      }
      placerDB::Node tmpnode = {tmptype, nit->iter, nit->iter2};
      tmpnet1.connected.push_back(tmpnode);
    }
    tmpnet2.name = it->net2.name;
    // tmpnet2.priority=it->net2.priority;
    for (vector<PnRDB::connectNode>::iterator nit = it->net2.connected.begin(); nit != it->net2.connected.end(); ++nit) {
      placerDB::NType tmptype = placerDB::Block;
      if (nit->type == PnRDB::Block) {
        tmptype = placerDB::Block;
      } else if (nit->type == PnRDB::Terminal) {
        tmptype = placerDB::Terminal;
      } else {
        logger->error("Placer-Error: incorrect connected node type");
        assert(0);
      }
      placerDB::Node tmpnode = {tmptype, nit->iter, nit->iter2};
      tmpnet2.connected.push_back(tmpnode);
    }
    SymmNet tmpsnet;
    tmpsnet.net1 = tmpnet1;
    tmpsnet.net2 = tmpnet2;
    if (it->axis_dir == PnRDB::H) {
      tmpsnet.axis_dir = placerDB::H;
    } else if (it->axis_dir == PnRDB::V) {
      tmpsnet.axis_dir = placerDB::V;
    }

    this->SNets.push_back(tmpsnet);
    // cout<<"# " <<this->SNets.size()<<endl;
  }
  // Add preplace block constraint
  for (vector<PnRDB::Preplace>::iterator it = node.Preplace_blocks.begin(); it != node.Preplace_blocks.end(); ++it) {
    this->Preplace_blocks.resize(this->Preplace_blocks.size() + 1);
    this->Preplace_blocks.back().blockid1 = it->blockid1;
    this->Preplace_blocks.back().blockid2 = it->blockid2;
    this->Preplace_blocks.back().conner = it->conner;
    this->Preplace_blocks.back().distance = it->distance;
    this->Preplace_blocks.back().horizon = it->horizon;
  }
  // Add aligned block constraint
  for (vector<PnRDB::Alignment>::iterator it = node.Alignment_blocks.begin(); it != node.Alignment_blocks.end(); ++it) {
    this->Alignment_blocks.resize(this->Alignment_blocks.size() + 1);
    this->Alignment_blocks.back().blockid1 = it->blockid1;
    this->Alignment_blocks.back().blockid2 = it->blockid2;
    this->Alignment_blocks.back().distance = it->distance;
    this->Alignment_blocks.back().horizon = it->horizon;
  }
  // Add abutted block constraint
  for (vector<PnRDB::Abument>::iterator it = node.Abument_blocks.begin(); it != node.Abument_blocks.end(); ++it) {
    this->Abument_blocks.resize(this->Abument_blocks.size() + 1);
    this->Abument_blocks.back().blockid1 = it->blockid1;
    this->Abument_blocks.back().blockid2 = it->blockid2;
    this->Abument_blocks.back().distance = it->distance;
    this->Abument_blocks.back().horizon = it->horizon;
  }
  // Add matched block constraint
  for (vector<PnRDB::MatchBlock>::iterator it = node.Match_blocks.begin(); it != node.Match_blocks.end(); ++it) {
    this->Match_blocks.resize(this->Match_blocks.size() + 1);
    this->Match_blocks.back().blockid1 = it->blockid1;
    this->Match_blocks.back().blockid2 = it->blockid2;
  }
  // Add align block constraint
  for (vector<PnRDB::AlignBlock>::iterator it = node.Align_blocks.begin(); it != node.Align_blocks.end(); ++it) {
    this->Align_blocks.resize(this->Align_blocks.size() + 1);
    this->Align_blocks.back().horizon = it->horizon;
    this->Align_blocks.back().line = it->line;
    for (std::vector<int>::iterator it2 = it->blocks.begin(); it2 != it->blocks.end(); ++it2) {
      this->Align_blocks.back().blocks.push_back(*it2);
    }
  }
  // Add port location constraint
  for (vector<PnRDB::PortPos>::iterator it = node.Port_Location.begin(); it != node.Port_Location.end(); ++it) {
    this->Port_Location.resize(this->Port_Location.size() + 1);
    this->Port_Location.back().tid = it->tid;
    this->Port_Location.back().pos = placerDB::Bmark(it->pos);
  }
  // Add spread constraints
  for (const auto& it : node.SpreadConstraints) {
    for (auto itb1 = it.blocks.begin(); itb1 != it.blocks.end(); ++itb1) {
      for (auto itb2 = std::next(itb1); itb2 != it.blocks.end(); ++itb2) {
        if (it.horizon) {
          hSpread[std::make_pair(*itb1, *itb2)] = it.distance;
        } else {
          vSpread[std::make_pair(*itb1, *itb2)] = it.distance;
        }
      }
    }
  }
  constructSymmGroup();
  this->ML_Constraints = node.ML_Constraints;
  for (const auto& order : node.Ordering_Constraints) {
    for (unsigned int i = 0; i < order.first.size() - 1; i++) {
      Ordering_Constraints.push_back(make_pair(make_pair(order.first[i], order.first[i + 1]), order.second == PnRDB::H ? placerDB::H : placerDB::V));
      if (Blocks[order.first[i]][0].counterpart != -1 && Blocks[order.first[i]][0].counterpart != order.first[i] &&
          Blocks[order.first[i + 1]][0].counterpart != order.first[i] && order.second == PnRDB::V)
        Ordering_Constraints.push_back(
            make_pair(make_pair(Blocks[order.first[i]][0].counterpart, order.first[i + 1]), order.second == PnRDB::H ? placerDB::H : placerDB::V));
      if (Blocks[order.first[i + 1]][0].counterpart != -1 && Blocks[order.first[i + 1]][0].counterpart != order.first[i + 1] &&
          Blocks[order.first[i + 1]][0].counterpart != order.first[i] && order.second == PnRDB::V)
        Ordering_Constraints.push_back(
            make_pair(make_pair(order.first[i], Blocks[order.first[i + 1]][0].counterpart), order.second == PnRDB::H ? placerDB::H : placerDB::V));
      if (Blocks[order.first[i]][0].counterpart != -1 && Blocks[order.first[i + 1]][0].counterpart != -1 &&
          Blocks[order.first[i]][0].counterpart != order.first[i] && Blocks[order.first[i + 1]][0].counterpart != order.first[i + 1] &&
          Blocks[order.first[i + 1]][0].counterpart != order.first[i] && order.second == PnRDB::V)
        Ordering_Constraints.push_back(make_pair(make_pair(Blocks[order.first[i]][0].counterpart, Blocks[order.first[i + 1]][0].counterpart),
                                                 order.second == PnRDB::H ? placerDB::H : placerDB::V));
      if (order.second == PnRDB::V) {
        for (const auto& al : node.Align_blocks) {
          if (al.horizon == 1 && find(al.blocks.begin(), al.blocks.end(), order.first[i]) != al.blocks.end()) {
            for (auto b : al.blocks) {
              if (b != order.first[i] && Blocks[order.first[i]][0].height >= Blocks[b][0].height) {
                Ordering_Constraints.push_back(make_pair(make_pair(b, order.first[i + 1]), order.second == PnRDB::H ? placerDB::H : placerDB::V));
              }
            }
          }
          if (al.horizon == 1 && find(al.blocks.begin(), al.blocks.end(), order.first[i+1]) != al.blocks.end()) {
            for (auto b : al.blocks) {
              if (b != order.first[i+1] && Blocks[order.first[i+1]][0].height >= Blocks[b][0].height) {
                Ordering_Constraints.push_back(make_pair(make_pair(order.first[i], b), order.second == PnRDB::H ? placerDB::H : placerDB::V));
              }
            }
          }
        }
      }
    }
  }
  for (const auto& abut : node.Abut_Constraints) {
    for (unsigned int i = 0; i < abut.first.size() - 1; i++) {
      Abut_Constraints.push_back(make_pair(make_pair(abut.first[i], abut.first[i + 1]), abut.second == PnRDB::H ? placerDB::H : placerDB::V));
    }
  }

  // PrintDesign();
  // std::cout<<"Leaving design2\n";
  hasAsymBlock = checkAsymmetricBlockExist();
  // std::cout<<"Leaving design\n";
  hasSymGroup = (not SBlocks.empty());
  noBlock4Move = GetSizeBlock4Move(1);
  noAsymBlock4Move = GetSizeAsymBlock4Move(1);
  noSymGroup4FullMove = GetSizeSymGroup4FullMove(1);
  noSymGroup4PartMove = noSymGroup4FullMove;
  // std::cout<<"Leaving design\n";
  // if (getenv("ALIGN_DEBUG_SEQ_PAIR") != nullptr && std::atoi(getenv("ALIGN_DEBUG_SEQ_PAIR"))) {
  //  _debugofs.open(name + ".seq_pair_dbg.data");
  //}
  int szmax{(int)Blocks.size() + (int)SBlocks.size()};
  for (auto& it : Blocks) {
    szmax = std::max((int)it.size(), szmax);
  }

  _rnd = new std::uniform_int_distribution<int>(0, std::max(20, 2 * szmax));
  if (node.compact_style == "left") {
    compact_style = CompactStyle::L;
  } else if (node.compact_style == "right") {
    compact_style = CompactStyle::R;
  } else {
    compact_style = CompactStyle::C;
  }
  maxBlockAreaSum = 0.;
  for (unsigned i = 0; i < Blocks.size(); i++) {
    double area = 0;
    for (unsigned j = 0; j < Blocks[i].size(); ++j) {
      double jarea = double(Blocks[i][j].width) * double(Blocks[i][j].height);
      if (area < jarea) area = jarea;
    }
    maxBlockAreaSum += area;
  }
  maxBlockHPWLSum = 0.;
  for (unsigned i = 0; i < Blocks.size(); i++) {
    double width = 0, height = 0;
    for (unsigned j = 0; j < Blocks[i].size(); ++j) {
      if (width < Blocks[i][j].width) {
        width = Blocks[i][j].width;
      }
      if (height < Blocks[i][j].height) {
        height = Blocks[i][j].height;
      }
    }
    maxBlockHPWLSum += (width + height);
  }
  std::map<std::string, std::pair<int, int> > pinName2Index;
  if (!node.CFValues.empty()) {
    CFdist_type = node.CFdist_type;
    for (auto& net : Nets) {
      if (node.CFValues.find(net.name) == node.CFValues.end()) continue;
      for (auto& conn : net.connected) {
        if (conn.type == placerDB::Block) {
          if (Blocks[conn.iter2].size() > 0 && Blocks[conn.iter2][0].blockPins.size() > conn.iter) {
            pinName2Index[Blocks[conn.iter2][0].name + '/' + Blocks[conn.iter2][0].blockPins[conn.iter].name] = std::make_pair(conn.iter2, conn.iter);
          }
        }
      }
    }

    for (auto& it : node.CFValues) {
      for (int i = 0; i < (int)Nets.size(); ++i) {
        auto cfit = CFValues.find(Nets[i].name);
        if (cfit == CFValues.end() && Nets[i].name == it.first) {
          for (auto& pp : it.second) {
            auto itp1 = pinName2Index.find(std::get<0>(pp));
            auto itp2 = pinName2Index.find(std::get<1>(pp));
            if (itp1 != pinName2Index.end() && itp2 != pinName2Index.end()) {
              CFValues[Nets[i].name][std::make_tuple(itp1->second.first, itp1->second.second,
                  itp2->second.first, itp2->second.second)] = std::get<2>(pp);
            }
          }
        }
      }
    }
  }
}

int design::rand() {
  if (_rnd) return (*_rnd)(_rng);
  return rand();
}

int design::GetSizeBlock4Move(int mode) {
  // mode-0: check mapIdx for original design
  // mode-1: never check mapIdx for reduced design
  if (mode == 0) {
    int ss = 0;
    for (unsigned int i = 0; i < this->Blocks.size(); ++i) {
      if (this->Blocks.at(i).back().mapIdx == -1) {
        ss++;
      }
    }
    return ss;
  } else {
    return (this->Blocks.size());
  }
}

int design::GetSizeAsymBlock4Move(int mode) {
  // mode-0: check mapIdx for original design
  // mode-1: never check mapIdx for reduced design
  int ss = 0;
  for (unsigned int i = 0; i < this->Blocks.size(); ++i) {
    if (mode == 0) {
      if (this->Blocks.at(i).back().mapIdx == -1 && this->Blocks.at(i).back().SBidx == -1) {
        ss++;
      }
    } else {
      if (this->Blocks.at(i).back().SBidx == -1) {
        ss++;
      }
    }
  }
  return ss;
}

int design::GetSizeSymGroup4FullMove(int mode) {
  // mode-0: check mapIdx of groups for original design
  // mode-1: never check mapIdx for reduced design
  int ss = 0;
  if (mode == 0) {
    for (unsigned int i = 0; i < this->SBlocks.size(); ++i) {
      if (this->SBlocks.at(i).mapIdx == -1) {
        ss++;
      }
    }
  } else {
    ss = this->SBlocks.size();
  }
  return ss;
}

int design::GetSizeofBlocks() { return Blocks.size(); }

int design::GetSizeofTerminals() { return Terminals.size(); }

int design::GetSizeofSBlocks() { return SBlocks.size(); }

// design::design(string blockfile, string netfile) {
//  bias_Vgraph=92;
//  bias_Hgraph=92;
//  readBlockFile(blockfile);
//  readNetFile(netfile);
//  hasAsymBlock=checkAsymmetricBlockExist();
//  hasSymGroup=(not SBlocks.empty());
//  mixFlag=false;
//}

/*
design::design(string blockfile, string netfile, string cfile) {
  bias_graph=100;
  readBlockFile(blockfile);
  readNetFile(netfile);
  readConstFile(cfile);
  constructSymmGroup();
  hasAsymBlock=checkAsymmetricBlockExist();
  hasSymGroup=(not SBlocks.empty());
}
*/
// added by yg
// design::design(string blockfile, string netfile, string cfile) {
//  bias_Hgraph=92;
//  bias_Vgraph=92;
//  mixFlag=false;
//  readBlockFile(blockfile);
//  readNetFile(netfile);
//  readConstFile(cfile);
//  constructSymmGroup();
//  hasAsymBlock=checkAsymmetricBlockExist();
//  hasSymGroup=(not SBlocks.empty());
//}

// design::design(string blockfile, string netfile, string cfile, string random_cfile) {
//  bias_Hgraph=92;
//  bias_Vgraph=92;
//  mixFlag=false;
//  readBlockFile(blockfile);
//  readNetFile(netfile);
//  readConstFile(cfile);
//  constructSymmGroup();
//  hasAsymBlock=checkAsymmetricBlockExist();
//  hasSymGroup=(not SBlocks.empty());
//}

// design::design(string blockfile, string netfile, string cfile, string random_const_file, int write_out_flag) {
//  bias_Vgraph=92;
//  bias_Hgraph=92;
//  mixFlag=false;
//  readBlockFile(blockfile);
//  readNetFile(netfile);
//  readConstFile(cfile);
//  hasAsymBlock=checkAsymmetricBlockExist();
//  hasSymGroup=(not SBlocks.empty());
//}

//

// void design::readNetFile(string netfile) {
//  ifstream fin;
//  string def;
//  fin.open(netfile.c_str());
//
//  vector<string> temp;
//  size_t found;
//
//  int *p=0;
//  int p_temp=0;
//  p=&p_temp;
//
//  int netNo, pinNo;
//  while(!fin.eof()) {
//    getline(fin, def);
//    if((found=def.find("NumNets"))!=string::npos) {
//      temp=get_true_word(found,def,0,';',p);
//      netNo=stoi(temp[2]);
//      break;
//    }
//  }
//
//  while(!fin.eof()) {
//    getline(fin, def);
//    if((found=def.find("NumPins"))!=string::npos) {
//      temp=get_true_word(found,def,0,';',p);
//      pinNo=stoi(temp[2]);
//      break;
//    }
//  }
//  cout<<"Placer-Info: reading "<<netNo<<" nets and "<<pinNo<<" pins ..."<<endl;
//  while(!fin.eof()) {
//    getline(fin,def);
//    if((found=def.find(":"))!=string::npos) {
//      temp=split_by_spaces(def);
//      string netname=temp[0];
//      int dno=stoi(temp[2]);
//      vector<placerDB::Node> tmpNlist;
//      //cout<<netname<<" "<<temp[2]<<endl;
//      for(int i=0;i<dno;++i) {
//        getline(fin,def);
//        temp=split_by_spaces(def);
//        placerDB::Node tmpNode;
//        bool mark=false;
//        if(temp[0].compare("terminal")==0) {
//          for(int k=0;k<(int)Terminals.size(); ++k) {
//            if(mark) {break;}
//            if(Terminals.at(k).name.compare(temp[1])==0) {
//              tmpNode.type=placerDB::Terminal;
//              tmpNode.iter=k;
//              tmpNode.iter2=-1;
//              Terminals.at(k).netIter=(int)Nets.size();
//              mark=true;
//            }
//          }
//        } else {
//          for(int k=0;k<(int)Blocks.size(); ++k) {
//            if(mark) {break;}
//            if(Blocks.at(k).back().name.compare(temp[0])==0) {
//              for(int j=0;j<(int)Blocks.at(k).back().blockPins.size();++j) {
//                if(mark) {break;}
//                if(Blocks.at(k).back().blockPins.at(j).name.compare(temp[1])==0) {
//                  tmpNode.type=placerDB::Block;
//                  tmpNode.iter=j;
//                  tmpNode.iter2=k;
//                  Blocks.at(k).back().blockPins.at(j).netIter=(int)Nets.size();
//                  mark=true;
//                }
//              }
//            }
//          }
//        }
//        tmpNlist.push_back(tmpNode);
//        //cout<<def<<endl;
//      }
//      Nets.resize(Nets.size()+1);
//      Nets.back().connected=tmpNlist;
//      Nets.back().name=netname;
//    }
//  }
//}

// void design::readBlockFile(string blockfile) {
//  ifstream fin;
//  string def;
//  fin.open(blockfile.c_str());
//
//  vector<string> temp, tempsec;
//  size_t found;
//
//  int *p=0;
//  int p_temp=0;
//  p=&p_temp;
//
//  placerDB::point p1,p2,p3,p4;
//  int blockNo=0, terminalNo=0;
//  while(!fin.eof()) {
//    getline(fin, def);
//    if((found=def.find("NumHardRectilinearBlocks"))!=string::npos) {
//      temp=get_true_word(found,def,0,';',p);
//      blockNo=stoi(temp[2]);
//      break;
//    }
//  }
//
//  while(!fin.eof()) {
//    getline(fin, def);
//    if((found=def.find("NumTerminals"))!=string::npos) {
//      temp=get_true_word(found,def,0,';',p);
//      terminalNo=stoi(temp[2]);
//      break;
//    }
//  }
//  cout<<"Placer-Info: reading "<<blockNo<<" blocks and "<<terminalNo<<" terminals ..."<<endl;
//  getline(fin, def);
//  for(int i=0;i<blockNo;++i) {
//    getline(fin, def);
//    //cout<<i<<"-"<<def;
//    temp=split_by_spaces(def);
//    block tmpblock;
//    tmpblock.SBidx=-1;
//    tmpblock.counterpart=-1;
//    tmpblock.name=temp[0];
//    tmpblock.type=temp[1];
//    found=def.find("(");
//    temp=get_true_word(found,def,0,';',p);
//    //int width, height;
//    p1.x=stoi(temp[0].substr(1,temp[0].length()-2)); p1.y=stoi(temp[1].substr(0,temp[1].length()-1));
//    p2.x=stoi(temp[2].substr(1,temp[2].length()-2)); p2.y=stoi(temp[3].substr(0,temp[3].length()-1));
//    p3.x=stoi(temp[4].substr(1,temp[4].length()-2)); p3.y=stoi(temp[5].substr(0,temp[5].length()-1));
//    p4.x=stoi(temp[6].substr(1,temp[6].length()-2)); p4.y=stoi(temp[7].substr(0,temp[7].length()-1));
//    tmpblock.width=abs(p3.x-p1.x);
//    tmpblock.height=abs(p2.y-p1.y);
//    tmpblock.boundary.polygon.push_back(p1);
//    tmpblock.boundary.polygon.push_back(p2);
//    tmpblock.boundary.polygon.push_back(p3);
//    tmpblock.boundary.polygon.push_back(p4);
//    //tmpblock.blockPins.resize(tmpblock.blockPins.size()+1);
//    //tmpblock.blockPins.back().name="B";
//    Blocks.push_back(tmpblock);
//    //cout<<p1.x<<p1.y<<p2.x<<p2.y<<p3.x<<p3.y<<p4.x<<p4.y<<endl;
//    //cout<<temp[0]<<endl;
//  }
//  //cout<<"end"<<endl;
//  while(!fin.eof()) {
//    getline(fin, def);
//    if((found=def.find("BLOCK"))!=string::npos) {
//      temp=split_by_spaces(def);
//      //cout<<temp[1]<<" "<<temp[temp.size()-2]<<endl;
//      int bi;
//      int pno=stoi(temp[temp.size()-2]);
//      string target=temp[1];
//      for(bi=0;bi<(int)Blocks.size();++bi) {
//        if(Blocks.at(bi).name.compare(target)==0) { break; }
//      }
//      for(int i=0;i<pno;++i) {
//        getline(fin, def);
//        if((found=def.find("INT"))==string::npos) {
//          tempsec=split_by_spaces(def);
//          //cout<<def<<endl;
//          p1.x=stoi(tempsec[2].substr(1,tempsec[2].length()-2)); p1.y=stoi(tempsec[3].substr(0,tempsec[3].length()-1));
//          p2.x=stoi(tempsec[4].substr(1,tempsec[4].length()-2)); p2.y=stoi(tempsec[5].substr(0,tempsec[5].length()-1));
//          p3.x=stoi(tempsec[6].substr(1,tempsec[6].length()-2)); p3.y=stoi(tempsec[7].substr(0,tempsec[7].length()-1));
//          p4.x=stoi(tempsec[8].substr(1,tempsec[8].length()-2)); p4.y=stoi(tempsec[9].substr(0,tempsec[9].length()-1));
//          //cout<<tempsec[0]<<" "<<tempsec[1]<<" "<<p1.x<<","<<p1.y<<" "<<p2.x<<","<<p2.y<<" "<<p3.x<<","<<p3.y<<" "<<p4.x<<","<<p4.y<<endl;
//          Blocks.at(bi).blockPins.resize(Blocks.at(bi).blockPins.size()+1);
//          Blocks.at(bi).blockPins.back().name=tempsec[0];
//          Blocks.at(bi).blockPins.back().center.resize(Blocks.at(bi).blockPins.back().center.size()+1);
//          Blocks.at(bi).blockPins.back().center.back().x=(p3.x+p1.x)/2;
//          Blocks.at(bi).blockPins.back().center.back().y=(p2.y+p1.y)/2;
//          Blocks.at(bi).blockPins.back().boundary.resize(Blocks.at(bi).blockPins.back().boundary.size()+1);
//          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p1);
//          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p2);
//          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p3);
//          Blocks.at(bi).blockPins.back().boundary.back().polygon.push_back(p4);
//        }
//      }
//    }
//    if((found=def.find("terminal"))!=string::npos) {
//      for(int i=0;i<terminalNo;++i) {
//        temp=split_by_spaces(def);
//        terminal tmpterm;
//        tmpterm.name=temp[0];
//        Terminals.push_back(tmpterm);
//        //cout<<tmpterm.name<<endl;
//        getline(fin, def);
//      }
//    //  break;
//    }
//  }
//
//}

// void design::readConstFile(string cfile) {
//  ifstream fin;
//  string def;
//  fin.open(cfile.c_str());
//
//  vector<string> temp, tempsec;
//  size_t found;
//
//  int *p=0;
//  int p_temp=0;
//  p=&p_temp;
//
//  while(!fin.eof()) {
//    getline(fin, def);
//    temp=split_by_spaces(def);
//    if(temp[0].compare("SymmNet")==0) {
//      string word=temp[2];
//      word=word.substr(1);
//      word=word.substr(0, word.length()-1);
//      //cout<<word<<endl;
//      tempsec=StringSplitbyChar(word, ',');
//      //cout<<tempsec[0]<<" "<<tempsec[1]<<endl;
//      placerDB::net tmpnet;
//      for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); ++it) {
//        if(it==tempsec.begin()) {
//          tmpnet.name=*it;
//        } else {
//          if(it->find("/")!=string::npos) {
//            vector<string> tempthd=StringSplitbyChar(*it, '/');
//            for(int i=0;i<(int)Blocks.size();++i) {
//              if(Blocks.at(i).name.compare(tempthd[0])==0) {
//                for(int j=0;j<(int)Blocks.at(i).blockPins.size();++j) {
//                  if(Blocks.at(i).blockPins.at(j).name.compare(tempthd[1])==0) {
//                    //cout<<j<<i<<endl;
//                    placerDB::Node newnode={placerDB::Block, j, i};
//                    tmpnet.connected.push_back(newnode);
//                    break;
//                  }
//                }
//                break;
//              }
//            }
//            //cout<<*it<<" is pin"<<tempthd[0]<<tempthd[1]<<endl;
//          } else {
//            for(int i=0;i<(int)Terminals.size();++i) {
//              if(Terminals.at(i).name.compare(*it)==0) {
//                placerDB::Node newnode={placerDB::Terminal, i, -1};
//                tmpnet.connected.push_back(newnode);
//                break;
//              }
//            }
//            //cout<<*it<<" is terminal"<<endl;
//          }
//        }
//      }
//      word=temp[4];
//      word=word.substr(1);
//      word=word.substr(0, word.length()-1);
//      tempsec=StringSplitbyChar(word, ',');
//      placerDB::net tmpnet2;
//      for(vector<string>::iterator it=tempsec.begin(); it!=tempsec.end(); ++it) {
//        if(it==tempsec.begin()) {
//          tmpnet2.name=*it;
//        } else {
//          if(it->find("/")!=string::npos) {
//            vector<string> tempthd=StringSplitbyChar(*it, '/');
//            for(int i=0;i<(int)Blocks.size();++i) {
//              if(Blocks.at(i).name.compare(tempthd[0])==0) {
//                for(int j=0;j<(int)Blocks.at(i).blockPins.size();++j) {
//                  if(Blocks.at(i).blockPins.at(j).name.compare(tempthd[1])==0) {
//                    //cout<<j<<i<<endl;
//                    placerDB::Node newnode={placerDB::Block, j, i};
//                    tmpnet2.connected.push_back(newnode);
//                    break;
//                  }
//                }
//                break;
//              }
//            }
//            //cout<<*it<<" is pin"<<tempthd[0]<<tempthd[1]<<endl;
//          } else {
//            for(int i=0;i<(int)Terminals.size();++i) {
//              if(Terminals.at(i).name.compare(*it)==0) {
//                placerDB::Node newnode={placerDB::Terminal, i, -1};
//                tmpnet2.connected.push_back(newnode);
//                break;
//              }
//            }
//            //cout<<*it<<" is terminal"<<endl;
//          }
//        }
//      }
//      SNets.resize(SNets.size()+1);
//      SNets.back().net1=tmpnet;
//      SNets.back().net2=tmpnet2;
//    } else if (temp[0].compare("CritNet")==0) {
//      for(int i=0;i<(int)Nets.size();++i) {
//        if(Nets.at(i).name.compare(temp[2])==0) {
//          Nets.at(i).priority=temp[4];
//          break;
//        }
//      }
//    }
//  }
//}

void design::PrintDesign() {
  auto logger = spdlog::default_logger()->clone("placer.design.PrintDesign");

  logger->debug("== Print Design ");
  logger->debug("bias_Vgraph: {0} mixFlag: {1}", bias_Vgraph, mixFlag);
  logger->debug("bias_Hgraph: {0} mixFlag: {1}", bias_Hgraph, mixFlag);
  // PrintBlocks();
  PrintTerminals();
  PrintNets();
  PrintConstraints();
  PrintSymmGroup();
  // std::cout<<"symmetry group size "<<SPBlocks.size()<<std::endl;
  for (unsigned int i = 0; i < SNets.size(); ++i) {
    logger->debug("Symmetry net {0} SBidx {1}", i, SNets.at(i).SBidx);
  }
  for (unsigned int i = 0; i < Port_Location.size(); ++i) {
    logger->debug("Port location {0} @ {1}", Port_Location.at(i).tid, Port_Location.at(i).pos);
  }
}

void design::PrintSymmGroup() {
  auto logger = spdlog::default_logger()->clone("placer.design.PrintSymmGroup");

  logger->debug("=== Symmetric Groups ===");
  for (vector<placerDB::SymmBlock>::iterator si = SBlocks.begin(); si != SBlocks.end(); ++si) {
    logger->debug("Group node: {0} mapIdx {1}", si->dnode, si->mapIdx);
    for (vector<pair<int, int>>::iterator pi = si->sympair.begin(); pi != si->sympair.end(); ++pi) {
      logger->debug("symmetric pair {0} vs {1}", pi->first, pi->second);
    }
    for (vector<pair<int, placerDB::Smark>>::iterator pi = si->selfsym.begin(); pi != si->selfsym.end(); ++pi) {
      logger->debug("self-symmetric {0} at {1}", pi->first, pi->second);
    }
  }
}

void design::PrintBlocks() {
  auto logger = spdlog::default_logger()->clone("placer.design.PrintBlocks");

  logger->debug("=== Blocks ===");
  for (std::vector<std::vector<block>>::iterator oit = Blocks.begin(); oit != Blocks.end(); ++oit) {
    logger->debug("Block idx {0}", oit - Blocks.begin());
    for (vector<block>::iterator it = oit->begin(); it != oit->end(); ++it) {
      logger->debug("Choice {0} Name {1} SBidx {2} counterpart {3} macro {4} mapIdx {5}", it - oit->begin(), (*it).name, it->SBidx, it->counterpart,
                    it->bigMacro, it->mapIdx);
      logger->debug("type {0} width {1} heigt {2} bbox", (*it).type, (*it).width, (*it).height);
      for (vector<placerDB::point>::iterator it2 = (*it).boundary.polygon.begin(); it2 != (*it).boundary.polygon.end(); ++it2) {
        logger->debug("{0} {1}", (*it2).x, (*it2).y);
      }
      // cout<<endl;
      for (vector<block::pin>::iterator it3 = it->blockPins.begin(); it3 != it->blockPins.end(); ++it3) {
        logger->debug("Pin {0} net {1} center", it3->name, it3->netIter);
        for (vector<placerDB::point>::iterator it4 = it3->center.begin(); it4 != it3->center.end(); ++it4) {
          logger->debug("{0} {1}", it4->x, it4->y);
        }
        logger->debug("bbox");
        for (vector<placerDB::bbox>::iterator it5 = it3->boundary.begin(); it5 != it3->boundary.end(); ++it5) {
          for (vector<placerDB::point>::iterator it4 = it5->polygon.begin(); it4 != it5->polygon.end(); ++it4) {
            logger->debug("{0} {1}", it4->x, it4->y);
          }
        }
      }
    }
  }
}

void design::PrintConstraints() {
  auto logger = spdlog::default_logger()->clone("placer.design.PrintConstraints");

  logger->debug("=== SymmNet Constraits ===");
  for (vector<SymmNet>::iterator it = SNets.begin(); it != SNets.end(); ++it) {
    logger->debug("{0}", it->net1.name);
    for (vector<placerDB::Node>::iterator ni = it->net1.connected.begin(); ni != it->net1.connected.end(); ++ni) {
      logger->debug("{0} {1} {2}", ni->type, ni->iter, ni->iter2);
      if (ni->type == placerDB::Block) {
        logger->debug("@ {0} / {1}", Blocks.at(ni->iter2).back().name, Blocks.at(ni->iter2).back().blockPins.at(ni->iter).name);
      }
      if (ni->type == placerDB::Terminal) {
        logger->debug("@ {0}", Terminals.at(ni->iter).name);
      }
    }
    logger->debug("{0} ", it->net2.name);
    for (vector<placerDB::Node>::iterator ni = it->net2.connected.begin(); ni != it->net2.connected.end(); ++ni) {
      logger->debug("{0} {1} {2}", ni->type, ni->iter, ni->iter2);
      if (ni->type == placerDB::Block) {
        logger->debug("@ {0} / {1}", Blocks.at(ni->iter2).back().name, Blocks.at(ni->iter2).back().blockPins.at(ni->iter).name);
      }
      if (ni->type == placerDB::Terminal) {
        logger->debug("@ {0}", Terminals.at(ni->iter).name);
      }
    }
  }
  logger->debug("=== SymmPairBlock Constraints ===");
  for (vector<SymmPairBlock>::iterator it = SPBlocks.begin(); it != SPBlocks.end(); ++it) {
    for (vector<pair<int, int>>::iterator sit = it->sympair.begin(); sit != it->sympair.end(); ++sit) {
      logger->debug("sympair {0} @ {1} vs {2} @ {3}", sit->first, Blocks.at(sit->first).back().name, sit->second, Blocks.at(sit->second).back().name);
    }
    for (vector<pair<int, placerDB::Smark>>::iterator sit = it->selfsym.begin(); sit != it->selfsym.end(); ++sit) {
      logger->debug("selfsym {0} @ {1} symmetric to {2}", sit->first, Blocks.at(sit->first).back().name, sit->second);
    }
  }
  logger->debug("=== Preplace_blocks Constraits ===");
  for (vector<Preplace>::iterator it = Preplace_blocks.begin(); it != Preplace_blocks.end(); ++it) {
    logger->debug("block1 {0} block2 {1} corner {2} distance {3} horizon {4}", it->blockid1, it->blockid2, it->conner, it->distance, it->horizon);
  }
  logger->debug("=== Alignment_blocks Constraits ===");
  for (vector<Alignment>::iterator it = Alignment_blocks.begin(); it != Alignment_blocks.end(); ++it) {
    logger->debug("block1 {0} block2 {1} distance {2} horizon {3}", it->blockid1, it->blockid2, it->distance, it->horizon);
  }
  logger->debug("=== Abument_blocks Constraits ===");
  for (vector<Abument>::iterator it = Abument_blocks.begin(); it != Abument_blocks.end(); ++it) {
    logger->debug("block1 {0} block2 {1} distance {2} horizon {3}", it->blockid1, it->blockid2, it->distance, it->horizon);
  }
  logger->debug("=== Match_blocks Constraits ===");
  for (vector<MatchBlock>::iterator it = Match_blocks.begin(); it != Match_blocks.end(); ++it) {
    logger->debug("block1 {0} block2 {1}", it->blockid1, it->blockid2);
  }
  logger->debug("=== Align_blocks Constraints ===");
  for (vector<AlignBlock>::iterator it = Align_blocks.begin(); it != Align_blocks.end(); ++it) {
    logger->debug("@");
    for (vector<int>::iterator it2 = it->blocks.begin(); it2 != it->blocks.end(); ++it2) {
      logger->debug(" {0} ", *it2);
    }
  }
  logger->debug("=== SpreadConstraints Constraints ===");
  for (auto it : hSpread) {
    logger->debug("@h ({0},{1}) {2}", it.first.first, it.first.second, it.second);
  }
  for (auto it : vSpread) {
    logger->debug("@v ({0},{1}) {2}", it.first.first, it.first.second, it.second);
  }
}

void design::PrintTerminals() {
  auto logger = spdlog::default_logger()->clone("placer.design.PrintTerminals");

  logger->debug("=== Terminals ===");
  for (vector<terminal>::iterator it = Terminals.begin(); it != Terminals.end(); ++it) {
    logger->debug("Name: {0} net: {1} @", it->name, it->netIter);
    if (it->netIter >= 0) {
      logger->debug(" {0} ", Nets.at(it->netIter).name);
    }
    logger->debug(" SBidx: {0} counterpart: {1}", it->SBidx, it->counterpart);
  }
}

void design::PrintNets() {
  auto logger = spdlog::default_logger()->clone("placer.design.PrintNets");

  logger->debug("=== Nets ===");
  for (vector<placerDB::net>::iterator it = Nets.begin(); it != Nets.end(); ++it) {
    logger->debug("Name: {0} Weight: {1} Priority: {2}", (*it).name, it->weight, it->priority);
    logger->debug("Name: {0} Priority: {1} Margin: {2}", (*it).name, it->priority, it->margin);
    logger->debug("Connected: ");
    for (vector<placerDB::Node>::iterator it2 = it->connected.begin(); it2 != it->connected.end(); ++it2) {
      logger->debug("type: {0} iter {1} iter2 {2}", it2->type, it2->iter, it2->iter2);
      if (it2->type == placerDB::Block) {
        const auto& blk = Blocks.at(it2->iter2);
        if (blk.size() == 0) {
          logger->debug(" <empty>");
        } else if (blk.back().blockPins.size() > it2->iter) {
          const auto& tmp = blk.back();
          const auto& tmp2 = tmp.blockPins.at(it2->iter);
          logger->debug("{0} / {1}", tmp.name, tmp2.name);
        }
      }
      if (it2->type == placerDB::Terminal) {
        logger->debug("{0}", Terminals.at(it2->iter).name);
      }
    }
  }
}

int design::GetBlockWidth(int blockid, placerDB::Omark ort, int sel) {
  if (ort == placerDB::N || ort == placerDB::S || ort == placerDB::FN || ort == placerDB::FS) {
    return Blocks.at(blockid).at(sel).width;
  } else {
    return Blocks.at(blockid).at(sel).height;
  }
}

int design::GetBlockHeight(int blockid, placerDB::Omark ort, int sel) {
  if (ort == placerDB::N || ort == placerDB::S || ort == placerDB::FN || ort == placerDB::FS) {
    return Blocks.at(blockid).at(sel).height;
  } else {
    return Blocks.at(blockid).at(sel).width;
  }
}

placerDB::point design::GetBlockAbsCenter(int blockid, placerDB::Omark ort, placerDB::point LL, int sel) {
  placerDB::point p;
  p.x = GetBlockWidth(blockid, ort, sel) / 2 + LL.x;
  p.y = GetBlockHeight(blockid, ort, sel) / 2 + LL.y;
  return p;
}

placerDB::point design::GetPlacedPosition(placerDB::point oldp, int width, int height, placerDB::Omark ort) {
  placerDB::point p;
  int WW = width;
  int HH = height;
  int X = oldp.x;
  int Y = oldp.y;
  switch (ort) {
    case placerDB::N:
      p.x = X;
      p.y = Y;
      break;
    case placerDB::S:
      p.x = WW - X;
      p.y = HH - Y;
      break;
    case placerDB::W:
      p.x = HH - Y;
      p.y = X;
      break;
    case placerDB::E:
      p.x = Y;
      p.y = WW - X;
      break;
    case placerDB::FN:
      p.x = WW - X;
      p.y = Y;
      break;
    case placerDB::FS:
      p.x = X;
      p.y = HH - Y;
      break;
    case placerDB::FW:
      p.x = Y;
      p.y = X;
      break;
    case placerDB::FE:
      p.x = HH - Y;
      p.y = WW - X;
      break;
    default:
      p.x = X;
      p.y = Y;
      break;
  }
  return p;
}

PnRDB::point design::GetPlacedPnRPosition(PnRDB::point oldp, int width, int height, placerDB::Omark ort) {
  PnRDB::point p;
  int WW = width;
  int HH = height;
  int X = oldp.x;
  int Y = oldp.y;
  switch (ort) {
    case placerDB::N:
      p.x = X;
      p.y = Y;
      break;
    case placerDB::S:
      p.x = WW - X;
      p.y = HH - Y;
      break;
    case placerDB::W:
      p.x = HH - Y;
      p.y = X;
      break;
    case placerDB::E:
      p.x = Y;
      p.y = WW - X;
      break;
    case placerDB::FN:
      p.x = WW - X;
      p.y = Y;
      break;
    case placerDB::FS:
      p.x = X;
      p.y = HH - Y;
      break;
    case placerDB::FW:
      p.x = Y;
      p.y = X;
      break;
    case placerDB::FE:
      p.x = HH - Y;
      p.y = WW - X;
      break;
    default:
      p.x = X;
      p.y = Y;
      break;
  }
  return p;
}

vector<placerDB::point> design::GetPlacedBlockPinRelPosition(int blockid, int pinid, placerDB::Omark ort, int sel) {
  vector<placerDB::point> newCenter;
  for (vector<placerDB::point>::iterator it = Blocks.at(blockid).at(sel).blockPins.at(pinid).center.begin();
       it != Blocks.at(blockid).at(sel).blockPins.at(pinid).center.end(); ++it) {
    newCenter.push_back(GetPlacedPosition(*it, Blocks.at(blockid).at(sel).width, Blocks.at(blockid).at(sel).height, ort));
  }
  return newCenter;
  // return GetPlacedPosition(Blocks.at(blockid).blockPins.at(pinid).center, Blocks.at(blockid).width, Blocks.at(blockid).height, ort);
}

vector<placerDB::point> design::GetPlacedBlockPinAbsPosition(int blockid, int pinid, placerDB::Omark ort, placerDB::point LL, int sel) {
  vector<placerDB::point> p;

  // std::cout<<"design test1"<<std::endl;
  p = GetPlacedBlockPinRelPosition(blockid, pinid, ort, sel);
  // std::cout<<"design test2"<<std::endl;
  for (vector<placerDB::point>::iterator it = p.begin(); it != p.end(); ++it) {
    (it->x) += LL.x;
    (it->y) += LL.y;
  }
  return p;
}

vector<placerDB::point> design::GetPlacedBlockRelBoundary(int blockid, placerDB::Omark ort, int sel) {
  vector<placerDB::point> newp;
  // cout<<"  In GetPlacedBlockRelBoundary"<<endl;
  for (vector<placerDB::point>::iterator it = Blocks.at(blockid).at(sel).boundary.polygon.begin(); it != Blocks.at(blockid).at(sel).boundary.polygon.end();
       ++it) {
    // std::cout<<"design test3"<<std::endl;
    newp.push_back(GetPlacedPosition(*it, Blocks.at(blockid).at(sel).width, Blocks.at(blockid).at(sel).height, ort));
    // std::cout<<"design test4"<<std::endl;
    // cout<<"push "<<newp.back().x<<", "<<newp.back().y<<endl;
  }
  // cout<<"point size "<<newp.size()<<endl;
  return newp;
}

vector<placerDB::point> design::GetPlacedBlockAbsBoundary(int blockid, placerDB::Omark ort, placerDB::point LL, int sel) {
  // cout<<"  In GetPlacedBlockAbsBoundary"<<endl;
  vector<placerDB::point> newp = GetPlacedBlockRelBoundary(blockid, ort, sel);
  for (vector<placerDB::point>::iterator it = newp.begin(); it != newp.end(); ++it) {
    (it->x) += LL.x;
    (it->y) += LL.y;
    // cout<<"push "<<it->x<<", "<<it->y<<endl;
  }
  // cout<<"point size "<<newp.size()<<endl;
  return newp;
}

vector<vector<placerDB::point>> design::GetPlacedBlockPinRelBoundary(int blockid, int pinid, placerDB::Omark ort, int sel) {
  vector<vector<placerDB::point>> newp;
  for (vector<placerDB::bbox>::iterator it = Blocks.at(blockid).at(sel).blockPins.at(pinid).boundary.begin();
       it != Blocks.at(blockid).at(sel).blockPins.at(pinid).boundary.end(); ++it) {
    newp.resize(newp.size() + 1);
    for (vector<placerDB::point>::iterator it2 = it->polygon.begin(); it2 != it->polygon.end(); ++it2) {
      newp.back().push_back(GetPlacedPosition(*it2, Blocks.at(blockid).at(sel).width, Blocks.at(blockid).at(sel).height, ort));
    }
  }
  // for(vector<placerDB::point>::iterator it=Blocks.at(blockid).blockPins.at(pinid).boundary.polygon.begin();
  // it!=Blocks.at(blockid).blockPins.at(pinid).boundary.polygon.end(); ++it) {
  //  newp.push_back( GetPlacedPosition(*it, Blocks.at(blockid).width, Blocks.at(blockid).height, ort) );
  //}
  return newp;
}

vector<vector<placerDB::point>> design::GetPlacedBlockPinAbsBoundary(int blockid, int pinid, placerDB::Omark ort, placerDB::point LL, int sel) {
  vector<vector<placerDB::point>> newp = GetPlacedBlockPinRelBoundary(blockid, pinid, ort, sel);
  for (vector<vector<placerDB::point>>::iterator it = newp.begin(); it != newp.end(); ++it) {
    for (vector<placerDB::point>::iterator it2 = it->begin(); it2 != it->end(); ++it2) {
      (it2->x) += LL.x;
      (it2->y) += LL.y;
    }
  }
  return newp;
}

PnRDB::point design::GetPlacedBlockInterMetalAbsPoint(int blockid, placerDB::Omark ort, PnRDB::point& originP, placerDB::point LL, int sel) {
  PnRDB::point placedP = GetPlacedPnRPosition(originP, Blocks.at(blockid).at(sel).width, Blocks.at(blockid).at(sel).height, ort);
  placedP.x += LL.x;
  placedP.y += LL.y;
  return placedP;
}

PnRDB::point design::GetPlacedBlockInterMetalRelPoint(int blockid, placerDB::Omark ort, PnRDB::point& originP, int sel) {
  return GetPlacedPnRPosition(originP, Blocks.at(blockid).at(sel).width, Blocks.at(blockid).at(sel).height, ort);
}

PnRDB::bbox design::GetPlacedBlockInterMetalRelBox(int blockid, placerDB::Omark ort, PnRDB::bbox& originBox, int sel) {
  const auto& blk = Blocks.at(blockid).at(sel);

  vector<PnRDB::point> points;
  points.push_back(GetPlacedPnRPosition(originBox.LL, blk.width, blk.height, ort));
  points.push_back(GetPlacedPnRPosition(originBox.UR, blk.width, blk.height, ort));

  int x = INT_MAX;
  int X = INT_MIN;
  int y = INT_MAX;
  int Y = INT_MIN;

  for (unsigned int i = 0; i < points.size(); ++i) {
    if (x > points[i].x) {
      x = points[i].x;
    }
    if (X < points[i].x) {
      X = points[i].x;
    }
    if (y > points[i].y) {
      y = points[i].y;
    }
    if (Y < points[i].y) {
      Y = points[i].y;
    }
  }

  PnRDB::bbox placedBox;
  placedBox.LL.x = x;
  placedBox.LL.y = y;
  placedBox.UR.x = X;
  placedBox.UR.y = Y;
  return placedBox;
}

PnRDB::bbox design::GetPlacedBlockInterMetalAbsBox(int blockid, placerDB::Omark ort, PnRDB::bbox& originBox, placerDB::point LL, int sel) {
  PnRDB::bbox placedBox = GetPlacedBlockInterMetalRelBox(blockid, ort, originBox, sel);
  placedBox.LL.x += LL.x;
  placedBox.LL.y += LL.y;
  placedBox.UR.x += LL.x;
  placedBox.UR.y += LL.y;
  return placedBox;
}

int design::GetBlockPinNum(int blockid, int sel) { return (int)Blocks.at(blockid).at(sel).blockPins.size(); }

string design::GetBlockPinName(int blockid, int pinid, int sel) { return Blocks.at(blockid).at(sel).blockPins.at(pinid).name; }

string design::GetBlockName(int blockid) { return Blocks.at(blockid).back().name; }

string design::GetTerminalName(int termid) { return Terminals.at(termid).name; }

vector<pair<int, int>> design::checkSympairInSymmBlock(vector<placerDB::SymmBlock>& SBs, vector<pair<int, int>>& Tsympair) {
  vector<pair<int, int>> pp;
  // vector<int> first; vector<int> second; bool mark=false;
  for (unsigned int j = 0; j < SBs.size(); ++j) {
    for (vector<pair<int, int>>::iterator pi = SBs.at(j).sympair.begin(); pi != SBs.at(j).sympair.end(); ++pi) {
      for (unsigned int i = 0; i < Tsympair.size(); ++i) {
        if (pi->first == Tsympair.at(i).first && pi->second == Tsympair.at(i).second) {
          pp.push_back(make_pair(j, i));
        }
      }
    }
  }
  // pair<int,int> pp=make_pair(first,second);
  return pp;
}

vector<pair<int, int>> design::checkSelfsymInSymmBlock(vector<placerDB::SymmBlock>& SBs, vector<pair<int, placerDB::Smark>>& Tselfsym) {
  vector<pair<int, int>> pp;
  // int first=-1; int second=-1; bool mark=false;
  for (unsigned int j = 0; j < SBs.size(); ++j) {
    for (vector<pair<int, placerDB::Smark>>::iterator pi = SBs.at(j).selfsym.begin(); pi != SBs.at(j).selfsym.end(); ++pi) {
      for (unsigned int i = 0; i < Tselfsym.size(); ++i) {
        if (pi->first == Tselfsym.at(i).first && pi->second == Tselfsym.at(i).second) {
          pp.push_back(make_pair(j, i));
        }
      }
    }
  }
  // pair<int,int> pp=make_pair(first,second);
  return pp;
}

void design::checkselfsym(vector<pair<int, int>>& tmpsympair, vector<pair<int, placerDB::Smark>>& tmpselfsym, placerDB::Smark tsmark) {
  auto logger = spdlog::default_logger()->clone("placer.design.constructSymmGroup");

  vector<pair<int, int>> tmpsympair_temp;

  pair<int, int> temp_pair;
  pair<int, placerDB::Smark> temp_selfpair;

  for (unsigned int i = 0; i < tmpsympair.size(); ++i) {
    bool found_redundant = false;
    int redundant_index = 0;
    for (unsigned int j = i + 1; j < tmpsympair.size(); ++j) {
      if (tmpsympair[i].first == tmpsympair[j].first or tmpsympair[i].first == tmpsympair[j].second or tmpsympair[i].second == tmpsympair[j].first or
          tmpsympair[i].second == tmpsympair[j].second) {
        found_redundant = true;
        redundant_index = j;
        break;
      }
    }
    if (found_redundant) {
      int j = redundant_index;
      if (tmpsympair[i].first == tmpsympair[j].first) {
        temp_selfpair = make_pair(tmpsympair[i].first, tsmark);
        temp_pair = (tmpsympair[i].second < tmpsympair[j].second) ? make_pair(tmpsympair[i].second, tmpsympair[j].second)
                                                                  : make_pair(tmpsympair[j].second, tmpsympair[i].second);
      }
      if (tmpsympair[i].first == tmpsympair[j].second) {
        temp_selfpair = make_pair(tmpsympair[i].first, tsmark);
        temp_pair = (tmpsympair[i].second < tmpsympair[j].first) ? make_pair(tmpsympair[i].second, tmpsympair[j].first)
                                                                 : make_pair(tmpsympair[j].first, tmpsympair[i].second);
      }
      if (tmpsympair[i].second == tmpsympair[j].first) {
        temp_selfpair = make_pair(tmpsympair[i].second, tsmark);
        temp_pair = (tmpsympair[i].first < tmpsympair[j].second) ? make_pair(tmpsympair[i].first, tmpsympair[j].second)
                                                                 : make_pair(tmpsympair[j].second, tmpsympair[i].first);
      }
      if (tmpsympair[i].second == tmpsympair[j].second) {
        temp_selfpair = make_pair(tmpsympair[i].second, tsmark);
        temp_pair = (tmpsympair[i].first < tmpsympair[j].first) ? make_pair(tmpsympair[i].first, tmpsympair[j].first)
                                                                : make_pair(tmpsympair[j].first, tmpsympair[i].first);
      }
      tmpsympair_temp.push_back(temp_pair);
      tmpsympair.erase(tmpsympair.begin() + redundant_index);
      bool found_slef = false;
      for (unsigned int k = 0; k < tmpselfsym.size(); ++k) {
        if (tmpselfsym[k].first == temp_selfpair.first) {
          found_slef = true;
        }
      }
      if (found_slef) {
        logger->debug("Placer-Warning: symmetey net bug exist");
      } else {
        tmpselfsym.push_back(temp_selfpair);
      }
    } else {
      tmpsympair_temp.push_back(tmpsympair[i]);
    }
  }

  tmpsympair = tmpsympair_temp;
}

void design::constructSymmGroup() {
  auto logger = spdlog::default_logger()->clone("placer.design.constructSymmGroup");

  // Known issues:
  // 1. The merging of individual symmetry nets into symmetry group depends on the order of nets.
  // If the common objects of two symmetry-net groups exist in another symmetry-net group,
  // the merging will not be completed.
  // Known limitation:
  // 1. The symmetric pair in the symmetry group should have the same object type.
  // E.g. mixing of terminal and block will be ignored.
  // 2. The self-symmetry object should be block rather than terminal.
  // 3. The self-symmetry object is assumed to be vertically symmetric.
  int dnidx = (int)Blocks.size() + 2;  // vertices:  blocks, source, sink, dummynodes
  int net1Sink, net2Sink;
  pair<int, int> tpair;
  vector<pair<int, int>> tmpsympair;
  vector<pair<int, placerDB::Smark>> tmpselfsym;
  vector<placerDB::SymmBlock> SBs;
  placerDB::Smark axis_dir;
  for (vector<SymmNet>::iterator sni = SNets.begin(); sni != SNets.end(); ++sni) {
    axis_dir = sni->axis_dir;
    tmpsympair.clear();
    tmpselfsym.clear();
    // cout<<sni->net1.name<<" vs "<<sni->net2.name<<endl;
    for (unsigned int i = 0; i < sni->net1.connected.size(); ++i) {
      // std::cout<<"type "<<sni->net1.connected.at(i).type<<" vs "<<sni->net2.connected.at(i).type<<std::endl;
      if (sni->net1.connected.at(i).type != sni->net2.connected.at(i).type) {
        logger->debug("Placer-Warning: different object type found in symmetric nets! Skip those objects...");
      }
      if (sni->net1.connected.at(i).type == placerDB::Terminal) {
        // cout<<sni->net1.connected.at(i).iter<<endl;
        // cout<<sni->net2.connected.at(i).iter<<endl;
        net1Sink = sni->net1.connected.at(i).iter + (int)Blocks.size();
        net2Sink = sni->net2.connected.at(i).iter + (int)Blocks.size();
      } else if (sni->net1.connected.at(i).type == placerDB::Block) {
        net1Sink = sni->net1.connected.at(i).iter2;
        net2Sink = sni->net2.connected.at(i).iter2;
      }
      tpair = (net1Sink < net2Sink) ? make_pair(net1Sink, net2Sink) : make_pair(net2Sink, net1Sink);
      // cout<<tpair.first<<" "<<tpair.second<<endl;
      if (tpair.first == tpair.second) {  // if self-symmetric block
        if (tpair.first < (int)Blocks.size()) {
          // cout<<"Block "<<sni->net1.connected.at(i).iter2<<"@"<<Blocks.at(sni->net1.connected.at(i).iter2).back().name<<  " pin
          // "<<sni->net1.connected.at(i).iter<<"@"<<Blocks.at(sni->net1.connected.at(i).iter2).back().blockPins.at(sni->net1.connected.at(i).iter).name<<endl;
          // vector<placerDB::point> p1V=Blocks.at(sni->net1.connected.at(i).iter2).blockPins.at(sni->net1.connected.at(i).iter).center;
          // vector<placerDB::point> p2V=Blocks.at(sni->net2.connected.at(i).iter2).blockPins.at(sni->net2.connected.at(i).iter).center;
          // placerDB::point p1=Blocks.at(sni->net1.connected.at(i).iter2).blockPins.at(sni->net1.connected.at(i).iter).center;
          // placerDB::point p2=Blocks.at(sni->net2.connected.at(i).iter2).blockPins.at(sni->net2.connected.at(i).iter).center;
          placerDB::Smark tsmark = axis_dir;
          // placerDB::Smark tsmark= ( abs(p1.x-p2.x)<abs(p1.y-p2.y) ) ? placerDB::V : placerDB::H;
          tmpselfsym.push_back(make_pair(tpair.first, tsmark));
        } else {
          logger->debug("Placer-Warning: self-symmetric terminal found! Skip this object...");
          continue;
        }
      } else {  // if paired-symmetric block
        tmpsympair.push_back(tpair);
      }
    }
    for (unsigned int i = 0; i < tmpsympair.size(); ++i) {
      logger->debug("paired-symmectric: {0} {1}", tmpsympair.at(i).first, tmpsympair.at(i).second);
    }
    for (unsigned int i = 0; i < tmpselfsym.size(); ++i) {
      logger->debug("self-symmectric: {0} {1}", tmpselfsym.at(i).first, tmpselfsym.at(i).second);
    }
    checkselfsym(tmpsympair, tmpselfsym, axis_dir);
    int sbidx = MergeNewBlockstoSymmetryGroup(tmpsympair, tmpselfsym, SBs, this->SNets, axis_dir);
    // std::cout<<"Placer-Info: symmetry net "<<sni-SNets.begin()<<" sbidx "<<sbidx<<"SBs size()"<<SBs.size()<<std::endl;
    sni->SBidx = sbidx;
    // vector<pair<int,int> > matchedPair,matchedSelf;
    // matchedPair=checkSympairInSymmBlock(SBs, tmpsympair);
    // matchedSelf=checkSelfsymInSymmBlock(SBs, tmpselfsym);
    // if(matchedPair.empty()) {
    //  if(matchedSelf.empty()) { // neither matched
    //    cout<<"New symmetric group "<<endl;
    //    SBs.resize(SBs.size()+1);
    //    SBs.back().sympair=tmpsympair;
    //    SBs.back().selfsym=tmpselfsym;
    //    //SBs.back().dnode=dnidx++;
    //  } else { // only matched self-symmetric
    //    int gidx=matchedSelf[0].first;
    //    for(vector<pair<int,int> >::iterator itt=matchedSelf.begin();itt!=matchedSelf.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit)
    //        {SBs.at(gidx).sympair.push_back(*spit);} for(vector<pair<int,placerDB::Smark> >::iterator
    //        spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);} cout<<"Move
    //        SB#"<<itt->first<<" to SB#"<<gidx<<endl; SBs.at(itt->first).sympair.clear(); SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    cout<<"Append symmetric group #"<<gidx<<endl;
    //    for(int i=0;i<(int)tmpsympair.size();i++) { SBs.at(gidx).sympair.push_back( tmpsympair.at(i) ); }
    //    for(int i=0;i<(int)tmpselfsym.size();i++) {
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedSelf.begin();mit!=matchedSelf.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) );
    //    }
    //  }
    //} else {
    //  if(matchedSelf.empty()) { // only matched paired-symmetric
    //    int gidx=matchedPair[0].first;
    //    for(vector<pair<int,int> >::iterator itt=matchedPair.begin();itt!=matchedPair.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit)
    //        {SBs.at(gidx).sympair.push_back(*spit);} for(vector<pair<int,placerDB::Smark> >::iterator
    //        spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);} cout<<"Move
    //        SB#"<<itt->first<<" to SB#"<<gidx<<endl; SBs.at(itt->first).sympair.clear(); SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    cout<<"Append symmetric group #"<<gidx<<endl;
    //    for(int i=0;i<(int)tmpsympair.size();i++) {
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedPair.begin();mit!=matchedPair.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).sympair.push_back( tmpsympair.at(i) );
    //    }
    //    for(int i=0;i<(int)tmpselfsym.size();i++) { SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) ); }
    //  } else { // both matched
    //    int gidx=matchedSelf[0].first;
    //    for(vector<pair<int,int> >::iterator itt=matchedSelf.begin();itt!=matchedSelf.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit)
    //        {SBs.at(gidx).sympair.push_back(*spit);} for(vector<pair<int,placerDB::Smark> >::iterator
    //        spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);} cout<<"Move
    //        SB#"<<itt->first<<" to SB#"<<gidx<<endl; SBs.at(itt->first).sympair.clear(); SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    for(vector<pair<int,int> >::iterator itt=matchedPair.begin();itt!=matchedPair.end();++itt) {
    //      if(itt->first!=gidx) {
    //        for(vector<pair<int,int> >::iterator spit=SBs.at(itt->first).sympair.begin();spit!=SBs.at(itt->first).sympair.end();++spit)
    //        {SBs.at(gidx).sympair.push_back(*spit);} for(vector<pair<int,placerDB::Smark> >::iterator
    //        spit=SBs.at(itt->first).selfsym.begin();spit!=SBs.at(itt->first).selfsym.end();++spit) {SBs.at(gidx).selfsym.push_back(*spit);} cout<<"Move
    //        SB#"<<itt->first<<" to SB#"<<gidx<<endl; SBs.at(itt->first).sympair.clear(); SBs.at(itt->first).selfsym.clear();
    //      }
    //    }
    //    for(int i=0;i<(int)tmpselfsym.size();i++) {
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedSelf.begin();mit!=matchedSelf.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).selfsym.push_back( tmpselfsym.at(i) );
    //    }
    //    for(int i=0;i<(int)tmpsympair.size();i++) {
    //      bool found=false;
    //      for(vector<pair<int,int> >::iterator mit=matchedPair.begin();mit!=matchedPair.end();++mit) {
    //        if(i==mit->second) {found=true;break;}
    //      }
    //      if(!found) SBs.at(gidx).sympair.push_back( tmpsympair.at(i) );
    //    }
    //  }
    //}
  }
  for (vector<SymmPairBlock>::iterator sni = SPBlocks.begin(); sni != SPBlocks.end(); ++sni) {
    MergeNewBlockstoSymmetryGroup(sni->sympair, sni->selfsym, SBs, this->SNets, sni->axis_dir);
  }
  SBlocks.clear();
  for (vector<placerDB::SymmBlock>::iterator it = SBs.begin(); it != SBs.end(); ++it) {
    // if(it->sympair.empty() && it->selfsym.empty()) {continue;}
    SBlocks.resize(SBlocks.size() + 1);
    SBlocks.back().sympair = it->sympair;
    SBlocks.back().selfsym = it->selfsym;
    SBlocks.back().axis_dir = it->axis_dir;
    SBlocks.back().dnode = dnidx++;
  }
  for (unsigned int i = 0; i < SBlocks.size(); ++i) {
    for (vector<pair<int, int>>::iterator pit = SBlocks[i].sympair.begin(); pit != SBlocks[i].sympair.end(); ++pit) {
      if (pit->first < (int)Blocks.size()) {
        for (unsigned int w = 0; w < Blocks.at(pit->first).size(); ++w) {
          Blocks.at(pit->first).at(w).SBidx = i;
          Blocks.at(pit->first).at(w).counterpart = pit->second;
        }
      } else {
        Terminals.at(pit->first - Blocks.size()).SBidx = i;
        Terminals.at(pit->first - Blocks.size()).counterpart = pit->second - Blocks.size();
      }
      if (pit->second < (int)Blocks.size()) {
        for (unsigned int w = 0; w < Blocks.at(pit->second).size(); ++w) {
          Blocks.at(pit->second).at(w).SBidx = i;
          Blocks.at(pit->second).at(w).counterpart = pit->first;
        }
      } else {
        Terminals.at(pit->second - Blocks.size()).SBidx = i;
        Terminals.at(pit->second - Blocks.size()).counterpart = pit->first - Blocks.size();
      }
    }
    for (vector<pair<int, placerDB::Smark>>::iterator sit = SBlocks[i].selfsym.begin(); sit != SBlocks[i].selfsym.end(); ++sit) {
      if (sit->first < (int)Blocks.size()) {
        for (unsigned int w = 0; w < Blocks.at(sit->first).size(); ++w) {
          Blocks.at(sit->first).at(w).SBidx = i;
          Blocks.at(sit->first).at(w).counterpart = sit->first;
        }
      } else {
        Terminals.at(sit->first - Blocks.size()).SBidx = i;
        Terminals.at(sit->first - Blocks.size()).counterpart = sit->first - Blocks.size();
      }
    }
  }
  ////std::cout<<"Leaving constrcution\n";
}

int design::MergeNewBlockstoSymmetryGroup(vector<pair<int, int>>& tmpsympair, vector<pair<int, placerDB::Smark>>& tmpselfsym, vector<placerDB::SymmBlock>& SBs,
                                          vector<SymmNet>& SNs, placerDB::Smark axis_dir) {
  auto logger = spdlog::default_logger()->clone("placer.design.MergeNewBlockstoSymmetryGroup");

  vector<pair<int, int>> matchedPair, matchedSelf;
  matchedPair = checkSympairInSymmBlock(SBs, tmpsympair);
  matchedSelf = checkSelfsymInSymmBlock(SBs, tmpselfsym);
  int sbidx = -1;
  if (matchedPair.empty()) {
    if (matchedSelf.empty()) {  // neither matched
      logger->debug("New symmetric group ");
      SBs.resize(SBs.size() + 1);
      SBs.back().sympair = tmpsympair;
      SBs.back().selfsym = tmpselfsym;
      SBs.back().axis_dir = axis_dir;
      // SBs.back().dnode=dnidx++;
      sbidx = SBs.size() - 1;
    } else {  // only matched self-symmetric
      int gidx = matchedSelf[0].first;
      for (vector<pair<int, int>>::iterator itt = matchedSelf.begin(); itt != matchedSelf.end(); ++itt) {
        if (itt->first != gidx) {
          for (vector<pair<int, int>>::iterator spit = SBs.at(itt->first).sympair.begin(); spit != SBs.at(itt->first).sympair.end(); ++spit) {
            SBs.at(gidx).sympair.push_back(*spit);
          }
          for (vector<pair<int, placerDB::Smark>>::iterator spit = SBs.at(itt->first).selfsym.begin(); spit != SBs.at(itt->first).selfsym.end(); ++spit) {
            SBs.at(gidx).selfsym.push_back(*spit);
          }
          logger->debug("Move SB# {0} to SB# {1}", itt->first, gidx);
          SBs.at(gidx).axis_dir = SBs.at(itt->first).axis_dir;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
          for (vector<SymmNet>::iterator nit = SNs.begin(); nit != SNs.end(); ++nit) {
            if (nit->SBidx == itt->first) {
              nit->SBidx = gidx;
            }
          }
        }
      }
      logger->debug("Append symmetric group # {0}", gidx);
      for (unsigned int i = 0; i < tmpsympair.size(); ++i) {
        SBs.at(gidx).sympair.push_back(tmpsympair.at(i));
      }
      for (unsigned int i = 0; i < tmpselfsym.size(); ++i) {
        bool found = false;
        for (vector<pair<int, int>>::iterator mit = matchedSelf.begin(); mit != matchedSelf.end(); ++mit) {
          if ((int)i == mit->second) {
            found = true;
            break;
          }
        }
        if (!found) SBs.at(gidx).selfsym.push_back(tmpselfsym.at(i));
      }
      SBs.at(gidx).axis_dir = axis_dir;
      sbidx = gidx;
    }
  } else {
    if (matchedSelf.empty()) {  // only matched paired-symmetric
      int gidx = matchedPair[0].first;
      for (vector<pair<int, int>>::iterator itt = matchedPair.begin(); itt != matchedPair.end(); ++itt) {
        if (itt->first != gidx) {
          for (vector<pair<int, int>>::iterator spit = SBs.at(itt->first).sympair.begin(); spit != SBs.at(itt->first).sympair.end(); ++spit) {
            SBs.at(gidx).sympair.push_back(*spit);
          }
          for (vector<pair<int, placerDB::Smark>>::iterator spit = SBs.at(itt->first).selfsym.begin(); spit != SBs.at(itt->first).selfsym.end(); ++spit) {
            SBs.at(gidx).selfsym.push_back(*spit);
          }
          SBs.at(gidx).axis_dir = SBs.at(itt->first).axis_dir;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
          for (vector<SymmNet>::iterator nit = SNs.begin(); nit != SNs.end(); ++nit) {
            if (nit->SBidx == itt->first) {
              nit->SBidx = gidx;
            }
          }
        }
      }
      logger->debug("Append symmetric group # {0}", gidx);
      for (unsigned int i = 0; i < tmpsympair.size(); ++i) {
        bool found = false;
        for (vector<pair<int, int>>::iterator mit = matchedPair.begin(); mit != matchedPair.end(); ++mit) {
          if ((int)i == mit->second) {
            found = true;
            break;
          }
        }
        if (!found) SBs.at(gidx).sympair.push_back(tmpsympair.at(i));
      }
      for (unsigned int i = 0; i < tmpselfsym.size(); ++i) {
        SBs.at(gidx).selfsym.push_back(tmpselfsym.at(i));
      }
      sbidx = gidx;
    } else {  // both matched
      int gidx = matchedSelf[0].first;
      for (vector<pair<int, int>>::iterator itt = matchedSelf.begin(); itt != matchedSelf.end(); ++itt) {
        if (itt->first != gidx) {
          for (vector<pair<int, int>>::iterator spit = SBs.at(itt->first).sympair.begin(); spit != SBs.at(itt->first).sympair.end(); ++spit) {
            SBs.at(gidx).sympair.push_back(*spit);
          }
          for (vector<pair<int, placerDB::Smark>>::iterator spit = SBs.at(itt->first).selfsym.begin(); spit != SBs.at(itt->first).selfsym.end(); ++spit) {
            SBs.at(gidx).selfsym.push_back(*spit);
          }
          logger->debug("Move SB# {0} to SB# {1}", itt->first, gidx);
          SBs.at(gidx).axis_dir = SBs.at(itt->first).axis_dir;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
          for (vector<SymmNet>::iterator nit = SNs.begin(); nit != SNs.end(); ++nit) {
            if (nit->SBidx == itt->first) {
              nit->SBidx = gidx;
            }
          }
        }
      }
      for (vector<pair<int, int>>::iterator itt = matchedPair.begin(); itt != matchedPair.end(); ++itt) {
        if (itt->first != gidx) {
          for (vector<pair<int, int>>::iterator spit = SBs.at(itt->first).sympair.begin(); spit != SBs.at(itt->first).sympair.end(); ++spit) {
            SBs.at(gidx).sympair.push_back(*spit);
          }
          for (vector<pair<int, placerDB::Smark>>::iterator spit = SBs.at(itt->first).selfsym.begin(); spit != SBs.at(itt->first).selfsym.end(); ++spit) {
            SBs.at(gidx).selfsym.push_back(*spit);
          }
          logger->debug("Move SB# {0} to SB# {1}", itt->first, gidx);
          SBs.at(gidx).axis_dir = SBs.at(itt->first).axis_dir;
          SBs.at(itt->first).sympair.clear();
          SBs.at(itt->first).selfsym.clear();
          for (vector<SymmNet>::iterator nit = SNs.begin(); nit != SNs.end(); ++nit) {
            if (nit->SBidx == itt->first) {
              nit->SBidx = gidx;
            }
          }
        }
      }
      for (unsigned int i = 0; i < tmpselfsym.size(); ++i) {
        bool found = false;
        for (vector<pair<int, int>>::iterator mit = matchedSelf.begin(); mit != matchedSelf.end(); ++mit) {
          if ((int)i == mit->second) {
            found = true;
            break;
          }
        }
        if (!found) SBs.at(gidx).selfsym.push_back(tmpselfsym.at(i));
      }
      for (unsigned int i = 0; i < tmpsympair.size(); ++i) {
        bool found = false;
        for (vector<pair<int, int>>::iterator mit = matchedPair.begin(); mit != matchedPair.end(); ++mit) {
          if ((int)i == mit->second) {
            found = true;
            break;
          }
        }
        if (!found) SBs.at(gidx).sympair.push_back(tmpsympair.at(i));
      }
      SBs.at(gidx).axis_dir = axis_dir;
      sbidx = gidx;
    }
  }
  return sbidx;
}

int design::GetBlockSymmGroup(int blockid) const { return Blocks.at(blockid).back().SBidx; }

int design::GetBlockCounterpart(int blockid) { return Blocks.at(blockid).back().counterpart; }

vector<int> design::GetRealBlockListfromSymmGroup(int sgid) {
  vector<int> blist;
  if (sgid >= 0 && sgid < (int)SBlocks.size()) {
    for (vector<pair<int, int>>::iterator sit = SBlocks.at(sgid).sympair.begin(); sit != SBlocks.at(sgid).sympair.end(); ++sit) {
      if (this->mixFlag) {
        if (sit->first < (int)Blocks.size() && Blocks.at(sit->first).back().mapIdx == -1) {
          blist.push_back(sit->first);
        }
        if (sit->second < (int)Blocks.size() && Blocks.at(sit->first).back().mapIdx == -1) {
          blist.push_back(sit->second);
        }
      } else {
        if (sit->first < (int)Blocks.size()) {
          blist.push_back(sit->first);
        }
        if (sit->second < (int)Blocks.size()) {
          blist.push_back(sit->second);
        }
      }
    }
    for (vector<pair<int, placerDB::Smark>>::iterator sit = SBlocks.at(sgid).selfsym.begin(); sit != SBlocks.at(sgid).selfsym.end(); ++sit) {
      if (this->mixFlag) {
        if (sit->first < (int)Blocks.size() && Blocks.at(sit->first).back().mapIdx == -1) {
          blist.push_back(sit->first);
        }  // cout<<"Push "<<sit->first<<endl;}
      } else {
        if (sit->first < (int)Blocks.size()) {
          blist.push_back(sit->first);
        }  // cout<<"Push "<<sit->first<<endl;}
      }
    }
  }
  return blist;
}

vector<int> design::GetRealBlockPlusAxisListfromSymmGroup(int sgid) {
  vector<int> blist;
  if (sgid >= 0 && sgid < (int)SBlocks.size()) {
    for (vector<pair<int, int>>::iterator sit = SBlocks.at(sgid).sympair.begin(); sit != SBlocks.at(sgid).sympair.end(); ++sit) {
      if (sit->first < (int)Blocks.size()) {
        blist.push_back(sit->first);
      }
      if (sit->second < (int)Blocks.size()) {
        blist.push_back(sit->second);
      }
    }
    for (vector<pair<int, placerDB::Smark>>::iterator sit = SBlocks.at(sgid).selfsym.begin(); sit != SBlocks.at(sgid).selfsym.end(); ++sit) {
      if (sit->first < (int)Blocks.size()) {
        blist.push_back(sit->first);
      }  // cout<<"Push "<<sit->first<<endl;}
    }
    blist.push_back(SBlocks.at(sgid).dnode);
  }
  return blist;
}

vector<int> design::GetBlockListfromSymmGroup(int sgid) {
  vector<int> blist;
  if (sgid >= 0 && sgid < (int)SBlocks.size()) {
    for (vector<pair<int, int>>::iterator sit = SBlocks.at(sgid).sympair.begin(); sit != SBlocks.at(sgid).sympair.end(); ++sit) {
      blist.push_back(sit->first);
      blist.push_back(sit->second);
    }
    for (vector<pair<int, placerDB::Smark>>::iterator sit = SBlocks.at(sgid).selfsym.begin(); sit != SBlocks.at(sgid).selfsym.end(); ++sit) {
      blist.push_back(sit->first);
    }
  }
  return blist;
}

placerDB::point design::GetTerminalCenter(int teridx) { return Terminals.at(teridx).center; }

bool design::checkSymmetricBlockExist() {
  auto logger = spdlog::default_logger()->clone("placer.design.checkSymmetricBlockExist");
  bool mark = false;
  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (Blocks.at(i).size() == 0) {
      logger->error("Block {0} has size 0.", i);
    } else {
      if (Blocks.at(i).back().SBidx != -1) {
        mark = true;
        break;
      }
    }
  }
  return mark;
}

bool design::checkAsymmetricBlockExist() {
  auto logger = spdlog::default_logger()->clone("placer.design.checkASymmetricBlockExist");
  bool mark = false;
  for (unsigned int i = 0; i < Blocks.size(); ++i) {
    if (Blocks.at(i).size() == 0) {
      logger->error("Block {0} has size 0.", i);
    } else {
      if (Blocks.at(i).back().SBidx == -1) {
        mark = true;
        break;
      }
    }
  }
  return mark;
}

int design::CheckCommonSymmGroup(design& reducedNL, placerDB::SymmBlock& reducedSB) {
  for (vector<placerDB::SymmBlock>::iterator it = this->SBlocks.begin(); it != this->SBlocks.end(); ++it) {
    // for each symmetry group in current design *it
    for (vector<pair<int, int>>::iterator spit = it->sympair.begin(); spit != it->sympair.end(); ++spit) {
      // for each symmetry pair in current design *it
      for (vector<pair<int, int>>::iterator sqit = reducedSB.sympair.begin(); sqit != reducedSB.sympair.end(); ++sqit) {
        // for each symmetry pair in reduced design *sqit
        if (spit->first == reducedNL.GetMappedBlockIdx(sqit->first) && spit->second == reducedNL.GetMappedBlockIdx(sqit->second)) {
          return (it - this->SBlocks.begin());
        }
      }
    }
    for (vector<pair<int, placerDB::Smark>>::iterator sfit = it->selfsym.begin(); sfit != it->selfsym.end(); ++sfit) {
      // for each self-symmetry block in current design *it
      for (vector<pair<int, placerDB::Smark>>::iterator sgit = reducedSB.selfsym.begin(); sgit != reducedSB.selfsym.end(); ++sgit) {
        // for each self-symmetry block in reduced design *sgit
        if (sfit->first == reducedNL.GetMappedBlockIdx(sgit->first) && sfit->second == sgit->second) {
          return (it - this->SBlocks.begin());
        }
      }
    }
  }
  return -1;
}

int design::GetMappedBlockIdx(int idx) {
  if (idx >= 0 && idx < (int)Blocks.size()) {
    return Blocks.at(idx).back().mapIdx;
  } else {
    return -1;
  }
}

int design::GetMappedSymmBlockIdx(int idx) {
  if (idx >= 0 && idx < (int)SBlocks.size()) {
    return SBlocks.at(idx).mapIdx;
  } else {
    return -1;
  }
}

void design::ResetBlockMapIdx() {
  for (std::vector<std::vector<block>>::iterator it = this->Blocks.begin(); it != this->Blocks.end(); ++it) {
    for (unsigned int w = 0; w < it->size(); ++w) {
      it->at(w).mapIdx = -1;
    }
  }
}

void design::ResetSymmBlockMapIdx() {
  for (std::vector<placerDB::SymmBlock>::iterator it = this->SBlocks.begin(); it != this->SBlocks.end(); ++it) {
    it->mapIdx = -1;
  }
}

std::vector<placerDB::SymmBlock> design::SplitSymmBlock(design& reducedNL, int originIdx) {
  placerDB::SymmBlock comm, diff;
  placerDB::SymmBlock reducedSB = reducedNL.SBlocks.at(this->SBlocks.at(originIdx).mapIdx);
  placerDB::SymmBlock originSB = this->SBlocks.at(originIdx);
  for (std::vector<pair<int, int>>::iterator it = originSB.sympair.begin(); it != originSB.sympair.end(); ++it) {
    int origin1 = it->first;
    int origin2 = it->second;
    if (origin1 >= GetSizeofBlocks() || origin2 >= GetSizeofBlocks()) {
      continue;
    }
    bool mark = false;
    for (std::vector<pair<int, int>>::iterator it2 = reducedSB.sympair.begin(); it2 != reducedSB.sympair.end(); ++it2) {
      int reduced1 = reducedNL.Blocks.at(it2->first).back().mapIdx;
      int reduced2 = reducedNL.Blocks.at(it2->second).back().mapIdx;
      if (origin1 == reduced1 && origin2 == reduced2) {
        mark = true;
        break;
      }
    }
    if (mark) {
      comm.sympair.push_back(*it);
    } else {
      diff.sympair.push_back(*it);
    }
  }
  for (std::vector<pair<int, placerDB::Smark>>::iterator it = originSB.selfsym.begin(); it != originSB.selfsym.end(); ++it) {
    if (it->first >= GetSizeofBlocks()) {
      continue;
    }
    bool mark = false;
    for (std::vector<pair<int, placerDB::Smark>>::iterator it2 = reducedSB.selfsym.begin(); it2 != reducedSB.selfsym.end(); ++it2) {
      int reduced1 = reducedNL.Blocks.at(it2->first).back().mapIdx;
      if (it->first == reduced1 && it->second == it2->second) {
        mark = true;
        break;
      }
    }
    if (mark) {
      comm.selfsym.push_back(*it);
    } else {
      diff.selfsym.push_back(*it);
    }
  }
  std::vector<placerDB::SymmBlock> SBvect;
  SBvect.push_back(comm);
  SBvect.push_back(diff);
  return SBvect;
}

std::set<int> design::GetUnmappedBlocks() {
  std::set<int> unmap;
  for (unsigned int i = 0; i < this->Blocks.size(); i++) {
    if (this->Blocks.at(i).back().mapIdx == -1) {
      unmap.insert(i);
    }
  }
  return unmap;
}

int design::GetBlockMargin(int i, int j) {
  int margin = 0;
  for (unsigned int a = 0; a < this->Blocks.at(i).back().blockPins.size(); a++) {
    int inet = this->Blocks.at(i).back().blockPins.at(a).netIter;
    if (inet == -1) {
      continue;
    }
    for (vector<placerDB::Node>::iterator it = this->Nets.at(inet).connected.begin(); it != this->Nets.at(inet).connected.end(); ++it) {
      if (it->type == placerDB::Block && it->iter2 == j && this->Nets.at(inet).margin > margin) {
        margin = this->Nets.at(inet).margin;
        break;
      }
    }
  }
  return margin;
}

int design::GetBlockSymmGroupDnode(int i) {
  if (i < 0 || i >= (int)SBlocks.size()) {
    return -1;
  }
  return SBlocks.at(i).dnode;
}

size_t design::getSeqIndex(const vector<int>& seq) {
  size_t ind = 0;
  if (seq.size() <= 12 && _factorial.size() < seq.size()) {
    for (unsigned i = _factorial.size(); i < seq.size(); ++i) {
      if (i > 0)
        _factorial.push_back(i * _factorial[i - 1]);
      else
        _factorial.push_back(1);
    }
  }
  if (seq.size() <= 12) {
    for (unsigned i = 0; i < seq.size() - 1; ++i) {
      unsigned count = 0;
      for (unsigned j = i + 1; j < seq.size(); ++j)
        if (seq[i] > seq[j]) ++count;
      if (count > 0) ind += _factorial[seq.size() - i - 1] * count;
    }
  } else {
    const auto& it = _seqPairHash.find(seq);
    if (it != _seqPairHash.end())
      ind = it->second;
    else {
      const auto& sz = _seqPairHash.size();
      _seqPairHash.insert(std::make_pair(seq, sz));
      ind = sz;
    }
  }
  return ind;
}

size_t design::getSeqIndex(const vector<int>& seq) const {
  size_t ind = ULONG_MAX;
  if (seq.size() <= 12) {
    if (_factorial.size() < seq.size()) {
      for (unsigned i = _factorial.size(); i < seq.size(); ++i) {
        if (i > 0)
          const_cast<vector<size_t>&>(_factorial).push_back(i * _factorial[i - 1]);
        else
          const_cast<vector<size_t>&>(_factorial).push_back(1);
      }
    }
    ind = 0;
    for (unsigned i = 0; i < seq.size() - 1; ++i) {
      unsigned count = 0;
      for (unsigned j = i + 1; j < seq.size(); ++j)
        if (seq[i] > seq[j]) ++count;
      if (count > 0) ind += _factorial[seq.size() - i - 1] * count;
    }
  } else {
    const auto it = _seqPairHash.find(seq);
    if (it != _seqPairHash.end()) ind = it->second;
  }
  return ind;
}

size_t design::getSelIndex(const vector<int>& sel) {
  size_t ind = 0;
  auto it = _selHash.find(sel);
  if (it != _selHash.end())
    ind = it->second;
  else {
    auto sz = _selHash.size();
    _selHash.insert(std::make_pair(sel, sz));
    ind = sz;
  }
  return ind;
}

size_t design::getSelIndex(const vector<int>& sel) const {
  size_t ind = ULONG_MAX;
  const auto it = _selHash.find(sel);
  if (it != _selHash.end()) ind = it->second;
  return ind;
}

void design::cacheSeq(const vector<int>& p, const vector<int>& n, const vector<int>& sel, const double cost) {
  auto logger = spdlog::default_logger()->clone("placer.design.cacheSeq");
  auto pindx = getSeqIndex(p), nindx = getSeqIndex(n), sindx = getSelIndex(sel);
  if (_seqPairCache.empty()) {
    logger->debug("Using seq pair cache for {0} to reduce redundancy", name);
  }
  _seqPairCache[std::make_tuple(pindx, nindx, sindx)] = cost;
}

bool design::isSeqInCache(const vector<int>& p, const vector<int>& n, const vector<int>& sel, double* cost) const {
  if (!_useCache) return false;
  auto pindx = getSeqIndex(p), nindx = getSeqIndex(n), sindx = getSelIndex(sel);
  if (pindx != ULONG_MAX && nindx != ULONG_MAX && sindx != ULONG_MAX) {
    const auto it = _seqPairCache.find(std::make_tuple(pindx, nindx, sindx));
    if (it != _seqPairCache.end()) {
      if (cost) *cost = it->second;
      return true;
    }
  }
  return false;
}

design::~design() {
  delete _rnd;
  _rnd = nullptr;
  auto logger = spdlog::default_logger()->clone("placer.design.design");
  // logger->debug("sa__seq {0} unique_cnt={1} seq_pair_hash={2} sel_hash={3}", name, _seqPairCache.size(), _seqPairHash.size(), _selHash.size());
  // logger->debug("sa__infeasible {0} aspect_ratio={1} ilp_fail={2} placement_boundary={3} total_calls={4} num_ilp_calls={5}", name, _infeasAspRatio, _infeasILPFail,
  //               _infeasPlBound, _totalNumCostCalc, _numILPCalls);
  // logger->debug("sa_cpp_runtime Block {0} total ILP runtime : {1}", name, ilp_runtime.count());
  // logger->debug("sa_cpp_runtime Block {0} total ILPsolve runtime : {1}", name, ilp_solve_runtime.count());
  // logger->debug("sa_cpp_runtime Block {0} total gen valid runtime : {1}", name, gen_valid_runtime.count());
  // logger->debug("sa__num_snap_grid_fails : {0}", _numSnapGridFail);
  //_debugofs.close();
}
