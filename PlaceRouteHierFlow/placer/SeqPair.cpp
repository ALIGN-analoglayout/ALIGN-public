#define CATCH_INFINITE_LOOP

#include "SeqPair.h"

#include <exception>
#include <set>
#include <unordered_set>

#include "spdlog/spdlog.h"

bool OrderedEnumerator::TopoSortUtil(vector<int>& res, map<int, bool>& visited) {
  if (_sequences.size() > _maxSeq) {
    return false;
  }
  bool flag = false;
  for (auto& it : _seq) {
    if (_indegree[it] == 0 && !visited[it]) {
      for (auto& adjit : _adj[it]) {
        _indegree[adjit]--;
      }
      res.push_back(it);
      visited[it] = true;
      if (!TopoSortUtil(res, visited)) return false;

      visited[it] = false;
      res.erase(res.end() - 1);
      for (auto& adjit : _adj[it]) {
        _indegree[adjit]++;
      }
      flag = true;
    }
  }

  if (!flag) {
    _sequences.push_back(res);
  }
  return (_sequences.size() <= _maxSeq);
}

OrderedEnumerator::OrderedEnumerator(const vector<int>& seq, const vector<pair<pair<int, int>, placerDB::Smark>>& constraints, const int maxSeq, const bool pos)
    : _seq(seq), _cnt(0), _maxSeq(maxSeq), _valid(!constraints.empty()) {
  if (constraints.empty()) return;
  std::sort(_seq.begin(), _seq.end());

  for (auto& it : _seq) {
    _indegree[it] = 0;
    _adj[it].clear();
  }

  auto logger = spdlog::default_logger()->clone("placer.OrderedEnumerator.OrderedEnumerator");
  for (auto& it : constraints) {
    int first(-1), second(-1);
    if (it.second == placerDB::V) {  // vertical
      if (pos) {
        first = it.first.first;
        second = it.first.second;
      } else {
        first = it.first.second;
        second = it.first.first;
      }
    } else {  // horizontal
      first = it.first.first;
      second = it.first.second;
    }
    _adj[first].push_back(second);
    ++_indegree[second];
  }
  map<int, bool> visited;
  for (auto& it : seq) {
    visited[it] = false;
  }
  vector<int> res;
  TopoSortUtil(res, visited);
  _valid = (_sequences.size() <= _maxSeq);
  if (!_valid) {
    _sequences.clear();
  }
  _seq.clear();
  _indegree.clear();
  _adj.clear();
  // logger->debug("num sequences {0} {1} {2}", _sequences.size(), constraints.size(), (_valid ? 1 : 0));
  /*string str;
  for (auto& it : _sequences) {
    str.clear();
    for (auto& r : it) {
      str += (std::to_string(r) + " ");
    }
    logger->info("seq : {0} {1}", pos, str);
  }*/
}

SeqPairEnumerator::SeqPairEnumerator(const vector<int>& pair, design& casenl, const size_t maxIter)
    : _enumIndex({0, 0}),
      _exhausted(0),
      _valid(1),
      _posPair(pair),
      _maxEnum(SeqPair::Factorial(_posPair.size())),
      _posEnumerator(pair, casenl.Ordering_Constraints, ceil(sqrt(maxIter)), true),
      _negEnumerator(pair, casenl.Ordering_Constraints, ceil(sqrt(maxIter)), false) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPairEnumerator.SeqPairEnumerator");
  size_t totEnum = _maxEnum * _maxEnum;
  if (!_posEnumerator.valid()) {
    if (maxIter > 0 && _posPair.size() <= 16 && maxIter > totEnum) {
      // totEnum *= (1 << (2*caseNL.GetSizeofBlocks()));
      for (unsigned i = 0; i < casenl.GetSizeofBlocks(); ++i) {
        totEnum *= casenl.Blocks.at(i).size();
        if (maxIter < totEnum) {
          _valid = 0;
          break;
        }
      }
    } else {
      _valid = 0;
    }
    logger->debug("enumeration check valid : {0}\n maxIter : {1} seq pair size : {2} total enumerations : {3}", (_valid ? 1 : 0), maxIter, _posPair.size(),
                  totEnum);
  } else {
    _maxEnum = _posEnumerator.NumSequences();
  }
  if (!_valid) return;
  std::sort(_posPair.begin(), _posPair.end());
  _negPair = _posPair;

  _selected.resize(casenl.GetSizeofBlocks(), 0);
  _maxSelected.reserve(casenl.GetSizeofBlocks());
  _maxSize = 0;
  for (unsigned i = 0; i < casenl.GetSizeofBlocks(); ++i) {
    auto s = static_cast<int>(casenl.Blocks.at(i).size());
    _maxSize = std::max(_maxSize, s);
    _maxSelected.push_back(s);
  }
  //_hflip = 0;
  //_vflip = 0;
  //_maxFlip = (1 << casenl.GetSizeofBlocks());
  // logger->info("maxflip : {0}", _maxFlip);
}

const bool SeqPairEnumerator::IncrementSelected() {
  // auto logger = spdlog::default_logger()->clone("placer.SeqPairEnumerator.IncrementSelected");
  if (_maxSize <= 1) return false;
  int i = _selected.size() - 1;
  int rem = 1;
  while (i >= 0) {
    auto ui = static_cast<unsigned>(i);
    _selected[ui] += rem;
    if (_selected[ui] >= _maxSelected[ui]) {
      _selected[ui] = 0;
      rem = 1;
    } else {
      rem = 0;
      break;
    }
    --i;
  }
  return rem ? false : true;
}

/*vector<int> SeqPairEnumerator::GetFlip(const bool hor) const
{
  vector<int> flipVec;
  flipVec.reserve(_maxSelected.size());
  const size_t flip = hor ? _hflip : _vflip;
  for (unsigned i = 1; i < _maxFlip; i = (i << 1)) {
    flipVec.push_back((flip & i) ? 1 : 0);
  }
  return flipVec;
}*/

/*bool SeqPairEnumerator::EnumFlip() {
  if (++_hflip >= _maxFlip) {
    _hflip = 0;
    if (++_vflip >= _maxFlip) {
      _vflip = 0;
      return false;
    }
  }
  return true;
}*/

void SeqPairEnumerator::Permute() {
  // auto logger = spdlog::default_logger()->clone("placer.SeqPairEnumerator.Permute");
  // if (!EnumFlip())
  if (_exhausted) return;
  if (!IncrementSelected()) {
    if (_enumIndex.second >= _maxEnum - 1) {
      std::sort(_negPair.begin(), _negPair.end());
      _enumIndex.second = 0;
      ++_enumIndex.first;
      if (_posEnumerator.valid())
        _posEnumerator.NextPermutation(_posPair, _enumIndex.first);
      else
        std::next_permutation(std::begin(_posPair), std::end(_posPair));
    } else {
      ++_enumIndex.second;
      if (_negEnumerator.valid())
        _negEnumerator.NextPermutation(_negPair, _enumIndex.second);
      else
        std::next_permutation(std::begin(_negPair), std::end(_negPair));
    }
  }
  if (_enumIndex.first >= _maxEnum) _exhausted = true;
  // logger->info("enum index : {0} {1}", _enumIndex.first, _enumIndex.second);
}

SeqPair::SeqPair() {
  this->posPair.clear();
  this->negPair.clear();
  this->orient.clear();
  this->symAxis.clear();
  this->selected.clear();
}

// SeqPair::SeqPair(int blockSize) {
//// For testing
//  for(int i=0;i<blockSize;i++) {
//    posPair.push_back(i);
//    negPair.push_back(i);
//    orient.push_back(placerDB::N);
//  }
//}

// SeqPair::SeqPair(string pos, string neg) {
//// For testing
//  vector<string> temp1=split_by_spaces(pos);
//  vector<string> temp2=split_by_spaces(neg);
//  for(vector<string>::iterator it=temp1.begin(); it!=temp1.end()-1; ++it) {
//    posPair.push_back(stoi(*it));
//  }
//  for(vector<string>::iterator it=temp2.begin(); it!=temp2.end()-1; ++it) {
//    negPair.push_back(stoi(*it));
//  }
//  for(int i=0;i<(int)posPair.size();++i) {orient.push_back(placerDB::N);}
//}

SeqPair::SeqPair(const SeqPair& sp) {
  this->posPair = sp.posPair;
  this->negPair = sp.negPair;
  this->orient = sp.orient;
  this->symAxis = sp.symAxis;
  this->selected = sp.selected;
  if (!_seqPairEnum) this->_seqPairEnum = sp._seqPairEnum;
}

void SeqPair::InsertNewSBlock(design& originNL, int originIdx) {
  // std::cout<<"InsertNewSBlock "<<originIdx<<std::endl;
  placerDB::Smark axis;
  vector<placerDB::SymmBlock>::iterator bit = originNL.SBlocks.begin() + originIdx;
  // axis=bit->axis_dir;
  // axis=placerDB::V; // initialize veritcal symmetry
  /*
  if ( !(bit->selfsym).empty() ) {
    switch( (bit->selfsym).at(0).second ) {
      case placerDB::H: axis=placerDB::V;break;
      case placerDB::V: axis=placerDB::H;break;
    }
  }
 */
  axis = bit->axis_dir;
  // cout<<"axis"<<axis<<endl;
  this->symAxis.at(originIdx) = axis;
  // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
  // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
  if (!bit->sympair.empty()) {
    for (vector<pair<int, int>>::iterator pit = bit->sympair.begin(); pit != bit->sympair.end(); ++pit) {
      if (pit->first < (int)originNL.GetSizeofBlocks()) {
        posPair.push_back(pit->first);  // a1,a2,...,ap --> positive
        orient[pit->first] = placerDB::N;
      }
    }
  }
  posPair.push_back(bit->dnode);  // axis --> positive
  if (!bit->selfsym.empty()) {
    for (vector<pair<int, placerDB::Smark>>::iterator sit = bit->selfsym.begin(); sit != bit->selfsym.end(); ++sit) {
      if (sit->first < (int)originNL.GetSizeofBlocks()) {
        posPair.push_back(sit->first);  // c1,...cs --> positve
        orient[sit->first] = placerDB::N;
      }
    }
  }
  if (!bit->sympair.empty()) {
    // for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
    for (vector<pair<int, int>>::reverse_iterator pit = bit->sympair.rbegin(); pit != bit->sympair.rend(); ++pit) {
      if (pit->second < (int)originNL.GetSizeofBlocks()) {
        posPair.push_back(pit->second);  // bp,...,b1 --> positive
        if (axis == placerDB::V) {
          orient[pit->second] = placerDB::FN;
        } else if (axis == placerDB::H) {
          orient[pit->second] = placerDB::FS;
        }
      }
    }
  }
  // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
  // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
  if (axis == placerDB::V) {
    if (!bit->sympair.empty()) {
      for (vector<pair<int, int>>::iterator pit = bit->sympair.begin(); pit != bit->sympair.end(); ++pit) {
        if (pit->first < (int)originNL.GetSizeofBlocks()) {
          negPair.push_back(pit->first);  // a1,a2,...,ap --> negative
        }
      }
    }
    if (!bit->selfsym.empty()) {
      // for(vector< pair<int,placerDB::Smark> >::iterator sit=bit->selfsym.end()-1; sit>=bit->selfsym.begin(); --sit) {
      for (vector<pair<int, placerDB::Smark>>::reverse_iterator sit = bit->selfsym.rbegin(); sit != bit->selfsym.rend(); ++sit) {
        if (sit->first < (int)originNL.GetSizeofBlocks()) {
          negPair.push_back(sit->first);  // cs,...c1 --> negative
        }
      }
    }
    negPair.push_back(bit->dnode);  // axis --> negative
    if (!bit->sympair.empty()) {
      // for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
      for (vector<pair<int, int>>::reverse_iterator pit = bit->sympair.rbegin(); pit != bit->sympair.rend(); ++pit) {
        if (pit->second < (int)originNL.GetSizeofBlocks()) {
          negPair.push_back(pit->second);  // bp,...,b1 --> positive
        }
      }
    }
  } else if (axis == placerDB::H) {
    if (!bit->sympair.empty()) {
      for (vector<pair<int, int>>::iterator pit = bit->sympair.begin(); pit != bit->sympair.end(); ++pit) {
        if (pit->second < (int)originNL.GetSizeofBlocks()) {
          negPair.push_back(pit->second);  // b1,...,bp --> negative
        }
      }
    }
    negPair.push_back(bit->dnode);  // axis --> negative
    if (!bit->selfsym.empty()) {
      for (vector<pair<int, placerDB::Smark>>::iterator sit = bit->selfsym.begin(); sit != bit->selfsym.end(); ++sit) {
        if (sit->first < (int)originNL.GetSizeofBlocks()) {
          negPair.push_back(sit->first);  // c1,...cs --> negative
        }
      }
    }
    if (!bit->sympair.empty()) {
      // for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
      for (vector<pair<int, int>>::reverse_iterator pit = bit->sympair.rbegin(); pit != bit->sympair.rend(); ++pit) {
        if (pit->first < (int)originNL.GetSizeofBlocks()) {
          negPair.push_back(pit->first);  // ap,...,a1 --> negative
        }
      }
    }
  }
}

void SeqPair::CompactSeq() {
  vector<int> temp_p;

  for (unsigned int i = 0; i < posPair.size(); ++i) {
    for (unsigned int j = i + 1; j < posPair.size(); ++j) {
      if (posPair[i] == posPair[j]) {
        posPair[j] = -1;
      }
    }
  }

  for (unsigned int i = 0; i < posPair.size(); ++i) {
    if (posPair[i] != -1) {
      temp_p.push_back(posPair[i]);
    }
  }

  vector<int> temp_n;

  for (unsigned int i = 0; i < negPair.size(); ++i) {
    for (unsigned int j = i + 1; j < negPair.size(); ++j) {
      if (negPair[i] == negPair[j]) {
        negPair[j] = -1;
      }
    }
  }

  for (unsigned int i = 0; i < negPair.size(); ++i) {
    if (negPair[i] != -1) {
      temp_n.push_back(negPair[i]);
    }
  }

  posPair = temp_p;
  negPair = temp_n;
}

SeqPair::SeqPair(design& caseNL, const size_t maxIter) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.SeqPair");

  // Know limitation: currently we force all symmetry group in veritcal symmetry
  placerDB::Smark axis;
  orient.resize(caseNL.GetSizeofBlocks());
  selected.resize(caseNL.GetSizeofBlocks(), 0);

  int sym_group_index = 0;
  for (vector<placerDB::SymmBlock>::iterator bit = caseNL.SBlocks.begin(); bit != caseNL.SBlocks.end(); ++bit) {
    axis = bit->axis_dir;
    sym_group_index++;
    // cout<<"axis"<<axis<<endl;
    symAxis.push_back(axis);
    // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
    // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
    if (!bit->sympair.empty()) {
      for (vector<pair<int, int>>::iterator pit = bit->sympair.begin(); pit != bit->sympair.end(); ++pit) {
        if (pit->first < (int)caseNL.GetSizeofBlocks()) {
          // std::<<pit->first<<","<<pit->secode<<" ";
          posPair.push_back(pit->first);  // a1,a2,...,ap --> positive
          orient[pit->first] = placerDB::N;
        }
      }
    }
    posPair.push_back(bit->dnode);  // axis --> positive
    if (!bit->selfsym.empty()) {
      for (vector<pair<int, placerDB::Smark>>::iterator sit = bit->selfsym.begin(); sit != bit->selfsym.end(); ++sit) {
        if (sit->first < (int)caseNL.GetSizeofBlocks()) {
          posPair.push_back(sit->first);  // c1,...cs --> positve
          orient[sit->first] = placerDB::N;
        }
      }
    }
    if (!bit->sympair.empty()) {
      for (vector<pair<int, int>>::reverse_iterator pit = bit->sympair.rbegin(); pit != bit->sympair.rend(); ++pit) {
        if (pit->second < (int)caseNL.GetSizeofBlocks()) {
          posPair.push_back(pit->second);  // bp,...,b1 --> positive
          if (axis == placerDB::V) {
            orient[pit->second] = placerDB::FN;
          } else if (axis == placerDB::H) {
            orient[pit->second] = placerDB::FS;
          }
        }
      }
    }
    // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
    // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
    if (axis == placerDB::V) {
      if (!bit->sympair.empty()) {
        for (vector<pair<int, int>>::iterator pit = bit->sympair.begin(); pit != bit->sympair.end(); ++pit) {
          if (pit->first < (int)caseNL.GetSizeofBlocks()) {
            negPair.push_back(pit->first);  // a1,a2,...,ap --> negative
          }
        }
      }
      if (!bit->selfsym.empty()) {
        for (vector<pair<int, placerDB::Smark>>::reverse_iterator sit = bit->selfsym.rbegin(); sit != bit->selfsym.rend(); ++sit) {
          if (sit->first < (int)caseNL.GetSizeofBlocks()) {
            negPair.push_back(sit->first);  // cs,...c1 --> negative
          }
        }
      }
      negPair.push_back(bit->dnode);  // axis --> negative
      if (!bit->sympair.empty()) {
        for (vector<pair<int, int>>::reverse_iterator pit = bit->sympair.rbegin(); pit != bit->sympair.rend(); ++pit) {
          if (pit->second < (int)caseNL.GetSizeofBlocks()) {
            negPair.push_back(pit->second);  // bp,...,b1 --> positive
          }
        }
      }
    } else if (axis == placerDB::H) {
      if (!bit->sympair.empty()) {
        for (vector<pair<int, int>>::iterator pit = bit->sympair.begin(); pit != bit->sympair.end(); ++pit) {
          if (pit->second < (int)caseNL.GetSizeofBlocks()) {
            negPair.push_back(pit->second);  // b1,...,bp --> negative
          }
        }
      }
      negPair.push_back(bit->dnode);  // axis --> negative
      if (!bit->selfsym.empty()) {
        for (vector<pair<int, placerDB::Smark>>::iterator sit = bit->selfsym.begin(); sit != bit->selfsym.end(); ++sit) {
          if (sit->first < (int)caseNL.GetSizeofBlocks()) {
            negPair.push_back(sit->first);  // c1,...cs --> negative
          }
        }
      }
      if (!bit->sympair.empty()) {
        for (vector<pair<int, int>>::reverse_iterator pit = bit->sympair.rbegin(); pit != bit->sympair.rend(); ++pit) {
          if (pit->first < (int)caseNL.GetSizeofBlocks()) {
            negPair.push_back(pit->first);  // ap,...,a1 --> negative
          }
        }
      }
    }
  }

  CompactSeq();

  for (int i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
    if (caseNL.GetBlockSymmGroup(i) == -1) {
      posPair.push_back(i);
      negPair.push_back(i);
      orient.at(i) = placerDB::N;
    }
  }

  bool ok = KeepOrdering(caseNL);
  // logger->info("KeepOrdering end: {0}", ok);

  SameSelected(caseNL);

  _seqPairEnum = std::make_shared<SeqPairEnumerator>(posPair, caseNL, maxIter);

  if (_seqPairEnum->valid()) {
    logger->info("Enumerated search");
  } else {
    _seqPairEnum.reset();
  }
}

SeqPair& SeqPair::operator=(const SeqPair& sp) {
  // auto logger = spdlog::default_logger()->clone("placer.SeqPair.=");
  this->posPair = sp.posPair;
  this->negPair = sp.negPair;
  this->orient = sp.orient;
  this->symAxis = sp.symAxis;
  this->selected = sp.selected;
  if (!_seqPairEnum) this->_seqPairEnum = sp._seqPairEnum;
  return *this;
}

void SeqPair::PrintVec(const std::string& tag, const std::vector<int>& vec) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.PrintVec");
  if (logger->should_log(spdlog::level::trace)) {
    std::string tmpstr;
    for (const auto& it : vec) tmpstr += (std::to_string(it) + " ");
    logger->trace("{0} {1}", tag, tmpstr);
  }
}

void SeqPair::PrintSeqPair() {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.PrintSeqPair");

  if (logger->should_log(spdlog::level::debug)) {
    logger->debug("=== Sequence Pair ===");
    std::string tmpstr;
    for (const auto& it : posPair) tmpstr += (std::to_string(it) + " ");
    logger->debug("Positive pair: {0}", tmpstr);

    tmpstr = "";
    for (const auto& it : negPair) tmpstr += (std::to_string(it) + " ");
    logger->debug("Negative pair: {0}", tmpstr);

    tmpstr = "";
    for (const auto& it : orient) tmpstr += (std::to_string(it) + " ");
    logger->debug("Orientation: {0}", tmpstr);

    tmpstr = "";
    for (const auto& it : symAxis) tmpstr += (it ? "H " : "V ");
    logger->debug("Symmetry axis: {0}", tmpstr);

    tmpstr = "";
    for (const auto& it : selected) tmpstr += (std::to_string(it) + " ");
    logger->debug("Selected: {0}", tmpstr);
    // cout<<endl;
  }
}

void SeqPair::SameSelected(design& caseNL) {
  for (const auto& group : caseNL.Same_Template_Constraints) {
    int id = selected[*group.begin()];
    for (const auto& i : group) selected[i] = id;
  }
}

int SeqPair::GetBlockSelected(int blockNo) {
  if (blockNo >= 0 && blockNo < (int)selected.size()) {
    return (selected.at(blockNo));
  }
  return -1;
}

vector<int> SeqPair::FindShortSeq(design& caseNL, vector<int>& seq, int idx) {
  vector<int> newQ;
  for (vector<int>::iterator it = seq.begin(); it != seq.end(); ++it) {
    if (*it < caseNL.GetSizeofBlocks() && *it >= 0) {
      if (caseNL.GetBlockSymmGroup(*it) == idx) {
        newQ.push_back(*it);
      }
    }
  }
  return newQ;
}

int SeqPair::GetVertexIndexinSeq(vector<int>& seq, int v) {
  int idx = -1;
  for (int i = 0; i < (int)seq.size(); ++i) {
    if (seq.at(i) == v) {
      idx = i;
      break;
    }
  }
  return idx;
}

placerDB::Smark SeqPair::GetSymmBlockAxis(int SBidx) { return symAxis.at(SBidx); }

bool SeqPair::ChangeSelectedBlock(design& caseNL) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.ChangeSelectedBlock");
  int anode = caseNL.rand() % caseNL.GetSizeofBlocks();
  if (caseNL.mixFlag) {
    while (caseNL.GetMappedBlockIdx(anode) != -1) {
      anode = caseNL.rand() % caseNL.GetSizeofBlocks();
    }  // randomly choose a block
  }
  if (caseNL.Blocks.at(anode).size() <= 1) {
    if (caseNL.Blocks.at(anode).size() < 1) logger->debug("anode size < 1");
    return false;
  }
  int newsel = caseNL.rand() % caseNL.Blocks.at(anode).size();
  selected.at(anode) = newsel;
  // if(caseNL.GetBlockCounterpart(anode)!=-1) {
  // selected.at( caseNL.GetBlockCounterpart(anode) )=newsel;
  //}
  return true;
}

/**
bool SeqPair::ValidateSelect(design & caseNL){
  //two sym pair blocks have conflict with place on grid
  // for(auto sympairblock:caseNL.SPBlocks){
  //   for(auto sympair:sympairblock.sympair){
  //     if(caseNL.Blocks[sympair.first][selected[sympair.first]].ypitch>1 && caseNL.Blocks[sympair.second][selected[sympair.second]].ypitch>1){
  //       if(caseNL.Blocks[sympair.first][selected[sympair.first]].ypitch>1 && caseNL.Blocks[sympair.second][selected[sympair.second]].ypitch>1)
  //     }
  //   }
  // }
  return true;
}**/
bool SeqPair::KeepOrdering(design& caseNL) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.KeepOrdering");

  {
#ifdef CATCH_INFINITE_LOOP
    std::unordered_set<std::vector<int>, VectorHasher> visitedPosPair = {posPair};
#endif

    bool pos_keep_order;

    std::vector<int> blocks2sort;               // the block with ordering constraints
    std::vector<int> blocks_original_position;  // the blocks position in the seqpair
    std::map<int, int> blockid2indexinvec;
    std::vector<int> blockid_after_sort;
    vector<vector<int>> adj;
    vector<int> ind;
    std::queue<int> q;
    for (const auto& order : caseNL.Ordering_Constraints) {
      if (find(blocks2sort.begin(), blocks2sort.end(), order.first.first) == blocks2sort.end()) {
        blocks2sort.push_back(order.first.first);  // store blocks to sort
        blockid2indexinvec[blocks2sort.back()] = int(blocks2sort.size() - 1);
      }
      if (find(blocks2sort.begin(), blocks2sort.end(), order.first.second) == blocks2sort.end()) {
        blocks2sort.push_back(order.first.second);
        blockid2indexinvec[blocks2sort.back()] = int(blocks2sort.size() - 1);  // store block index in vec
      }
    }
    adj.resize(blocks2sort.size());
    ind.resize(blocks2sort.size());
    for (const auto& b : blocks2sort) {
      blocks_original_position.push_back(find(posPair.begin(), posPair.end(), b) - posPair.begin());
    }
    for (const auto& order : caseNL.Ordering_Constraints) {
      int first_it = blockid2indexinvec[order.first.first];
      int second_it = blockid2indexinvec[order.first.second];
      if (find(adj[first_it].begin(), adj[first_it].end(), second_it) == adj[first_it].end()) {
        adj[first_it].push_back(second_it);
        ind[second_it]++;
      }
    }
    for (unsigned int i = 0; i < blocks2sort.size(); i++) {
      int it = blockid2indexinvec[blocks2sort[i]];
      if (ind[it] == 0) q.push(it);
    }
    while (!q.empty()) {
      int v = q.front();
      q.pop();
      blockid_after_sort.push_back(blocks2sort[v]);
      std::random_shuffle(adj[v].begin(), adj[v].end(), [](int i) { return std::rand() % i; });
      for (auto& it : adj[v]) {
        ind[it]--;
        if (ind[it] == 0) q.push(it);
      }
    }
    sort(blocks_original_position.begin(), blocks_original_position.end());
    for (unsigned int i = 0; i < blockid_after_sort.size(); i++) {
      posPair[blocks_original_position[i]] = blockid_after_sort[i];
    }

    do {
#ifdef CATCH_INFINITE_LOOP
      logger->trace("====Fixup pos order====");
      PrintVec("Before:", posPair);
#endif

      int first_it, second_it;
      pos_keep_order = true;
      for (const auto& order : caseNL.Ordering_Constraints) {
        first_it = find(posPair.begin(), posPair.end(), order.first.first) - posPair.begin();
        second_it = find(posPair.begin(), posPair.end(), order.first.second) - posPair.begin();
        assert(first_it != posPair.end() - posPair.begin());
        assert(second_it != posPair.end() - posPair.begin());
        if (first_it - second_it > 0) {
          logger->trace("Fixup pos: {0} at pos {1} is after {2} at pos {3}", order.first.first, first_it, order.first.second, second_it);
          pos_keep_order = false;
          int first_counterpart = caseNL.Blocks[order.first.first][0].counterpart;
          int second_counterpart = caseNL.Blocks[order.first.second][0].counterpart;
          auto it = posPair.begin();
          if (first_counterpart == -1) {
            posPair.erase(it + first_it);
            it = posPair.insert(it + second_it, order.first.first);
            // move first to before second
          } else if (second_counterpart == -1) {
            it = posPair.insert(it + first_it + 1, order.first.second);
            it = posPair.begin();
            posPair.erase(it + second_it);
            // move second to after first
          } else {
            swap(posPair.at(first_it), posPair.at(second_it));
          }

          break;
        }
      }
#ifdef CATCH_INFINITE_LOOP
      PrintVec("After: ", posPair);
      if (!pos_keep_order && visitedPosPair.find(posPair) != visitedPosPair.end()) {
        // logger->critical("Infinite loop in posPair loop.");
        return false;
      } else {
        visitedPosPair.insert(posPair);
      }
#endif
    } while (!pos_keep_order);
  }
  {
    bool neg_keep_order;

#ifdef CATCH_INFINITE_LOOP
    std::unordered_set<std::vector<int>, VectorHasher> visitedNegPair = {negPair};
#endif
    std::vector<int> blocks2sort;               // the block with ordering constraints
    std::vector<int> blocks_original_position;  // the blocks position in the seqpair
    std::map<int, int> blockid2indexinvec;
    std::vector<int> blockid_after_sort;
    vector<vector<int>> adj;
    vector<int> ind;
    std::queue<int> q;
    for (const auto& order : caseNL.Ordering_Constraints) {
      if (find(blocks2sort.begin(), blocks2sort.end(), order.first.first) == blocks2sort.end()) {
        blocks2sort.push_back(order.first.first);  // store blocks to sort
        blockid2indexinvec[blocks2sort.back()] = int(blocks2sort.size() - 1);
      }
      if (find(blocks2sort.begin(), blocks2sort.end(), order.first.second) == blocks2sort.end()) {
        blocks2sort.push_back(order.first.second);
        blockid2indexinvec[blocks2sort.back()] = int(blocks2sort.size() - 1);  // store block index in vec
      }
    }
    adj.resize(blocks2sort.size());
    ind.resize(blocks2sort.size());
    for (const auto& b : blocks2sort) {
      blocks_original_position.push_back(find(negPair.begin(), negPair.end(), b) - negPair.begin());
    }
    for (const auto& order : caseNL.Ordering_Constraints) {
      if (order.second == placerDB::H) {
        int first_it = blockid2indexinvec[order.first.first];
        int second_it = blockid2indexinvec[order.first.second];
        if (find(adj[first_it].begin(), adj[first_it].end(), second_it) == adj[first_it].end()) {
          adj[first_it].push_back(second_it);
          ind[second_it]++;
        }
      } else {
        int first_it = blockid2indexinvec[order.first.first];
        int second_it = blockid2indexinvec[order.first.second];
        if (find(adj[second_it].begin(), adj[second_it].end(), first_it) == adj[second_it].end()) {
          adj[second_it].push_back(first_it);
          ind[first_it]++;
        }
      }
    }
    // check align_blocks
    for (const auto& alignblock : caseNL.Align_blocks) {
      if (alignblock.horizon) {
        for (unsigned int i = 0; i < alignblock.blocks.size(); i++) {
          if (find(blocks2sort.begin(), blocks2sort.end(), alignblock.blocks[i]) == blocks2sort.end()) continue;
          for (unsigned int j = i + 1; j < alignblock.blocks.size(); j++) {
            if (find(blocks2sort.begin(), blocks2sort.end(), alignblock.blocks[j]) == blocks2sort.end()) continue;
            auto it1 = find(posPair.begin(), posPair.end(), alignblock.blocks[i]);
            auto it2 = find(posPair.begin(), posPair.end(), alignblock.blocks[j]);
            if (it1 < it2 &&
                find(adj[alignblock.blocks[i]].begin(), adj[alignblock.blocks[i]].end(), alignblock.blocks[j]) == adj[alignblock.blocks[i]].end()) {
              adj[alignblock.blocks[i]].push_back(alignblock.blocks[j]);
              ind[alignblock.blocks[j]]++;
            } else if (it1 > it2 &&
                       find(adj[alignblock.blocks[j]].begin(), adj[alignblock.blocks[j]].end(), alignblock.blocks[i]) == adj[alignblock.blocks[j]].end()) {
              adj[alignblock.blocks[j]].push_back(alignblock.blocks[i]);
              ind[alignblock.blocks[i]]++;
            }
          }
        }
      } else {
        for (unsigned int i = 0; i < alignblock.blocks.size(); i++) {
          if (find(blocks2sort.begin(), blocks2sort.end(), alignblock.blocks[i]) == blocks2sort.end()) continue;
          for (unsigned int j = i + 1; j < alignblock.blocks.size(); j++) {
            if (find(blocks2sort.begin(), blocks2sort.end(), alignblock.blocks[j]) == blocks2sort.end()) continue;
            auto it1 = find(posPair.begin(), posPair.end(), alignblock.blocks[i]);
            auto it2 = find(posPair.begin(), posPair.end(), alignblock.blocks[j]);
            if (it1 < it2 &&
                find(adj[alignblock.blocks[j]].begin(), adj[alignblock.blocks[j]].end(), alignblock.blocks[i]) == adj[alignblock.blocks[j]].end()) {
              adj[alignblock.blocks[j]].push_back(alignblock.blocks[i]);
              ind[alignblock.blocks[i]]++;
            } else if (it1 > it2 &&
                       find(adj[alignblock.blocks[i]].begin(), adj[alignblock.blocks[i]].end(), alignblock.blocks[j]) == adj[alignblock.blocks[i]].end()) {
              adj[alignblock.blocks[i]].push_back(alignblock.blocks[j]);
              ind[alignblock.blocks[j]]++;
            }
          }
        }
      }
    }
    for (unsigned int i = 0; i < blocks2sort.size(); i++) {
      int it = blockid2indexinvec[blocks2sort[i]];
      if (ind[it] == 0) q.push(it);
    }
    while (!q.empty()) {
      int v = q.front();
      q.pop();
      blockid_after_sort.push_back(blocks2sort[v]);
      std::random_shuffle(adj[v].begin(), adj[v].end(), [](int i) { return std::rand() % i; });
      for (auto& it : adj[v]) {
        ind[it]--;
        if (ind[it] == 0) q.push(it);
      }
    }
    sort(blocks_original_position.begin(), blocks_original_position.end());
    for (unsigned int i = 0; i < blockid_after_sort.size(); i++) {
      negPair[blocks_original_position[i]] = blockid_after_sort[i];
    }
    // generate a neg order
    do {
#ifdef CATCH_INFINITE_LOOP
      logger->trace("====Fixup neg order====");
      PrintVec("Before:", negPair);
#endif
      int first_it, second_it;
      neg_keep_order = true;
      for (const auto& order : caseNL.Ordering_Constraints) {
        first_it = find(negPair.begin(), negPair.end(), order.first.first) - negPair.begin();
        second_it = find(negPair.begin(), negPair.end(), order.first.second) - negPair.begin();
        assert(first_it != negPair.end() - negPair.begin());
        assert(second_it != negPair.end() - negPair.begin());
        if (first_it - second_it < 0) {
          logger->trace("Fixup neg: {0} at pos {1} is before {2} at pos {3}", order.first.first, first_it, order.first.second, second_it);
          if (order.second == placerDB::V) {
            neg_keep_order = false;
            int first_counterpart = caseNL.Blocks[order.first.first][0].counterpart;
            int second_counterpart = caseNL.Blocks[order.first.second][0].counterpart;
            auto it = negPair.begin();
            logger->trace("Order: {0} {1}", order.first.first, order.first.second);
            logger->trace("Counterparts: {0} {1}", first_counterpart, second_counterpart);
            if (first_counterpart == -1 || first_counterpart == order.first.first) {
              // move first to after second
              it = negPair.insert(it + second_it + 1, order.first.first);
              it = negPair.begin();
              negPair.erase(it + first_it);
            } else if (second_counterpart == -1) {
              // mvoe second to before first
              negPair.erase(it + second_it);
              it = negPair.insert(it + first_it, order.first.second);
            } else {
              swap(negPair.at(first_it), negPair.at(second_it));
            }
            break;
          }
        } else if (order.second == placerDB::H) {
          neg_keep_order = false;
          int first_counterpart = caseNL.Blocks[order.first.first][0].counterpart;
          int second_counterpart = caseNL.Blocks[order.first.second][0].counterpart;
          auto it = negPair.begin();
          if (first_counterpart == -1) {
            // mvoe second to after first
            it = negPair.insert(it + first_it + 1, order.first.second);
            it = negPair.begin();
            negPair.erase(it + second_it);
          } else if (second_counterpart == -1) {
            // move first to before second
            negPair.erase(it + first_it);
            it = negPair.insert(it + second_it, order.first.first);
          } else {
            swap(negPair.at(first_it), negPair.at(second_it));
          }
          break;
        }
      }
#ifdef CATCH_INFINITE_LOOP
      PrintVec("After: ", negPair);
      if (!neg_keep_order && visitedNegPair.find(negPair) != visitedNegPair.end()) {
        // logger->critical("Infinite loop in negPair loop.");
        return false;
      } else {
        visitedNegPair.insert(negPair);
      }
#endif

      if (!neg_keep_order && visitedNegPair.find(negPair) != visitedNegPair.end()) {
        logger->critical("Infinite loop in negPair loop.");
        return false;
      } else {
        visitedNegPair.insert(negPair);
      }

    } while (!neg_keep_order);
  }
  return true;
}

inline size_t SeqPair::Factorial(const size_t& t) {
  if (t <= 1) return 1;
  return t * Factorial(t - 1);
}

std::string SeqPair::getLexIndex(design& des) const {
  return "pos_pair=" + std::to_string(des.getSeqIndex(posPair)) + " neg_pair=" + std::to_string(des.getSeqIndex(negPair)) +
         " selected=" + std::to_string(des.getSelIndex(selected));
}

bool SeqPair::CheckSymm(design& caseNL) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.CheckSymm");
  std::map<int, int> posPosition, negPosition;
  for (int i = 0; i < ((int)posPair.size()); ++i) {
    posPosition[posPair[i]] = i;
    negPosition[negPair[i]] = i;
  }
  for (const auto& sb : caseNL.SBlocks) {
    // self symm blocks should be (above/below for vertical axis) or (left/right for horizontal axis)
    // self symm blocks to the (left/right for vertical axis) or (above/below) for horizontal) is a violation
    for (int i = 0; i < ((int)sb.selfsym.size()) - 1; ++i) {
      auto posA = posPosition[sb.selfsym[i].first];
      auto negA = negPosition[sb.selfsym[i].first];
      for (int j = i + 1; j < ((int)sb.selfsym.size()); ++j) {
        auto posB = posPosition[sb.selfsym[j].first];
        auto negB = negPosition[sb.selfsym[j].first];
        if (sb.axis_dir == placerDB::V) {
          if ((posA < posB && negA < negB) || (posA > posB && negA > negB)) {
            return false;
          }
        } else {
          if ((posA < posB && negA > negB) || (posA > posB && negA < negB)) {
            return false;
          }
        }
      }
    }
    for (int i = 0; i < ((int)sb.sympair.size()); ++i) {
      const auto& sympairi = sb.sympair[i];
      auto posA = posPosition[sympairi.first];
      auto negA = negPosition[sympairi.first];
      auto posB = posPosition[sympairi.second];
      auto negB = negPosition[sympairi.second];
      if (sb.axis_dir == placerDB::V) {
        // symm pairs should be left/right for vertical axis
        if ((posA < posB && negA > negB) || (posA > posB && negA < negB)) {
          return false;
        }
        for (const auto& itselfsym : sb.selfsym) {
          auto posC = posPosition[itselfsym.first];
          auto negC = negPosition[itselfsym.first];
          // symm pairs lying on same side (both left or both right) of self symm block is a violation
          if (posA < posB) {
            if ((posB < posC && negB < negC) || (posC < posA && negC < negA)) return false;
          } else {
            if ((posA < posC && negA < negC) || (posC < posB && negC < negB)) return false;
          }
        }
        for (int j = i + 1; j < ((int)sb.sympair.size()); ++j) {
          const auto& sympairj = sb.sympair[j];
          auto posC = posPosition[sympairj.first];
          auto negC = negPosition[sympairj.first];
          auto posD = posPosition[sympairj.second];
          auto negD = negPosition[sympairj.second];
          //(A,B) and (C,D) are symm pairs sharing axis of symmetry
          // if A is above C, then A cannot be below D
          if (posA < posC && negA > negC && posA > posD && negA < negD) return false;
          // if A is below C, then A cannot be above D
          if (posA > posC && negA < negC && posA < posD && negA > negD) return false;
          // if B is above C, then B cannot be below D
          if (posB < posC && negB > negC && posB > posD && negB < negD) return false;
          // if B is below C, then B cannot be above D
          if (posB > posC && negB < negC && posB < posD && negB > negD) return false;

          // if A is above C, then B cannot be below D
          if (posA < posC && negA > negC && posB > posD && negB < negD) return false;
          // if A is below C, then B cannot be above D
          if (posA > posC && negA < negC && posB < posD && negB > negD) return false;
          // if A is above D, then B cannot be below C
          if (posA < posD && negA > negD && posB > posC && negB < negC) return false;
          // if A is below D, then B cannot be above C
          if (posA > posD && negA < negD && posB < posC && negB > negC) return false;

          // if A is to the left of C, then B cannot be to the left of D
          if (posA < posC && negA < negC && posB < posD && negB < negD) return false;
          // if A is to the right of C, then B cannot be to the right of D
          if (posA > posC && negA > negC && posB > posD && negB > negD) return false;
          // if A is to the left of D, then B cannot be to the left of C
          if (posA < posD && negA < negD && posB < posC && negB < negC) return false;
          // if A is to the right of D, then B cannot be to the right of C
          if (posA > posD && negA > negD && posB > posC && negB > negC) return false;
        }
      } else {
        if ((posA < posB && negA < negB) || (posA > posB && negA > negB)) {
          return false;
        }
        for (const auto& itselfsym : sb.selfsym) {
          auto posC = posPosition[itselfsym.first];
          auto negC = negPosition[itselfsym.first];
          if ((posA < posB && posC > posB && negC < negB) || (posA > posB && posC > posA && negC < negA)) {
            return false;
          }
        }
        for (int j = i + 1; j < ((int)sb.sympair.size()); ++j) {
          const auto& sympairj = sb.sympair[j];
          auto posC = posPosition[sympairj.first];
          auto negC = negPosition[sympairj.first];
          auto posD = posPosition[sympairj.second];
          auto negD = negPosition[sympairj.second];
          if (posA < posC && negA < negC && posA > posD && negA > negD) return false;
          if (posA > posC && negA > negC && posA < posD && negA < negD) return false;
          if (posB < posC && negB < negC && posB > posD && negB > negD) return false;
          if (posB > posC && negB > negC && posB < posD && negB < negD) return false;

          if (posA < posC && negA < negC && posB > posD && negB > negD) return false;
          if (posA > posC && negA > negC && posB < posD && negB < negD) return false;
          if (posA < posD && negA < negD && posB > posC && negB > negC) return false;
          if (posA > posD && negA > negD && posB < posC && negB < negC) return false;

          if (posA > posC && negA < negC && posB < posD && negB > negD) return false;
          if (posA < posC && negA > negC && posB > posD && negB < negD) return false;
          if (posA > posD && negA < negD && posB < posC && negB > negC) return false;
          if (posA < posD && negA > negD && posB > posC && negB < negC) return false;
        }
      }
    }
  }

  // collect all horizontal align blocks that align to the bottom
  std::map<int, std::vector<int>> alignBlocksHor, alignBlocksVer;
  for (const auto& sb : caseNL.SBlocks) {
    if (sb.axis_dir == placerDB::V) {
      for (const auto& it : sb.sympair) {
        std::vector<int> tmpvec{it.first, it.second};
        auto itAlign = alignBlocksHor.find(it.first);
        if (itAlign == alignBlocksHor.end()) {
          alignBlocksHor.emplace(it.first, tmpvec);
        } else {
          itAlign->second.insert(itAlign->second.end(), tmpvec.begin(), tmpvec.end());
        }
        itAlign = alignBlocksHor.find(it.second);
        if (itAlign == alignBlocksHor.end()) {
          alignBlocksHor.emplace(it.second, tmpvec);
        } else {
          itAlign->second.insert(itAlign->second.end(), tmpvec.begin(), tmpvec.end());
        }
      }
    } else {
      for (const auto& it : sb.sympair) {
        std::vector<int> tmpvec{it.first, it.second};
        auto itAlign = alignBlocksVer.find(it.first);
        if (itAlign == alignBlocksVer.end()) {
          alignBlocksVer.emplace(it.first, tmpvec);
        } else {
          itAlign->second.insert(itAlign->second.end(), tmpvec.begin(), tmpvec.end());
        }
        itAlign = alignBlocksVer.find(it.second);
        if (itAlign == alignBlocksVer.end()) {
          alignBlocksVer.emplace(it.second, tmpvec);
        } else {
          itAlign->second.insert(itAlign->second.end(), tmpvec.begin(), tmpvec.end());
        }
      }
    }
  }
  for (const auto& au : caseNL.Align_blocks) {
    if (au.line == 0) {
      if (au.horizon == 1) {
        for (const auto& it : au.blocks) {
          auto itAlign = alignBlocksHor.find(it);
          if (itAlign == alignBlocksHor.end()) {
            alignBlocksHor.emplace(it, au.blocks);
          } else {
            itAlign->second.insert(itAlign->second.end(), au.blocks.begin(), au.blocks.end());
          }
        }
      } else {
        for (const auto& it : au.blocks) {
          auto itAlign = alignBlocksVer.find(it);
          if (itAlign == alignBlocksVer.end()) {
            alignBlocksVer.emplace(it, au.blocks);
          } else {
            itAlign->second.insert(itAlign->second.end(), au.blocks.begin(), au.blocks.end());
          }
        }
      }
    }
  }
  std::map<int, std::set<int>> aboveSet, belowSet, rightSet, leftSet;
  // collect set of above blocks/ below blocks for all blocks
  for (auto& it : posPair) {
    if (it >= caseNL.Blocks.size()) continue;
    auto posA = posPosition[it];
    auto negA = negPosition[it];
    for (int i = 0; i < posA; ++i) {
      const auto& bi = posPair[i];
      if (bi < caseNL.Blocks.size()) {
        auto negB = negPosition[bi];
        if (negB > negA) {
          aboveSet[it].insert(posPair[i]);
          // if any block above is part of a horizontal align constraint,
          // then the whole collection in the align constraint needs to be above
          auto itAlign = alignBlocksHor.find(bi);
          if (itAlign != alignBlocksHor.end()) {
            aboveSet[it].insert(itAlign->second.begin(), itAlign->second.end());
          }
        } else {
          rightSet[it].insert(posPair[i]);
          auto itAlign = alignBlocksVer.find(bi);
          if (itAlign != alignBlocksVer.end()) {
            rightSet[it].insert(itAlign->second.begin(), itAlign->second.end());
          }
        }
      }
    }
    for (int i = posA + 1; i < ((int)posPair.size()); ++i) {
      const auto& bi = posPair[i];
      if (bi < caseNL.Blocks.size()) {
        if (negPosition[bi] < negA) {
          belowSet[it].insert(posPair[i]);
          const auto& cpt = caseNL.Blocks[bi][0].counterpart;
          // if any block below is part of a horizontal align constraint,
          // then the whole collection in the align constraint needs to be below
          auto itAlign = alignBlocksHor.find(bi);
          if (itAlign != alignBlocksHor.end()) {
            belowSet[it].insert(itAlign->second.begin(), itAlign->second.end());
          }
        } else {
          leftSet[it].insert(posPair[i]);
          auto itAlign = alignBlocksVer.find(bi);
          if (itAlign != alignBlocksVer.end()) {
            leftSet[it].insert(itAlign->second.begin(), itAlign->second.end());
          }
        }
      }
    }
  }

  for (auto& horiz : {true, false}) {
    const auto& alignBlocks = horiz ? alignBlocksHor : alignBlocksVer;
    auto& arSet = horiz ? aboveSet : rightSet;
    auto& blSet = horiz ? belowSet : leftSet;
    if (!alignBlocks.empty()) {
      // expand set to include transitive relation above of above/below of below/right of right/left of left
      std::vector<int> intersec(posPair.size());
      for (auto& itpos : posPair) {
        if (itpos >= caseNL.Blocks.size()) continue;
        std::set<int> tmpset;
        for (auto& itar : arSet[itpos]) {
          tmpset.insert(arSet[itar].begin(), arSet[itar].end());
        }
        arSet[itpos].insert(tmpset.begin(), tmpset.end());
        tmpset.clear();
        for (auto& itbl : blSet[itpos]) {
          tmpset.insert(blSet[itbl].begin(), blSet[itbl].end());
        }
        blSet[itpos].insert(tmpset.begin(), tmpset.end());
        auto itinter = std::set_intersection(arSet[itpos].begin(), arSet[itpos].end(), blSet[itpos].begin(), blSet[itpos].end(), intersec.begin());
        if ((itinter - intersec.begin()) > 0) {
          return false;
        }
      }

      // check if above/below or left/right set overlap for all align blocks
      for (const auto& au : caseNL.Align_blocks) {
        if (au.line == 0) {
          if ((horiz && au.horizon == 1) || (!horiz && au.horizon == 0)) {
            for (int i = 0; i < ((int)au.blocks.size()) - 1; ++i) {
              const int& ai = au.blocks[i];
              const auto& arai = arSet[ai];
              const auto& blai = blSet[ai];
              for (int j = i + 1; j < ((int)au.blocks.size()); ++j) {
                const int& bj = au.blocks[j];
                const auto& arbj = arSet[bj];
                const auto& blbj = blSet[bj];
                auto itinter = std::set_intersection(arai.begin(), arai.end(), blbj.begin(), blbj.end(), intersec.begin());
                if ((itinter - intersec.begin()) > 0) {
                  return false;
                }
                itinter = std::set_intersection(blai.begin(), blai.end(), arbj.begin(), arbj.end(), intersec.begin());
                if ((itinter - intersec.begin()) > 0) {
                  return false;
                }
              }
            }
          }
        }
        // check if above/below or left/right overlap for all symmetry pairs
        for (const auto& sb : caseNL.SBlocks) {
          for (const auto& it : sb.sympair) {
            if ((horiz && sb.axis_dir == placerDB::V) || (!horiz && sb.axis_dir == placerDB::H)) {
              const auto& arai = arSet[it.first];
              const auto& blbj = blSet[it.second];
              auto itinter = std::set_intersection(arai.begin(), arai.end(), blbj.begin(), blbj.end(), intersec.begin());
              if ((itinter - intersec.begin()) > 0) {
                return false;
              }
              const auto& blai = blSet[it.first];
              const auto& arbj = arSet[it.second];
              itinter = std::set_intersection(blai.begin(), blai.end(), arbj.begin(), arbj.end(), intersec.begin());
              if ((itinter - intersec.begin()) > 0) {
                return false;
              }
            }
          }
        }
      }
    }
  }
  return true;
}

bool SeqPair::CheckAlign(design& caseNL) {
  for (const auto& align : caseNL.Align_blocks) {
    for (int i = 0; i < ((int)align.blocks.size()) - 1; ++i) {
      for (int j = i + 1; j < ((int)align.blocks.size()); ++j) {
        int first_it_pos, second_it_pos, first_it_neg, second_it_neg;
        first_it_pos = find(posPair.begin(), posPair.end(), align.blocks[i]) - posPair.begin();
        second_it_pos = find(posPair.begin(), posPair.end(), align.blocks[j]) - posPair.begin();
        first_it_neg = find(negPair.begin(), negPair.end(), align.blocks[i]) - negPair.begin();
        second_it_neg = find(negPair.begin(), negPair.end(), align.blocks[j]) - negPair.begin();
        if (first_it_pos > second_it_pos) {
          swap(first_it_pos, second_it_pos);
          swap(first_it_neg, second_it_neg);
        }
        if (align.horizon) {
          if ((first_it_pos - second_it_pos) * (first_it_neg - second_it_neg) < 0) return false;
        } else if (!align.horizon) {
          if ((first_it_pos - second_it_pos) * (first_it_neg - second_it_neg) > 0) return false;
        }
        set<int> s1(posPair.begin(), posPair.begin() + first_it_pos);
        set<int> s2(posPair.begin() + first_it_pos + 1, posPair.begin() + second_it_pos);
        set<int> s3(posPair.begin() + second_it_pos + 1, posPair.end());
        set<int> u_23, u_12;
        std::set_union(s2.begin(), s2.end(), s3.begin(), s3.end(), std::inserter(u_23, u_23.begin()));
        std::set_union(s1.begin(), s1.end(), s2.begin(), s2.end(), std::inserter(u_12, u_12.begin()));
        if (align.horizon) {
          set<int> s4(negPair.begin(), negPair.begin() + first_it_neg);
          set<int> s5(negPair.begin() + first_it_neg + 1, negPair.begin() + second_it_neg);
          set<int> s6(negPair.begin() + second_it_neg + 1, negPair.end());
          std::vector<int> i_u23_4, i_u12_6;
          std::set_intersection(u_23.begin(), u_23.end(), s4.begin(), s4.end(), std::back_inserter(i_u23_4));
          std::set_intersection(u_12.begin(), u_12.end(), s6.begin(), s6.end(), std::back_inserter(i_u12_6));
          for (const auto& a : i_u23_4) {
            for (const auto& b : i_u12_6) {
              for (const auto& SPBlock : caseNL.SPBlocks) {
                if (SPBlock.axis_dir == placerDB::V) {
                  for (const auto& sympair : SPBlock.sympair) {
                    if (a == sympair.first && b == sympair.second || a == sympair.second && b == sympair.first) return false;
                    // check sympair
                  }
                }
              }
              for (const auto& otheralign : caseNL.Align_blocks) {
                for (int i = 0; i < ((int)otheralign.blocks.size()) - 1; ++i) {
                  for (int j = i + 1; j < ((int)otheralign.blocks.size()); ++j) {
                    if (otheralign.horizon) {
                      if (a == otheralign.blocks[i] && b == otheralign.blocks[j] || a == otheralign.blocks[j] && b == otheralign.blocks[i]) return false;
                      // check other align pairs
                    }
                  }
                }
              }
            }
          }
        } else if (!align.horizon) {
          set<int> s4(negPair.begin(), negPair.begin() + second_it_neg);
          set<int> s5(negPair.begin() + second_it_neg + 1, negPair.begin() + first_it_neg);
          set<int> s6(negPair.begin() + first_it_neg + 1, negPair.end());
          vector<int> i_u23_6, i_u12_4;
          std::set_intersection(u_23.begin(), u_23.end(), s6.begin(), s6.end(), std::back_inserter(i_u23_6));
          std::set_intersection(u_12.begin(), u_12.end(), s4.begin(), s4.end(), std::back_inserter(i_u12_4));
          for (const auto& a : i_u23_6) {
            for (const auto& b : i_u12_4) {
              for (const auto& SPBlock : caseNL.SPBlocks) {
                if (SPBlock.axis_dir == placerDB::H) {
                  for (const auto& sympair : SPBlock.sympair) {
                    if (a == sympair.first && b == sympair.second || a == sympair.second && b == sympair.first) return false;
                    // check sympair
                  }
                }
              }
              for (const auto& otheralign : caseNL.Align_blocks) {
                for (int i = 0; i < ((int)otheralign.blocks.size()) - 1; ++i) {
                  for (int j = i + 1; j < ((int)otheralign.blocks.size()); ++j) {
                    if (!otheralign.horizon) {
                      if (a == otheralign.blocks[i] && b == otheralign.blocks[j] || a == otheralign.blocks[j] && b == otheralign.blocks[i]) return false;
                      // check other align pairs
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  return true;
}

bool SeqPair::PerturbationNew(design& caseNL) {
  /* initialize random seed: */
  // srand(time(NULL));
  //
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.PerturbationNew");

  const SeqPair cpsp(*this);
  const int max_trial_cnt{20};
  bool retval{true};
  int trial_cnt{0};
  do {
    if (_seqPairEnum) {
      posPair = _seqPairEnum->PosPair();
      negPair = _seqPairEnum->NegPair();
      selected = _seqPairEnum->Selected();
      _seqPairEnum->Permute();
    } else {
      bool mark = false;
      std::set<int> pool;
      // 0:ChangeSelectedBlock
      // 1:MoveAsymmetricBlockposPair
      // 2:MoveAsymmetricBlocknegPair
      // 3:MoveAsymmetricBlockdoublePair
      // 4:SwapTwoBlocksofSameGroup
      // 5:SwapTwoSymmetryGroup
      // 6:SwapMultiBlocksofSameGroup
      if (caseNL.GetSizeofBlocks() <= 1) {
        return true;
      }
      if (caseNL.noBlock4Move > 0) {
        pool.insert(0);
      }
      if (caseNL.noAsymBlock4Move > 0) {
        pool.insert(1);
        pool.insert(2);
        pool.insert(3);
      }
      if (caseNL.noSymGroup4PartMove > 0) {
        pool.insert(4);
        pool.insert(6);
      }
      if (caseNL.noSymGroup4FullMove > 1) {
        pool.insert(5);
      }
      int fail = 0;
      while (!mark && fail < max_trial_cnt) {
        // std::cout<<int(pool.size())<<std::endl;
        int choice = caseNL.rand() % int(pool.size());
        std::set<int>::iterator cit = pool.begin();
        std::advance(cit, choice);
        switch (*cit) {
          case 0:
            mark = ChangeSelectedBlock(caseNL);
            break;
          case 1:
            mark = MoveAsymmetricBlockposPair(caseNL);
            break;
          case 2:
            mark = MoveAsymmetricBlocknegPair(caseNL);
            break;
          case 3:
            mark = MoveAsymmetricBlockdoublePair(caseNL);
            break;
          case 4:
            mark = SwapTwoBlocksofSameGroup(caseNL);
            break;
          case 5:
            mark = SwapTwoSymmetryGroup(caseNL);
            break;
          case 6:
            mark = SwapMultiBlocksofSameGroup(caseNL);
            break;
          default:
            mark = false;
        }
        fail++;
      }
    }
    bool ok = KeepOrdering(caseNL);
    // logger->info("KeepOrdering end: {0}", ok);

    SameSelected(caseNL);
    retval = ((cpsp == *this) || !CheckAlign(caseNL) || !CheckSymm(caseNL) || !ok);
    if (logger->should_log(spdlog::level::debug)) {
      std::string tmpstr, tmpstrn, tmpstrs;
      for (const auto& it : posPair) tmpstr += (std::to_string(it) + " ");
      for (const auto& it : negPair) tmpstrn += (std::to_string(it) + " ");
      for (const auto& it : selected) tmpstrs += (std::to_string(it) + " ");
      logger->debug("block : {0} sa_print_seq_pair [Positive pair: {1} Negative pair : {2} Selected : {3}]", caseNL.name, tmpstr, tmpstrn, tmpstrs);
    }
  } while (retval && ++trial_cnt < max_trial_cnt);
  return !retval;
}

void SeqPair::TestSwap() {
  // For testing
  vector<int> Alist, Blist;
  Blist.push_back(2);
  Blist.push_back(4);
  Blist.push_back(6);
  Alist.push_back(3);
  Alist.push_back(5);
  this->posPair = SwapTwoListinSeq(Alist, Blist, this->posPair);
  // this->negPair=SwapTwoListinSeq(Alist, Blist, this->negPair);
}

bool SeqPair::SwapTwoSymmetryGroup(design& caseNL) {
  /* initialize random seed: */
  // srand(time(NULL));
  int sgA, sgB;
  if (caseNL.GetSizeofSBlocks() <= 1) {
    return false;
  } else {
    sgA = caseNL.rand() % caseNL.GetSizeofSBlocks();
    sgB = caseNL.rand() % caseNL.GetSizeofSBlocks();
    while (sgB == sgA) {
      sgB = caseNL.rand() % caseNL.GetSizeofSBlocks();
    }
  }
  if (caseNL.mixFlag) {
    if (caseNL.GetMappedSymmBlockIdx(sgA) != -1 || caseNL.GetMappedSymmBlockIdx(sgB) != -1) {
      return false;
    }
  }
  // cout<<"Swap symmetry group "<<sgA<<" and "<<sgB<<endl;
  vector<int> Alist = caseNL.GetRealBlockPlusAxisListfromSymmGroup(sgA);
  vector<int> Blist = caseNL.GetRealBlockPlusAxisListfromSymmGroup(sgB);

  this->posPair = SwapTwoListinSeq(Alist, Blist, this->posPair);
  this->negPair = SwapTwoListinSeq(Alist, Blist, this->negPair);
  return true;
}

vector<int> SeqPair::GetVerticesIndexinSeq(vector<int>& seq, vector<int>& L) {
  vector<int> idx;
  for (int i = 0; i < (int)seq.size(); ++i) {
    for (vector<int>::iterator it = L.begin(); it != L.end(); ++it) {
      if (seq.at(i) == *it) {
        idx.push_back(i);
        break;
      }
    }
  }
  return idx;
}

vector<int> SeqPair::SwapTwoListinSeq(vector<int>& Alist, vector<int>& Blist, vector<int>& seq) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.SwapTwoListinSeq");

  vector<int> newseq = seq;
  vector<int> Apos = GetVerticesIndexinSeq(seq, Alist);
  vector<int> Bpos = GetVerticesIndexinSeq(seq, Blist);
  /*
  cout<<"Apos: ";
  for(vector<int>::iterator it=Apos.begin();it!=Apos.end();it++) {cout<<" "<<*it;}
  cout<<endl;
  cout<<"Bpos: ";
  for(vector<int>::iterator it=Bpos.begin();it!=Bpos.end();it++) {cout<<" "<<*it;}
  cout<<endl;
  */
  if (Apos.size() == Bpos.size()) {
    for (int i = 0; i < (int)Apos.size(); ++i) {
      int temp_value = newseq.at(Apos.at(i));
      newseq.at(Apos.at(i)) = newseq.at(Bpos.at(i));  // B --> A
      newseq.at(Bpos.at(i)) = temp_value;             // A --> B
    }
  } else if (Apos.size() < Bpos.size()) {
    for (int i = 0; i < (int)Apos.size(); ++i) newseq.at(Bpos.at(i)) = seq.at(Apos.at(i));  // A --> B
    // Merge sort to create new Apos list
    vector<int> newApos;
    vector<int>::iterator ait = Apos.begin();
    vector<int>::iterator bit = Bpos.begin() + Apos.size();
    while (ait != Apos.end() && bit != Bpos.end()) {
      if ((*ait) < (*bit)) {
        newApos.push_back(*ait);
        ++ait;
      } else if ((*ait) > (*bit)) {
        newApos.push_back(*bit);
        ++bit;
      } else {
        newApos.push_back(*bit);
        newApos.push_back(*bit);
        ++bit;
        ++ait;
        logger->debug("Placer-Error: same index for different lists!");
      }
    }
    while (ait != Apos.end()) {
      newApos.push_back(*ait);
      ++ait;
    }
    while (bit != Bpos.end()) {
      newApos.push_back(*bit);
      ++bit;
    }
    /*
    cout<<"newApos: ";
    for(vector<int>::iterator it=newApos.begin();it!=newApos.end();it++) {cout<<" "<<*it;}
    cout<<endl;
    */

    for (int i = 0; i < (int)Bpos.size(); ++i) newseq.at(newApos.at(i)) = seq.at(Bpos.at(i));  // B--> A
  } else {
    for (int i = 0; i < (int)Bpos.size(); ++i) newseq.at(Apos.at(i)) = seq.at(Bpos.at(i));  // B --> A
    // Merge sort to create new Bpos list
    vector<int> newBpos;
    vector<int>::iterator ait = Apos.begin() + Bpos.size();
    vector<int>::iterator bit = Bpos.begin();
    while (ait != Apos.end() && bit != Bpos.end()) {
      if ((*ait) < (*bit)) {
        newBpos.push_back(*ait);
        ++ait;
      } else if ((*ait) > (*bit)) {
        newBpos.push_back(*bit);
        ++bit;
      } else {
        newBpos.push_back(*ait);
        newBpos.push_back(*ait);
        ++ait;
        ++bit;
        logger->debug("Placer-Error: same index for different lists!");
      }
    }
    while (ait != Apos.end()) {
      newBpos.push_back(*ait);
      ++ait;
    }
    while (bit != Bpos.end()) {
      newBpos.push_back(*bit);
      ++bit;
    }

    /*
    cout<<"newBpos: ";
    for(vector<int>::iterator it=newBpos.begin();it!=newBpos.end();it++) {cout<<" "<<*it;}
    cout<<endl;
    */

    for (int i = 0; i < (int)Apos.size(); ++i) newseq.at(newBpos.at(i)) = seq.at(Apos.at(i));  // A--> B
  }
  return newseq;
}

bool SeqPair::SwapTwoBlocksofSameGroup(design& caseNL) {
  /* initialize random seed: */
  // srand(time(NULL));
  int sgid;
  if (caseNL.GetSizeofSBlocks() > 1) {
    sgid = caseNL.rand() % caseNL.GetSizeofSBlocks();
  } else if (caseNL.GetSizeofSBlocks() == 1) {
    sgid = 0;
  } else {
    return false;
  }
  // cout<<"sgid "<<sgid<<endl;
  vector<int> blist = caseNL.GetRealBlockListfromSymmGroup(sgid);  // all real blocks in symmetry group cosidering mixFlag
  // cout<<"blist size: "<<blist.size()<<endl;
  if (blist.empty() || (int)blist.size() == 1) {
    return false;
  }  // std::cout<<"empty or 1"<<std::endl;}
  if ((int)blist.size() == 2 && blist.at(0) == caseNL.GetBlockCounterpart(blist.at(1))) {
    return false;
  }
  int A = blist.at(caseNL.rand() % (int)blist.size());
  // while(A>=(int)caseNL.GetSizeofBlocks()) {
  //   A=blist.at( rand() % (int)blist.size() );
  //}
  int symA = caseNL.GetBlockCounterpart(A);
  int B = blist.at(caseNL.rand() % (int)blist.size());
  while (B == A || B == symA) {
    B = blist.at(caseNL.rand() % (int)blist.size());
  }
  // while(B==A || B==symA || B>=(int)caseNL.GetSizeofBlocks() )  {
  //  B=blist.at( rand() % (int)blist.size() );
  //}
  int symB = caseNL.GetBlockCounterpart(B);
  int Apos = GetVertexIndexinSeq(posPair, A);
  int Bpos = GetVertexIndexinSeq(posPair, B);
  int symApos = GetVertexIndexinSeq(negPair, symA);
  int symBpos = GetVertexIndexinSeq(negPair, symB);
  // cout<<endl<<"Swap "<<A<<" and "<<B<<" in pos SP"<<endl;
  // cout<<"Swap "<<symA<<" and "<<symB<<" in neg SP"<<endl;
  posPair.at(Bpos) = A;
  posPair.at(Apos) = B;
  negPair.at(symBpos) = symA;
  negPair.at(symApos) = symB;
  return true;
}

bool SeqPair::SwapMultiBlocksofSameGroup(design& caseNL) {
  /* initialize random seed: */
  // srand(time(NULL));
  int count = 3;
  int sgid;
  if (caseNL.GetSizeofSBlocks() > 1) {
    sgid = caseNL.rand() % caseNL.GetSizeofSBlocks();
  } else if (caseNL.GetSizeofSBlocks() == 1) {
    sgid = 0;
  } else {
    return false;
  }
  // cout<<"sgid "<<sgid<<endl;
  vector<int> blist = caseNL.GetRealBlockListfromSymmGroup(sgid);  // all real blocks in symmetry group considering mixFlag
  // cout<<"blist size: "<<blist.size()<<endl;
  if (blist.empty() || (int)blist.size() == 1) {
    return false;
  }  // std::cout<<"empty or 2"<<std::endl;}
  if ((int)blist.size() == 2 && blist.at(0) == caseNL.GetBlockCounterpart(blist.at(1))) {
    return false;
  }
  for (int i = 0; i < count; ++i) {
    int A = blist.at(caseNL.rand() % (int)blist.size());
    // while(A>=(int)caseNL.GetSizeofBlocks()) {
    //   A=blist.at( rand() % (int)blist.size() );
    //}
    int symA = caseNL.GetBlockCounterpart(A);
    int B = blist.at(caseNL.rand() % (int)blist.size());
    while (B == A || B == symA) {
      B = blist.at(caseNL.rand() % (int)blist.size());
    }
    // while(B==A || B==symA || B>=(int)caseNL.GetSizeofBlocks() )  {
    //  B=blist.at( rand() % (int)blist.size() );
    //}
    int symB = caseNL.GetBlockCounterpart(B);
    int Apos = GetVertexIndexinSeq(posPair, A);
    int Bpos = GetVertexIndexinSeq(posPair, B);
    int symApos = GetVertexIndexinSeq(negPair, symA);
    int symBpos = GetVertexIndexinSeq(negPair, symB);
    // cout<<endl<<"Swap "<<A<<" and "<<B<<" in pos SP"<<endl;
    // cout<<"Swap "<<symA<<" and "<<symB<<" in neg SP"<<endl;
    posPair.at(Bpos) = A;
    posPair.at(Apos) = B;
    negPair.at(symBpos) = symA;
    negPair.at(symApos) = symB;
  }
  return true;
}

bool SeqPair::MoveAsymmetricBlockposPair(design& caseNL) {
  /* initialize random seed: */
  // srand(time(NULL));
  if (!caseNL.checkAsymmetricBlockExist()) {
    return false;
  }
  int anode = caseNL.rand() % caseNL.GetSizeofBlocks();
  while (caseNL.GetBlockSymmGroup(anode) >= 0) {
    anode = caseNL.rand() % caseNL.GetSizeofBlocks();
  }  // randomly choose an asymmetric block
  if (caseNL.mixFlag && caseNL.GetMappedBlockIdx(anode) != -1) {
    return false;
  }
  // cout<<endl<<"Move asymmetric block in pos SP"<<endl;
  return MoveAsymmetricBlockUnit(caseNL, this->posPair, anode);
}

bool SeqPair::MoveAsymmetricBlocknegPair(design& caseNL) {
  /* initialize random seed: */
  // srand(time(NULL));
  if (!caseNL.checkAsymmetricBlockExist()) {
    return false;
  }
  int anode = caseNL.rand() % caseNL.GetSizeofBlocks();
  while (caseNL.GetBlockSymmGroup(anode) >= 0) {
    anode = caseNL.rand() % caseNL.GetSizeofBlocks();
  }  // randomly choose an asymmetric block
  if (caseNL.mixFlag && caseNL.GetMappedBlockIdx(anode) != -1) {
    return false;
  }
  // cout<<endl<<"Move asymmetric block in neg SP"<<endl;
  return MoveAsymmetricBlockUnit(caseNL, this->negPair, anode);
}

bool SeqPair::MoveAsymmetricBlockdoublePair(design& caseNL) {
  /* initialize random seed: */
  // srand(time(NULL));
  if (!caseNL.checkAsymmetricBlockExist()) {
    return false;
  }
  int anode = caseNL.rand() % caseNL.GetSizeofBlocks();
  while (caseNL.GetBlockSymmGroup(anode) >= 0) {
    anode = caseNL.rand() % caseNL.GetSizeofBlocks();
  }  // randomly choose an asymmetric block
  if (caseNL.mixFlag && caseNL.GetMappedBlockIdx(anode) != -1) {
    return false;
  }
  bool mark = true;
  // cout<<endl<<"Move asymmetric block in pos SP"<<endl;
  mark = mark && MoveAsymmetricBlockUnit(caseNL, this->posPair, anode);
  // cout<<"Move asymmetric block in neg SP"<<endl;
  mark = mark && MoveAsymmetricBlockUnit(caseNL, this->negPair, anode);
  return mark;
}

bool SeqPair::MoveAsymmetricBlockUnit(design& caseNL, vector<int>& seq, int anode) {
  /* initialize random seed: */
  // srand(time(NULL));
  vector<int> newseq;
  newseq.resize(seq.size());
  int oldpos = GetVertexIndexinSeq(seq, anode);  // position of anode in original seqence
  int newpos = caseNL.rand() % (int)seq.size();
  while (oldpos == newpos) {
    newpos = caseNL.rand() % (int)seq.size();
  }  // randomly choose a new position
  // cout<<"Aymnode-"<<anode<<" oldpos-"<<oldpos<<" newpos-"<<newpos<<endl;

  if (oldpos < newpos) {
    for (int i = 0; i < oldpos; ++i) newseq.at(i) = seq.at(i);
    for (int i = oldpos + 1; i <= newpos; ++i) newseq.at(i - 1) = seq.at(i);
    for (int i = newpos + 1; i < (int)seq.size(); ++i) newseq.at(i) = seq.at(i);
    newseq.at(newpos) = seq.at(oldpos);
  } else if (oldpos > newpos) {
    for (int i = 0; i < newpos; ++i) newseq.at(i) = seq.at(i);
    newseq.at(newpos) = seq.at(oldpos);
    for (int i = newpos + 1; i <= oldpos; ++i) newseq.at(i) = seq.at(i - 1);
    for (int i = oldpos + 1; i < (int)seq.size(); ++i) newseq.at(i) = seq.at(i);
  }
  seq = newseq;
  return true;
}
