#include "SeqPair.h"
#include "spdlog/spdlog.h"


SeqPairEnumerator::SeqPairEnumerator(const vector<int>& pair, design& casenl)
{
  _enumIndex = std::make_pair(0, 0);
  _exhausted = 0;
  _posPair = pair;
  std::sort(_posPair.begin(), _posPair.end());
  _negPair = _posPair;
  _maxEnum = SeqPair::Factorial(_posPair.size());
  _selected.resize(casenl.GetSizeofBlocks(), 0);
  _maxSelected.reserve(casenl.GetSizeofBlocks());
  _maxSize = 0;
  for (unsigned i = 0; i < casenl.GetSizeofBlocks(); ++i) {
    auto s = static_cast<int>(casenl.Blocks.at(i).size());
    _maxSize = std::max(_maxSize, s);
    _maxSelected.push_back(s);
  }
}

const bool SeqPairEnumerator::IncrementSelected()
{
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

void SeqPairEnumerator::Permute()
{
  if (!IncrementSelected()) {
    if (_enumIndex.second >= _maxEnum - 1) {
      _enumIndex.second = 0;
      ++_enumIndex.first;
      std::sort(_negPair.begin(), _negPair.end());
      std::next_permutation(std::begin(_posPair), std::end(_posPair));
    } else {
      ++_enumIndex.second;
      std::next_permutation(std::begin(_negPair), std::end(_negPair));
    }
  }
  if (_enumIndex.first >= _maxEnum) _exhausted = true;
}

SeqPair::SeqPair() {
  this->posPair.clear();
  this->negPair.clear();
  this->orient.clear();
  this->symAxis.clear();
  this->selected.clear();
}

//SeqPair::SeqPair(int blockSize) {
//// For testing
//  for(int i=0;i<blockSize;i++) {
//    posPair.push_back(i);
//    negPair.push_back(i);
//    orient.push_back(placerDB::N);
//  }
//}

//SeqPair::SeqPair(string pos, string neg) {
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
  this->posPair=sp.posPair;
  this->negPair=sp.negPair;
  this->orient=sp.orient;
  this->symAxis=sp.symAxis;
  this->selected=sp.selected;
  if (!_seqPairEnum) this->_seqPairEnum = sp._seqPairEnum;
}

SeqPair::SeqPair(design& originNL, design& reducedNL, SeqPair& reducedSP) {

  auto logger = spdlog::default_logger()->clone("placer.SeqPair.SeqPair");

  this->posPair=reducedSP.posPair;
  this->negPair=reducedSP.negPair;
  this->orient.resize( originNL.GetSizeofBlocks(),  placerDB::N  );
  this->symAxis.resize(originNL.GetSizeofSBlocks(), placerDB::V  );
  this->selected.resize(originNL.GetSizeofBlocks(), 0);
  if (!_seqPairEnum) this->_seqPairEnum = reducedSP._seqPairEnum;
  // A. For those common symmetry groups in both original and reduced designs
  // 1. first, convert all the axis nodes of reduced design in sequence pairs
  // into axis nodes of original design
  std::set<int> commonSBs;
  //std::cout<<"work on axis nodes\n";
  for(vector<placerDB::SymmBlock>::iterator it=reducedNL.SBlocks.begin(); it!=reducedNL.SBlocks.end(); ++it) {
    //std::cout<<"work on axis "<<it-reducedNL.SBlocks.begin()<<std::endl;
    // for each symmetry group of reduced design,
    // find the corresponding group in original design
    int reducedsbIdx=it-reducedNL.SBlocks.begin();
    int sbIdx=reducedNL.GetMappedSymmBlockIdx(reducedsbIdx);
    if(sbIdx==-1) {logger->debug("Placer-Error: cannot find similar symmetry group in original design");continue;}
    // modify positive sequence
    commonSBs.insert(sbIdx);
    for(vector<int>::iterator ppit=this->posPair.begin(); ppit!=this->posPair.end(); ++ppit) {
      if( (*ppit)==it->dnode ) { *ppit=originNL.SBlocks.at(sbIdx).dnode; break; }
    }
    // modify negative sequence
    for(vector<int>::iterator npit=this->negPair.begin(); npit!=this->negPair.end(); ++npit) {
      if( (*npit)==it->dnode ) { *npit=originNL.SBlocks.at(sbIdx).dnode; break; }
    }
    this->symAxis.at(sbIdx) = reducedSP.symAxis.at(reducedsbIdx);
  }
  // 2. second, convert all other nodes of reduced design in sequence pairs
  // into nodes of original design
  //std::cout<<"work on sp nodes\n";
  for(vector<int>::iterator it=this->posPair.begin(); it!=this->posPair.end(); ++it) {
    //std::cout<<"work on "<<*it<<" @ "<<it-this->posPair.begin()<<std::endl;
    if( *it<reducedNL.GetSizeofBlocks() ) {  
      int newi=reducedNL.GetMappedBlockIdx(*it);
      if(newi!=-1) { this->orient.at(newi)=reducedSP.orient.at(*it); *it=newi; 
      } else {logger->debug("Placer-Error: cannot covert block in positive sequence");}
    }
  }
  for(vector<int>::iterator it=this->negPair.begin(); it!=this->negPair.end(); ++it) {
    //std::cout<<"work on "<<*it<<" @ "<<it-this->negPair.begin()<<std::endl;
    if( *it<reducedNL.GetSizeofBlocks() ) {  
      int newi=reducedNL.GetMappedBlockIdx(*it);
      if(newi!=-1) {*it=newi;
      } else {logger->debug("Placer-Error: cannot covert block in negative sequence");}
    }
  }
  // 3. third, add other nodes in the original design into sequence pairs
  //std::cout<<"work on other sp nodes\n";
  for(int i=0;i<(int)originNL.SBlocks.size(); ++i) {
    if(commonSBs.find(i)==commonSBs.end()) { // not common SB
      // Potential bug: some blocks might belong to one original symmetry group but not in reduced symmetry group (e.g. a single self-symmetry block)
      // in this case its symmetry group cannot be inserted as new one
      // need fix in future [wbxu]
      logger->debug("InsertNewSBlock(originNL, {0})",i);
      InsertNewSBlock(originNL, i);
    } else { // common SB
      logger->debug("InsertCommonSBlock(originNL, reducedNL, {0})",i);
      InsertCommonSBlock(originNL, reducedNL, i);
    } 
  }
  // 4. add other nodes
  //std::cout<<"work on other nodes\n";
  //std::cout<<"size "<<originNL.GetSizeofBlocks()<<std::endl;
  for(int i=0;i<originNL.GetSizeofBlocks();++i) {
    //std::cout<<i<<endl;
    if(originNL.GetBlockSymmGroup(i)==-1 && originNL.GetMappedBlockIdx(i)==-1) {
      posPair.push_back(i);
      negPair.push_back(i);
      orient.at(i)=placerDB::N;
    }
  }
  //std::cout<<"work on selected mark\n";
  // 5. update selected mark
  for(int i=0;i<reducedNL.GetSizeofBlocks();++i) {
    //std::cout<<i<<" map "<<reducedNL.GetMappedBlockIdx(i)<<" sel " <<reducedSP.GetBlockSelected(i)<<std::endl;
    selected.at( reducedNL.GetMappedBlockIdx(i) )=reducedSP.GetBlockSelected(i);
  }
}

void SeqPair::InsertNewSBlock(design& originNL, int originIdx) {
  //std::cout<<"InsertNewSBlock "<<originIdx<<std::endl;
  placerDB::Smark axis;
  vector<placerDB::SymmBlock>::iterator bit=originNL.SBlocks.begin()+originIdx;
    //axis=bit->axis_dir;
    //axis=placerDB::V; // initialize veritcal symmetry
    /*
    if ( !(bit->selfsym).empty() ) {
      switch( (bit->selfsym).at(0).second ) {
        case placerDB::H: axis=placerDB::V;break;
        case placerDB::V: axis=placerDB::H;break;
      }
    }
   */
    axis=bit->axis_dir;
    //cout<<"axis"<<axis<<endl;
    this->symAxis.at(originIdx)=axis;
    // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
    // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
    if(!bit->sympair.empty()) {
      for(vector< pair<int,int> >::iterator pit=bit->sympair.begin(); pit!=bit->sympair.end(); ++pit) {
        if( pit->first<(int)originNL.GetSizeofBlocks() ) {
          posPair.push_back(pit->first); // a1,a2,...,ap --> positive
          orient[pit->first]=placerDB::N;
        }
      }
    }
    posPair.push_back(bit->dnode); // axis --> positive
    if(!bit->selfsym.empty()) {
      for(vector< pair<int,placerDB::Smark> >::iterator sit=bit->selfsym.begin(); sit!=bit->selfsym.end(); ++sit) {
        if ( sit->first<(int)originNL.GetSizeofBlocks() ) {
          posPair.push_back(sit->first); // c1,...cs --> positve
          orient[sit->first]=placerDB::N;
        }
      }
    }
    if(!bit->sympair.empty()) {
      //for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
      for(vector< pair<int,int> >::reverse_iterator pit=bit->sympair.rbegin(); pit!=bit->sympair.rend(); ++pit) {
        if( pit->second<(int)originNL.GetSizeofBlocks() ) {
          posPair.push_back(pit->second); // bp,...,b1 --> positive
          if(axis==placerDB::V) { orient[pit->second]=placerDB::FN; }
          else if (axis==placerDB::H) { orient[pit->second]=placerDB::FS; }
        }
      }
    }
    // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
    // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
    if(axis==placerDB::V) {
      if(!bit->sympair.empty()) {
        for(vector< pair<int,int> >::iterator pit=bit->sympair.begin(); pit!=bit->sympair.end(); ++pit) {
          if( pit->first<(int)originNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->first); // a1,a2,...,ap --> negative
          }
        }
      }
      if(!bit->selfsym.empty()) {
        //for(vector< pair<int,placerDB::Smark> >::iterator sit=bit->selfsym.end()-1; sit>=bit->selfsym.begin(); --sit) {
        for(vector< pair<int,placerDB::Smark> >::reverse_iterator sit=bit->selfsym.rbegin(); sit!=bit->selfsym.rend(); ++sit) {
          if ( sit->first<(int)originNL.GetSizeofBlocks() ) {
            negPair.push_back(sit->first); // cs,...c1 --> negative
          }
        }
      }
      negPair.push_back(bit->dnode); // axis --> negative
      if (!bit->sympair.empty()) {
        //for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
        for(vector< pair<int,int> >::reverse_iterator pit=bit->sympair.rbegin(); pit!=bit->sympair.rend(); ++pit) {
          if( pit->second<(int)originNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->second); // bp,...,b1 --> positive
          }
        }
      }
    } else if (axis==placerDB::H) {
      if(!bit->sympair.empty()) {
        for(vector< pair<int,int> >::iterator pit=bit->sympair.begin(); pit!=bit->sympair.end(); ++pit) {
          if( pit->second<(int)originNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->second); // b1,...,bp --> negative
          }
        }
      }
      negPair.push_back(bit->dnode); // axis --> negative
      if(!bit->selfsym.empty()) {
        for(vector< pair<int,placerDB::Smark> >::iterator sit=bit->selfsym.begin(); sit!=bit->selfsym.end(); ++sit) {
          if ( sit->first<(int)originNL.GetSizeofBlocks() ) {
            negPair.push_back(sit->first); // c1,...cs --> negative
          }
        }
      }
      if(!bit->sympair.empty()) {
        //for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
        for(vector< pair<int,int> >::reverse_iterator pit=bit->sympair.rbegin(); pit!=bit->sympair.rend(); ++pit) {
          if( pit->first<(int)originNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->first); // ap,...,a1 --> negative
          }
        }
      }
    }
}

void SeqPair::InsertCommonSBlock(design& originNL, design& reducedNL, int originIdx) {

  auto logger = spdlog::default_logger()->clone("placer.SeqPair.InsertCommonSBlock");

  std::vector<placerDB::SymmBlock> tempSB=originNL.SplitSymmBlock(reducedNL, originIdx);
  placerDB::SymmBlock comm=tempSB.at(0);
  placerDB::SymmBlock diff=tempSB.at(1);
  std::set<int> existingPairNode;
  logger->debug("InsertCommonSBlock\nComm SB");
  for(vector<pair<int,int> >::iterator it=comm.sympair.begin(); it!=comm.sympair.end(); ++it) {
    existingPairNode.insert(it->first);
    existingPairNode.insert(it->second);
    logger->debug("sympair {0} vs {1}",it->first,it->second);
  }
  for(vector<pair<int,placerDB::Smark> >::iterator it=comm.selfsym.begin(); it!=comm.selfsym.end(); ++it) {
    logger->debug("selfsym {0} @ {1}",it->first,it->second);
  }
  logger->debug("Diff SB");
  for(vector<pair<int,int> >::iterator it=diff.sympair.begin(); it!=diff.sympair.end(); ++it) {
    logger->debug("sympair {0} vs {1}",it->first,it->second);
  }
  for(vector<pair<int,placerDB::Smark> >::iterator it=diff.selfsym.begin(); it!=diff.selfsym.end(); ++it) {
    logger->debug("selfsym {0} @ {1}",it->first,it->second);
  }
  int anode=originNL.SBlocks.at(originIdx).dnode;
  int anode_pos=-1, anode_neg=-1;
  int L_pos=-1, R_pos=this->posPair.size(), L_neg=-1, R_neg=this->negPair.size();
  for(int i=0;i<(int)this->posPair.size();++i) {
    if(this->posPair.at(i)==anode) {anode_pos=i;break;}
  }
  for(int i=0;i<(int)this->negPair.size();++i) {
    if(this->negPair.at(i)==anode) {anode_neg=i;break;}
  }
  if(anode_pos==-1 || anode_neg==-1) {
    logger->debug("Placer-Error: cannot find axis node in seq pair");
  }
  for(int i=0;i<anode_pos;++i) {
    if(existingPairNode.find(this->posPair.at(i))!=existingPairNode.end()) {
      if(i>L_pos) {L_pos=i;}
    }
  }
  for(int i=anode_pos+1;i<(int)this->posPair.size();++i) {
    if(existingPairNode.find(this->posPair.at(i))!=existingPairNode.end()) {
      if(i<R_pos) {R_pos=i;break;}
    }
  }
  for(int i=0;i<anode_neg;++i) {
    if(existingPairNode.find(this->negPair.at(i))!=existingPairNode.end()) {
      if(i>L_neg) {L_neg=i;}
    }
  }
  for(int i=anode_neg+1;i<(int)this->negPair.size();++i) {
    if(existingPairNode.find(this->negPair.at(i))!=existingPairNode.end()) {
      if(i<R_neg) {R_neg=i;break;}
    }
  }
  logger->debug("posPair: axis {0} left {1} right {2}",anode_pos,L_pos,R_pos);
  logger->debug("negPair: axis {0} left {1} right {2}",anode_neg,L_neg,R_neg);
  vector<int> new_posPair, new_negPair;
  // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
  // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
  // Positive sequence
  // 1. push new sympair a nodes
  if(!diff.sympair.empty()) {
    for(vector< pair<int,int> >::iterator it=diff.sympair.begin(); it!=diff.sympair.end(); ++it) {
      new_posPair.push_back(it->first);
    }
  }
  // 2. push original nodes before L_pos
  for(int i=0;i<=L_pos;++i) {new_posPair.push_back(this->posPair.at(i));}
  // 3. push original nodes between L_pos and R_pos
  for(int i=L_pos+1;i<R_pos;++i) {new_posPair.push_back(this->posPair.at(i));}
  // 4. push new selfsym nodes
  if(!diff.selfsym.empty()) {
    for(vector< pair<int, placerDB::Smark> >::iterator it=diff.selfsym.begin(); it!=diff.selfsym.end(); ++it) {
      new_posPair.push_back(it->first);
    }
  }
  // 5. push orignal nodes after R_pos
  for(int i=R_pos;i<(int)this->posPair.size();++i) {new_posPair.push_back(this->posPair.at(i));}
  // 6. push new sympair b nodes
  if(!diff.sympair.empty()) {
    //for(vector< pair<int,int> >::iterator it=diff.sympair.end()-1; it>=diff.sympair.begin(); it--) {
    for(vector< pair<int,int> >::reverse_iterator it=diff.sympair.rbegin(); it!=diff.sympair.rend(); ++it) {
      new_posPair.push_back(it->second);
    }
  }
  // Negative sequence
  // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
  // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
  //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
  if(this->symAxis.at(originIdx)==placerDB::V) {
    // 1. push new sympair a nodes
    if(!diff.sympair.empty()) {
      for(vector< pair<int,int> >::iterator it=diff.sympair.begin(); it!=diff.sympair.end(); ++it) {
        new_negPair.push_back(it->first);
        this->orient.at(it->first)=placerDB::N;
      }
    }
    // 2. push original nodes before L_neg
    for(int i=0;i<=L_neg;++i) {new_negPair.push_back(this->negPair.at(i));}
    // 3. push new selfsym nodes
    if(!diff.selfsym.empty()) {
      //for(vector< pair<int, placerDB::Smark> >::iterator it=diff.selfsym.end()-1; it!=diff.selfsym.begin(); --it) {
      for(vector< pair<int, placerDB::Smark> >::reverse_iterator it=diff.selfsym.rbegin(); it!=diff.selfsym.rend(); ++it) {
        new_negPair.push_back(it->first);
        this->orient.at(it->first)=placerDB::N;
      }
    }
    // 4. push original nodes between L_neg and R_neg
    for(int i=L_neg+1;i<R_neg;++i) {new_negPair.push_back(this->negPair.at(i));}
    // 5. push orignal nodes after R_neg
    for(int i=R_neg;i<(int)this->negPair.size();++i) {new_negPair.push_back(this->negPair.at(i));}
    // 6. push new sympair b nodes
    if(!diff.sympair.empty()) {
      //for(vector< pair<int,int> >::iterator it=diff.sympair.end()-1; it>=diff.sympair.begin(); it--) {
      for(vector< pair<int,int> >::reverse_iterator it=diff.sympair.rbegin(); it!=diff.sympair.rend(); ++it) {
        new_negPair.push_back(it->second);
        this->orient.at(it->second)=placerDB::FN;
      }
    }
  } else if (this->symAxis.at(originIdx)==placerDB::H) {
    // 1. push new sympair b nodes
    if(!diff.sympair.empty()) {
      for(vector< pair<int,int> >::iterator it=diff.sympair.begin(); it!=diff.sympair.end(); ++it) {
        new_negPair.push_back(it->second);
        this->orient.at(it->second)=placerDB::FS;
      }
    }
    // 2. push original nodes before L_neg
    for(int i=0;i<=L_neg;++i) {new_negPair.push_back(this->negPair.at(i));}
    // 3. push original nodes between L_neg and R_neg
    for(int i=L_neg+1;i<R_neg;++i) {new_negPair.push_back(this->negPair.at(i));}
    // 4. push new selfsym nodes
    if(!diff.selfsym.empty()) {
      for(vector< pair<int, placerDB::Smark> >::iterator it=diff.selfsym.begin(); it!=diff.selfsym.end(); ++it) {
        new_negPair.push_back(it->first);
        this->orient.at(it->first)=placerDB::N;
      }
    }
    // 5. push orignal nodes after R_neg
    for(int i=R_neg;i<(int)this->negPair.size();++i) {new_negPair.push_back(this->negPair.at(i));}
    // 6. push new sympair a nodes
    if(!diff.sympair.empty()) {
      //for(vector< pair<int,int> >::iterator it=diff.sympair.end()-1; it>=diff.sympair.begin(); it--) {
      for(vector< pair<int,int> >::reverse_iterator it=diff.sympair.rbegin(); it!=diff.sympair.rend(); ++it) {
        new_negPair.push_back(it->first);
        this->orient.at(it->first)=placerDB::N;
      }
    }
  } else {
    logger->debug("Placer-Error: incorrect axis");
  }
  this->posPair=new_posPair;
  this->negPair=new_negPair;
}

void SeqPair::CompactSeq(){

  vector<int> temp_p;

  for(unsigned int i=0;i<posPair.size();++i){
     for(unsigned int j=i+1;j<posPair.size();++j){
        if(posPair[i]==posPair[j]){
           posPair[j] = -1;
        }
     }
  }

  for(unsigned int i=0;i<posPair.size();++i){
     if(posPair[i]!=-1){
        temp_p.push_back(posPair[i]);
     }
  }

  vector<int> temp_n;

  for(unsigned int i=0;i<negPair.size();++i){
     for(unsigned int j=i+1;j<negPair.size();++j){
        if(negPair[i]==negPair[j]){
           negPair[j] = -1;
        }
     }
  }

  for(unsigned int i=0;i<negPair.size();++i){
     if(negPair[i]!=-1){
        temp_n.push_back(negPair[i]);
     }
  }

  posPair = temp_p;
  negPair = temp_n;

}

SeqPair::SeqPair(design& caseNL, const size_t maxIter) {
  // Know limitation: currently we force all symmetry group in veritcal symmetry
  placerDB::Smark axis;
  orient.resize(caseNL.GetSizeofBlocks());
  selected.resize(caseNL.GetSizeofBlocks(),0);

  int sym_group_index = 0;
  for(vector<placerDB::SymmBlock>::iterator bit=caseNL.SBlocks.begin(); bit!=caseNL.SBlocks.end(); ++bit) {
    axis = bit->axis_dir;
    sym_group_index++;
    //cout<<"axis"<<axis<<endl;
    symAxis.push_back(axis);
    // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
    // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
    if(!bit->sympair.empty()) {
      for(vector< pair<int,int> >::iterator pit=bit->sympair.begin(); pit!=bit->sympair.end(); ++pit) {
        if( pit->first<(int)caseNL.GetSizeofBlocks() ) {
          //std::<<pit->first<<","<<pit->secode<<" ";
          posPair.push_back(pit->first); // a1,a2,...,ap --> positive
          orient[pit->first]=placerDB::N;
        }
      }
    }
    posPair.push_back(bit->dnode); // axis --> positive
    if(!bit->selfsym.empty()) {
      for(vector< pair<int,placerDB::Smark> >::iterator sit=bit->selfsym.begin(); sit!=bit->selfsym.end(); ++sit) {
        if ( sit->first<(int)caseNL.GetSizeofBlocks() ) {
          posPair.push_back(sit->first); // c1,...cs --> positve
          orient[sit->first]=placerDB::N;
        }
      }
    }
    if(!bit->sympair.empty()) {
      for(vector< pair<int,int> >::reverse_iterator pit=bit->sympair.rbegin(); pit!=bit->sympair.rend(); ++pit) {
        if( pit->second<(int)caseNL.GetSizeofBlocks() ) {
          posPair.push_back(pit->second); // bp,...,b1 --> positive
          if(axis==placerDB::V) { orient[pit->second]=placerDB::FN; }
          else if (axis==placerDB::H) { orient[pit->second]=placerDB::FS; }
        }
      }
    }
    // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
    // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
    if(axis==placerDB::V) {
      if(!bit->sympair.empty()) {
        for(vector< pair<int,int> >::iterator pit=bit->sympair.begin(); pit!=bit->sympair.end(); ++pit) {
          if( pit->first<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->first); // a1,a2,...,ap --> negative
          }
        }

      }
      if(!bit->selfsym.empty()) {

        for(vector< pair<int,placerDB::Smark> >::reverse_iterator sit=bit->selfsym.rbegin(); sit!=bit->selfsym.rend(); ++sit) {

          if ( sit->first<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(sit->first); // cs,...c1 --> negative
          }
        }

      }
      negPair.push_back(bit->dnode); // axis --> negative
      if (!bit->sympair.empty()) {
        for(vector< pair<int,int> >::reverse_iterator pit=bit->sympair.rbegin(); pit!=bit->sympair.rend(); ++pit) {
          if( pit->second<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->second); // bp,...,b1 --> positive
          }
        }
      }
    } else if (axis==placerDB::H) {
      if(!bit->sympair.empty()) {

        for(vector< pair<int,int> >::iterator pit=bit->sympair.begin(); pit!=bit->sympair.end(); ++pit) {

          if( pit->second<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->second); // b1,...,bp --> negative
          }
        }

      }
      negPair.push_back(bit->dnode); // axis --> negative
      if(!bit->selfsym.empty()) {

        for(vector< pair<int,placerDB::Smark> >::iterator sit=bit->selfsym.begin(); sit!=bit->selfsym.end(); ++sit) {

          if ( sit->first<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(sit->first); // c1,...cs --> negative
          }
        }

      }
      if(!bit->sympair.empty()) {
        for(vector< pair<int,int> >::reverse_iterator pit=bit->sympair.rbegin(); pit!=bit->sympair.rend(); ++pit) {
          if( pit->first<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->first); // ap,...,a1 --> negative
          }
        }
      }
    }
  }


  CompactSeq();

  for(int i=0;i<caseNL.GetSizeofBlocks();++i) {
    if(caseNL.GetBlockSymmGroup(i)==-1) {
      posPair.push_back(i);
      negPair.push_back(i);
      orient.at(i)=placerDB::N;
    }
  }

  KeepOrdering(caseNL);

  bool enumerate(false);
  if (maxIter > 0 && posPair.size() <= 6) {
    size_t totEnum = SeqPair::Factorial(posPair.size());
    totEnum *= totEnum;
    if (maxIter > totEnum) {
      for (unsigned i = 0; i < caseNL.GetSizeofBlocks(); ++i) {
        totEnum *= caseNL.Blocks.at(i).size();
        if (2 * maxIter > totEnum) break;
      }
      enumerate = 2 * maxIter > totEnum;
    }
  }

  if (enumerate) {
    _seqPairEnum = std::make_shared<SeqPairEnumerator>(posPair, caseNL);
    auto logger = spdlog::default_logger()->clone("placer.SeqPair.SetEnumerate");
    logger->info("Enumerated search");
  } else {
    _seqPairEnum.reset();
  }

}

SeqPair& SeqPair::operator=(const SeqPair& sp) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.=");
  this->posPair=sp.posPair;
  this->negPair=sp.negPair;
  this->orient=sp.orient;
  this->symAxis=sp.symAxis;
  this->selected=sp.selected;
  if (!_seqPairEnum) this->_seqPairEnum = sp._seqPairEnum;
  return *this;
}

void SeqPair::PrintSeqPair() {

  auto logger = spdlog::default_logger()->clone("placer.SeqPair.PrintSeqPair");

  logger->debug("=== Sequence Pair ===");
  logger->debug("Positive pair: ");
  for(int i=0;i<(int)posPair.size();++i) {
    logger->debug("{0} ",posPair.at(i));
  }
  logger->debug("Negative pair: ");
  for(int i=0;i<(int)negPair.size();++i) {
    logger->debug("{0}",negPair.at(i));
  }
  logger->debug("Orientation: ");
  for(int i=0;i<(int)orient.size();++i) {
    logger->debug("{0}",orient.at(i));
  }
  logger->debug("Symmetry axis: ");
  for(int i=0;i<(int)symAxis.size();++i) {
    if(symAxis.at(i)==0) {logger->debug("H ");
    } else {logger->debug("V ");}
  }
  logger->debug("Selected: ");
  for(int i=0;i<(int)selected.size();++i) {
    logger->debug("{0}",selected.at(i));
  }
  //cout<<endl;
}

int SeqPair::GetBlockSelected(int blockNo) {
  if(blockNo>=0 && blockNo<(int)selected.size()) {
    return(selected.at(blockNo));
  }
  return -1;
}

vector<int> SeqPair::GetBlockIndex(int blockNo) {
  vector<int> blockIdx;
  for(int i=0;i<(int)posPair.size();++i) {
    if(posPair.at(i)==blockNo) {blockIdx.push_back(i);break;}
  }
  for(int i=0;i<(int)negPair.size();++i) {
    if(negPair.at(i)==blockNo) {blockIdx.push_back(i);break;}
  }
  return(blockIdx);
}

vector<int> SeqPair::GetRightBlock(int blockNo) {
  vector<int> blockIdx=GetBlockIndex(blockNo);
  vector<int> Rblock;
  for(int i=blockIdx.at(0)+1;i<(int)posPair.size();++i) {
    for(int j=blockIdx.at(1)+1;j<(int)negPair.size();++j) {
      if(posPair.at(i)==negPair.at(j)) {
        Rblock.push_back(posPair.at(i));
        //cout<<"Push "<<posPair.at(i)<<endl;
        break;
      }
    }
  }
  return(Rblock);
}

vector<int> SeqPair::GetLeftBlock(int blockNo) {
  vector<int> blockIdx=GetBlockIndex(blockNo);
  vector<int> Lblock;
  for(int i=0; i<blockIdx.at(0); ++i) {
    for(int j=0; j<blockIdx.at(1); ++j) {
      if(posPair.at(i)==negPair.at(j)) {Lblock.push_back(posPair.at(i));break;}
    }
  }
  return(Lblock);
}

vector<int> SeqPair::GetAboveBlock(int blockNo) {
  vector<int> blockIdx=GetBlockIndex(blockNo);
  vector<int> Ablock;
  for(int i=0; i<blockIdx.at(0); ++i) {
    for(int j=blockIdx.at(1)+1;j<(int)negPair.size();++j) {
      if(posPair.at(i)==negPair.at(j)) {Ablock.push_back(posPair.at(i));break;}
    }
  }
  return(Ablock);
}

vector<int> SeqPair::GetBelowBlock(int blockNo) {
  vector<int> blockIdx=GetBlockIndex(blockNo);
  vector<int> Bblock;
  for(int i=blockIdx.at(0)+1;i<(int)posPair.size();++i) {
    for(int j=0; j<blockIdx.at(1); ++j) {
      if(posPair.at(i)==negPair.at(j)) {Bblock.push_back(posPair.at(i));break;}
    }
  }
  return(Bblock);
}

placerDB::Omark SeqPair::GetBlockOrient(int blockNo) {
  return orient.at(blockNo);
}

void SeqPair::ChangeOrient(int blockNo, placerDB::Omark ort) {
  orient.at(blockNo)=ort;
}


void SeqPair::AdjustOrient(int blockNo, placerDB::Omark ort) {
  switch(orient.at(blockNo)) {
    case placerDB::N: if(ort==placerDB::N || ort==placerDB::S || ort==placerDB::FN || ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::S: if(ort==placerDB::N || ort==placerDB::S || ort==placerDB::FN || ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::FN:if(ort==placerDB::N || ort==placerDB::S || ort==placerDB::FN || ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::FS:if(ort==placerDB::N || ort==placerDB::S || ort==placerDB::FN || ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::E: if(ort==placerDB::E || ort==placerDB::W || ort==placerDB::FE || ort==placerDB::FW)  orient.at(blockNo)=ort;
            break;
    case placerDB::W: if(ort==placerDB::E || ort==placerDB::W || ort==placerDB::FE || ort==placerDB::FW)  orient.at(blockNo)=ort;
            break;
    case placerDB::FE:if(ort==placerDB::E || ort==placerDB::W || ort==placerDB::FE || ort==placerDB::FW)  orient.at(blockNo)=ort;
            break;
    case placerDB::FW:if(ort==placerDB::E || ort==placerDB::W || ort==placerDB::FE || ort==placerDB::FW)  orient.at(blockNo)=ort;
            break;
    default:break;
  }
}

void SeqPair::FlipOrient(int blockNo) {
  switch(orient.at(blockNo)) {
    case placerDB::N: orient.at(blockNo)=placerDB::FN;break;
    case placerDB::S: orient.at(blockNo)=placerDB::FS;break;
    case placerDB::E: orient.at(blockNo)=placerDB::FE;break;
    case placerDB::W: orient.at(blockNo)=placerDB::FW;break;
    case placerDB::FN:orient.at(blockNo)=placerDB::N;break;
    case placerDB::FS:orient.at(blockNo)=placerDB::S;break;
    case placerDB::FE:orient.at(blockNo)=placerDB::E;break;
    case placerDB::FW:orient.at(blockNo)=placerDB::W;break;
    default:break;
  }
}

void SeqPair::SwitchSingleSequence(int b1, int b2, bool flag) {
  vector<int> oldPair;
  if(flag) {
    oldPair=posPair;
    this->posPair.clear();
    for(int i=0;i<(int)oldPair.size(); ++i) {
      if(oldPair.at(i)==b1) { posPair.push_back(b2);
      } else if (oldPair.at(i)==b2) { posPair.push_back(b1);
      } else { posPair.push_back( oldPair.at(i) );
      }
    }
  } else {
    oldPair=negPair;
    this->negPair.clear();
    for(int i=0;i<(int)oldPair.size(); ++i) {
      if(oldPair.at(i)==b1) { negPair.push_back(b2);
      } else if (oldPair.at(i)==b2) { negPair.push_back(b1);
      } else { negPair.push_back( oldPair.at(i) );
      }
    }
  }
}

void SeqPair::SwitchDoubleSequence(int b1, int b2) {
  SwitchSingleSequence(b1,b2,true);
  SwitchSingleSequence(b1,b2,false);
}

vector<int> SeqPair::FindShortSeq(design& caseNL, vector<int>& seq, int idx) {
  vector<int> newQ;
  for(vector<int>::iterator it=seq.begin(); it!=seq.end(); ++it) {
    if( *it<caseNL.GetSizeofBlocks() && *it>=0) {
      if(caseNL.GetBlockSymmGroup(*it)==idx) { newQ.push_back(*it); }
    }
  }
  return newQ;
}

int SeqPair::GetVertexIndexinSeq(vector<int>& seq, int v) {
  int idx=-1;
  for(int i=0;i<(int)seq.size(); ++i) {
    if(seq.at(i)==v) {idx=i; break;}
  }
  return idx;
}

bool SeqPair::FastInitialScan(design& caseNL) {
// return true if any violation found, otherwise return false
// Current feature: only support scan of symmetry constraints
// Future supports: will support scan of general placement constraints
  bool mark=true;
  for(int b=0; b<(int)caseNL.GetSizeofSBlocks() && mark ; ++b) {
    // for each symmetry group
    placerDB::Smark axis=symAxis.at(b);
    vector<int> posQ=FindShortSeq(caseNL, posPair, b);
    vector<int> negQ=FindShortSeq(caseNL, negPair, b);
    for(int i=0; i<(int)posQ.size() && mark ; ++i) {
      for(int j=i+1; j<(int)posQ.size() && mark ; ++j) { 
        // V: posSeq_i < posSeq_j <==> negSeq_counter(j) < negSeq_counter(i)
        // H: posSeq_i < posSeq_j <==> negSeq_counter(i) < negSeq_counter(j)
        int negi=GetVertexIndexinSeq(negQ , caseNL.GetBlockCounterpart( posQ.at(i) ) );
        int negj=GetVertexIndexinSeq(negQ , caseNL.GetBlockCounterpart( posQ.at(j) ) );
        if(axis==placerDB::V) {
          if(negj>negi) {mark=false;}
        } else if (axis==placerDB::H) {
          if(negj<negi) {mark=false;}
        }
        //cout<<"Check "<<posQ[i]<<"-"<<caseNL.GetBlockCounterpart( posQ.at(i) )<<" vs "<<posQ[j]<<"-"<<caseNL.GetBlockCounterpart( posQ.at(j) )<<" in posQ "<<mark<<endl;
      }
    }
    for(int i=0; i<(int)negQ.size() && mark; ++i) {
      for(int j=i+1; j<(int)negQ.size() && mark ; ++j) {
        int posi=GetVertexIndexinSeq(posQ , caseNL.GetBlockCounterpart( negQ.at(i) ) );
        int posj=GetVertexIndexinSeq(posQ , caseNL.GetBlockCounterpart( negQ.at(j) ) );
        if(axis==placerDB::V) {
          if(posj>posi) {mark=false;}
        } else if (axis==placerDB::H) {
          if(posj<posi) {mark=false;}
        }
        //cout<<"Check "<<negQ[i]<<"-"<<caseNL.GetBlockCounterpart( negQ.at(i) )<<" vs "<<negQ[j]<<"-"<<caseNL.GetBlockCounterpart( negQ.at(j) )<<" in negQ "<<mark<<endl;
      }
    }
  }
  return !mark;
}

placerDB::Smark SeqPair::GetSymmBlockAxis(int SBidx) {
  return symAxis.at(SBidx);
}

bool SeqPair::ChangeSelectedBlock(design& caseNL) {
  auto logger = spdlog::default_logger()->clone("placer.SeqPair.ChangeSelectedBlock");
  int anode=rand() % caseNL.GetSizeofBlocks();
  if(caseNL.mixFlag) {
    while(caseNL.GetMappedBlockIdx(anode)!=-1) {
      anode=rand() % caseNL.GetSizeofBlocks();
    } // randomly choose a block
  }
  if(caseNL.Blocks.at(anode).size()<=1) {
    logger->debug("anode size < 1");
    return false;
  }
  int newsel=rand() % caseNL.Blocks.at(anode).size();
  selected.at(anode)=newsel;
  if(caseNL.GetBlockCounterpart(anode)!=-1) { selected.at( caseNL.GetBlockCounterpart(anode) )=newsel;}
  return true;
}

void SeqPair::KeepOrdering(design& caseNL) {
  // ids of blocks which have order constraints
  set<int> block_id_with_order;
  for (auto order : caseNL.Ordering_Constraints) {
    block_id_with_order.insert(order.first.first);
    block_id_with_order.insert(order.first.second);
  }
  // places of block_id_with_order in pair
  vector<int> pos_idx, neg_idx;


  for (unsigned int i = 0; i < posPair.size(); i++) {
    if (block_id_with_order.find(posPair[i]) != block_id_with_order.end()) pos_idx.push_back(i);
    if (block_id_with_order.find(negPair[i]) != block_id_with_order.end()) neg_idx.push_back(i);
  }



  vector<int> pos_order(block_id_with_order.size()), neg_order(block_id_with_order.size());
  for (unsigned int i = 0; i < block_id_with_order.size(); i++) {
    pos_order[i] = posPair[pos_idx[i]];
    neg_order[i] = negPair[neg_idx[i]];
  }
  bool pos_keep_order = true, neg_keep_order = true;
  //unsigned seed = std::chrono::system_clock::now().time_since_epoch().count();
  //std::default_random_engine e(seed);
  // generate a pos order
  do {
	  int first_it, second_it;
    pos_keep_order = true;
    for (auto order : caseNL.Ordering_Constraints) {
		  first_it = find(pos_order.begin(), pos_order.end(), order.first.first)- pos_order.begin();
		  second_it = find(pos_order.begin(), pos_order.end(), order.first.second)- pos_order.begin();
      if (first_it - second_it > 0) {
        pos_keep_order = false;
        break;
      }
    }
    if (!pos_keep_order) {
	    swap(pos_order.at(first_it), pos_order.at(second_it));
      //shuffle(pos_order.begin(), pos_order.end(), e);
    }

  } while (!pos_keep_order);
  // generate a neg order
  do {
	  int first_it, second_it;
    neg_keep_order = true;
    for (auto order : caseNL.Ordering_Constraints) {
		  first_it = find(neg_order.begin(), neg_order.end(), order.first.first) - neg_order.begin();
		  second_it = find(neg_order.begin(), neg_order.end(), order.first.second) - neg_order.begin();
	    if (first_it - second_it < 0) {
        if (order.second == placerDB::V) {
          neg_keep_order = false;
          break;
        }
      } else if (order.second == placerDB::H) {
        neg_keep_order = false;
        break;
      }
    }
    if (!neg_keep_order) {
	    swap(neg_order.at(first_it), neg_order.at(second_it));
      //shuffle(neg_order.begin(), neg_order.end(), e);
    }
  } while (!neg_keep_order);
  //write order back to pospair and negpair

  for (unsigned int i = 0; i < pos_idx.size(); i++) {
    posPair[pos_idx[i]] = pos_order[i];
    negPair[neg_idx[i]] = neg_order[i];
  }

}

inline size_t SeqPair::Factorial(const size_t& t)
{
  if (t <= 1) return 1;
  return t * Factorial(t - 1);
}

void SeqPair::PerturbationNew(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));

  if (_seqPairEnum) {
    posPair = _seqPairEnum->PosPair();
    negPair = _seqPairEnum->NegPair();
    selected = _seqPairEnum->Selected();
    _seqPairEnum->Permute();
  } else {
    bool mark=false;
    std::set<int> pool;
    // 0:ChangeSelectedBlock
    // 1:MoveAsymmetricBlockposPair
    // 2:MoveAsymmetricBlocknegPair
    // 3:MoveAsymmetricBlockdoublePair
    // 4:ChangeAsymmetricBlockOrient
    // 5:SwapTwoBlocksofSameGroup
    // 6:SwapTwoSymmetryGroup
    // 7:ChangeSymmetryBlockOrient
    // 8:SwapMultiBlocksofSameGroup
    // 9:RotateSymmetryGroup
    if(caseNL.GetSizeofBlocks()<=1) {return;}
    if(caseNL.noBlock4Move>0) {pool.insert(0);}
    if(caseNL.noAsymBlock4Move>0) { pool.insert(1); pool.insert(2); pool.insert(3);}
    if(caseNL.noSymGroup4PartMove>0) {pool.insert(5); pool.insert(8); } 
    if(caseNL.noSymGroup4FullMove>1) {pool.insert(6);}
    int fail = 0;
    int count = 20;
    while(!mark && fail<count) {
      //std::cout<<int(pool.size())<<std::endl;
      int choice=rand() % int(pool.size());
      std::set<int>::iterator cit=pool.begin(); std::advance(cit, choice);
      switch(*cit) {
        case 0: mark=ChangeSelectedBlock(caseNL); break;
        case 1: mark=MoveAsymmetricBlockposPair(caseNL); break;
        case 2: mark=MoveAsymmetricBlocknegPair(caseNL); break;
        case 3: mark=MoveAsymmetricBlockdoublePair(caseNL); break;
                //case 4: mark=ChangeAsymmetricBlockOrient(caseNL); break;
        case 5: mark=SwapTwoBlocksofSameGroup(caseNL); break;
        case 6: mark=SwapTwoSymmetryGroup(caseNL); break;
                //case 7: mark=ChangeSymmetryBlockOrient(caseNL); break;
        case 8: mark=SwapMultiBlocksofSameGroup(caseNL); break;
                //case 9: mark=RotateSymmetryGroup(caseNL); break;
        default: mark=false;
      }
      fail++;
    }
  }
  //auto logger = spdlog::default_logger()->clone("placer.SeqPair.PerturbationNew");
  //std::string pos("{ "), neg("{ "), sel("{ ");
  //for (auto& it : posPair) pos += (std::to_string(it) + " ");
  //for (auto& it : negPair) neg += (std::to_string(it) + " ");
  //for (auto& it : selected) sel += (std::to_string(it) + " ");
  //pos += "}";
  //neg += "}";
  //sel += "}";
  //logger->info("seq pair {0} {1} {2}", pos, neg, sel);

  KeepOrdering(caseNL);
}

void SeqPair::Perturbation(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  int choice;
  bool mark=false;
  //cout<<"Perturbation?"<<endl;
  while(!mark) {
    if(!caseNL.designHasAsymBlock() && caseNL.GetSymGroupSize()==1 ) {
      choice=rand() % 3;
      //cout<<"Perturbation choice "<<choice<<endl;
      switch(choice) {
        case 0: mark=SwapTwoBlocksofSameGroup(caseNL); break;
        case 1: mark=ChangeSymmetryBlockOrient(caseNL); break;
        case 2: mark=SwapMultiBlocksofSameGroup(caseNL); break;
        //case 2: mark=RotateSymmetryGroup(caseNL); break;
        default: mark=SwapTwoBlocksofSameGroup(caseNL);
      }
    } else if(!caseNL.designHasAsymBlock()) {
      choice=rand() % 3;
      //cout<<"Perturbation choice "<<choice<<endl;
      switch(choice) {
        case 0: mark=SwapTwoBlocksofSameGroup(caseNL); break;
        case 1: mark=SwapTwoSymmetryGroup(caseNL); break;
        case 2: mark=ChangeSymmetryBlockOrient(caseNL); break;
        //case 3: mark=RotateSymmetryGroup(caseNL); break;
        default: mark=SwapTwoBlocksofSameGroup(caseNL);
      }
    } else if (!caseNL.designHasSymGroup()) {
      choice=rand() % 4;
      //cout<<"Perturbation choice "<<choice<<endl;
      switch(choice) {
        case 0: mark=MoveAsymmetricBlockposPair(caseNL); break;
        case 1: mark=MoveAsymmetricBlocknegPair(caseNL); break;
        case 2: mark=MoveAsymmetricBlockdoublePair(caseNL); break;
        case 3: mark=ChangeAsymmetricBlockOrient(caseNL); break;
        default: mark=MoveAsymmetricBlockdoublePair(caseNL);
      }
    } else {
      choice=rand() % 7;
      //cout<<"Perturbation choice "<<choice<<endl;
      switch(choice) {
        case 0: mark=MoveAsymmetricBlockposPair(caseNL); break;
        case 1: mark=MoveAsymmetricBlocknegPair(caseNL); break;
        case 2: mark=MoveAsymmetricBlockdoublePair(caseNL); break;
        case 3: mark=SwapTwoBlocksofSameGroup(caseNL); break;
        case 4: mark=SwapTwoSymmetryGroup(caseNL); break;
        case 5: mark=ChangeAsymmetricBlockOrient(caseNL); break;
        case 6: mark=ChangeSymmetryBlockOrient(caseNL); break;
        //case 7: mark=RotateSymmetryGroup(caseNL); break;
        default: mark=MoveAsymmetricBlockdoublePair(caseNL);
      }
    }
  }
  //int sgsize=caseNL.GetSizeofSBlocks();
  //if(sgsize==0) {
  //  // no symmetry group
  //} else if(sgsize==1) {
  //  // one symmetry group
  //} else if(sgsize>1) {
  //  // more than one symmetry group
  //} else {
  //}
}

void SeqPair::TestSwap() {
  // For testing
  vector<int> Alist, Blist;
  Blist.push_back(2);
  Blist.push_back(4);
  Blist.push_back(6);
  Alist.push_back(3);
  Alist.push_back(5);
  this->posPair=SwapTwoListinSeq(Alist, Blist, this->posPair);
  //this->negPair=SwapTwoListinSeq(Alist, Blist, this->negPair);
}

bool SeqPair::SwapTwoSymmetryGroup(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  int sgA, sgB;
  if(caseNL.GetSizeofSBlocks()<=1) { 
    return false;
  } else {
    sgA=rand() % caseNL.GetSizeofSBlocks();
    sgB=rand() % caseNL.GetSizeofSBlocks();
    while(sgB==sgA) { sgB=rand() % caseNL.GetSizeofSBlocks(); }
  }
  if(caseNL.mixFlag) {
    if(caseNL.GetMappedSymmBlockIdx(sgA)!=-1 || caseNL.GetMappedSymmBlockIdx(sgB)!=-1) {return false;}
  }
  //cout<<"Swap symmetry group "<<sgA<<" and "<<sgB<<endl;
  vector<int> Alist=caseNL.GetRealBlockPlusAxisListfromSymmGroup(sgA);
  vector<int> Blist=caseNL.GetRealBlockPlusAxisListfromSymmGroup(sgB);

  this->posPair=SwapTwoListinSeq(Alist, Blist, this->posPair);
  this->negPair=SwapTwoListinSeq(Alist, Blist, this->negPair);
  return true;
}

vector<int> SeqPair::GetVerticesIndexinSeq(vector<int>& seq, vector<int>& L) {
  vector<int> idx;
  for(int i=0;i<(int)seq.size();++i) {
    for(vector<int>::iterator it=L.begin(); it!=L.end(); ++it) {
      if(seq.at(i)==*it) {idx.push_back(i);break;}
    }
  }
  return idx;
}

vector<int> SeqPair::SwapTwoListinSeq(vector<int>& Alist, vector<int>& Blist, vector<int>& seq) {

  auto logger = spdlog::default_logger()->clone("placer.SeqPair.SwapTwoListinSeq");

  vector<int> newseq=seq;
  vector<int> Apos=GetVerticesIndexinSeq(seq, Alist);
  vector<int> Bpos=GetVerticesIndexinSeq(seq, Blist);
  //cout<<"Apos: ";
  //for(vector<int>::iterator it=Apos.begin();it!=Apos.end();it++) {cout<<" "<<*it;} 
  //cout<<endl;
  //cout<<"Bpos: ";
  //for(vector<int>::iterator it=Bpos.begin();it!=Bpos.end();it++) {cout<<" "<<*it;} 
  //cout<<endl;
  //vector<int> AL=Alist;
  //vector<int> BL=Blist;
  //if(Apos.at(0)>Bpos.at(0)) {
  //  //vector<int> tmp=BL;   BL=AL;     AL=tmp;
  //  vector<int> tmp=Bpos; Bpos=Apos; Apos=tmp;
  //} // Make Apos_0 , ..., Bpos_0
  // A0, A1, ..., An
  //     B0, B1, ..., Bm
  if(Apos.size()==Bpos.size()) {
    for(int i=0;i<(int)Apos.size();++i) {
      //newseq.at(Apos.at(i))=seq.at(Bpos.at(i)); // B --> A
      //newseq.at(Bpos.at(i))=seq.at(Apos.at(i)); // A --> B
      int temp_value = newseq.at(Apos.at(i));
      newseq.at(Apos.at(i))=newseq.at(Bpos.at(i)); // B --> A
      newseq.at(Bpos.at(i))=temp_value;//A --> B
    }
  } else if (Apos.size()<Bpos.size()) {
    for(int i=0;i<(int)Apos.size();++i)
      newseq.at(Bpos.at(i))=seq.at(Apos.at(i)); // A --> B
    // Merge sort to create new Apos list
    vector<int> newApos;
    vector<int>::iterator ait=Apos.begin();
    vector<int>::iterator bit=Bpos.begin()+Apos.size();
    while(ait!=Apos.end() && bit!=Bpos.end()) {
      if( (*ait)<(*bit) ) {
        newApos.push_back(*ait); ++ait;
      } else if ( (*ait)>(*bit) ) {
        newApos.push_back(*bit); ++bit;
      } else {
        logger->debug("Placer-Error: same index for different lists!");
      }
    }
    while(ait!=Apos.end()) { newApos.push_back(*ait); ++ait; }
    while(bit!=Bpos.end()) { newApos.push_back(*bit); ++bit; }
    for(int i=0;i<(int)Bpos.size();++i)
      newseq.at(newApos.at(i))=seq.at(Bpos.at(i)); // B--> A
  } else {
    for(int i=0;i<(int)Bpos.size();++i)
      newseq.at(Apos.at(i))=seq.at(Bpos.at(i)); // B --> A
    // Merge sort to create new Bpos list
    vector<int> newBpos;
    vector<int>::iterator ait=Apos.begin()+Bpos.size();
    vector<int>::iterator bit=Bpos.begin();
    while(ait!=Apos.end() && bit!=Bpos.end()) {
      if( (*ait)<(*bit) ) {
        newBpos.push_back(*ait); ++ait;
      } else if ( (*ait)>(*bit) ) {
        newBpos.push_back(*bit); ++bit;
      } else {
        logger->debug("Placer-Error: same index for different lists!");
      }
    }
    while(ait!=Apos.end()) { newBpos.push_back(*ait); ++ait; }
    while(bit!=Bpos.end()) { newBpos.push_back(*bit); ++bit; }
    for(int i=0;i<(int)Apos.size();++i)
      newseq.at(newBpos.at(i))=seq.at(Apos.at(i)); // A--> B
  }
  return newseq;
}

bool SeqPair::SwapTwoBlocksofSameGroup(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  int sgid;
  if(caseNL.GetSizeofSBlocks()>1) {
    sgid=rand() % caseNL.GetSizeofSBlocks();
  } else if (caseNL.GetSizeofSBlocks()==1) {
    sgid=0;
  } else { return false; }
  //cout<<"sgid "<<sgid<<endl;
  vector<int> blist=caseNL.GetRealBlockListfromSymmGroup(sgid); // all real blocks in symmetry group cosidering mixFlag
  //cout<<"blist size: "<<blist.size()<<endl;
  if(blist.empty() || (int)blist.size()==1) {return false;}//std::cout<<"empty or 1"<<std::endl;}
  if((int)blist.size()==2 && blist.at(0)==caseNL.GetBlockCounterpart(blist.at(1))) {return false;}
  int A=blist.at( rand() % (int)blist.size() );
  //while(A>=(int)caseNL.GetSizeofBlocks()) {
  //   A=blist.at( rand() % (int)blist.size() );
  //}
  int symA=caseNL.GetBlockCounterpart(A);
  int B=blist.at( rand() % (int)blist.size() );
  while(B==A || B==symA)  {
    B=blist.at( rand() % (int)blist.size() );
  }
  //while(B==A || B==symA || B>=(int)caseNL.GetSizeofBlocks() )  {
  //  B=blist.at( rand() % (int)blist.size() );
  //}
  int symB=caseNL.GetBlockCounterpart(B);
  int Apos=GetVertexIndexinSeq(posPair, A);
  int Bpos=GetVertexIndexinSeq(posPair, B);
  int symApos=GetVertexIndexinSeq(negPair, symA);
  int symBpos=GetVertexIndexinSeq(negPair, symB);
  //cout<<endl<<"Swap "<<A<<" and "<<B<<" in pos SP"<<endl;
  //cout<<"Swap "<<symA<<" and "<<symB<<" in neg SP"<<endl;
  posPair.at(Bpos)=A; 
  posPair.at(Apos)=B;
  negPair.at(symBpos)=symA;
  negPair.at(symApos)=symB;
  return true;
}

bool SeqPair::SwapMultiBlocksofSameGroup(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  int count=3;
  int sgid;
  if(caseNL.GetSizeofSBlocks()>1) {
    sgid=rand() % caseNL.GetSizeofSBlocks();
  } else if (caseNL.GetSizeofSBlocks()==1) {
    sgid=0;
  } else { return false; }
  //cout<<"sgid "<<sgid<<endl;
  vector<int> blist=caseNL.GetRealBlockListfromSymmGroup(sgid); // all real blocks in symmetry group considering mixFlag
  //cout<<"blist size: "<<blist.size()<<endl;
  if(blist.empty() || (int)blist.size()==1) {return false;}//std::cout<<"empty or 2"<<std::endl;}
  if((int)blist.size()==2 && blist.at(0)==caseNL.GetBlockCounterpart(blist.at(1))) {return false;}
  for(int i=0;i<count;++i) {
    int A=blist.at( rand() % (int)blist.size() );
    //while(A>=(int)caseNL.GetSizeofBlocks()) {
    //   A=blist.at( rand() % (int)blist.size() );
    //}
    int symA=caseNL.GetBlockCounterpart(A);
    int B=blist.at( rand() % (int)blist.size() );
    while(B==A || B==symA)  {
      B=blist.at( rand() % (int)blist.size() );
    }
    //while(B==A || B==symA || B>=(int)caseNL.GetSizeofBlocks() )  {
    //  B=blist.at( rand() % (int)blist.size() );
    //}
    int symB=caseNL.GetBlockCounterpart(B);
    int Apos=GetVertexIndexinSeq(posPair, A);
    int Bpos=GetVertexIndexinSeq(posPair, B);
    int symApos=GetVertexIndexinSeq(negPair, symA);
    int symBpos=GetVertexIndexinSeq(negPair, symB);
    //cout<<endl<<"Swap "<<A<<" and "<<B<<" in pos SP"<<endl;
    //cout<<"Swap "<<symA<<" and "<<symB<<" in neg SP"<<endl;
    posPair.at(Bpos)=A; 
    posPair.at(Apos)=B;
    negPair.at(symBpos)=symA;
    negPair.at(symApos)=symB;
  }
  return true;
}

bool SeqPair::MoveAsymmetricBlockposPair(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  if(!caseNL.checkAsymmetricBlockExist()) {return false;}
  int anode=rand() % caseNL.GetSizeofBlocks();
  while(caseNL.GetBlockSymmGroup(anode)>=0) {
    anode=rand() % caseNL.GetSizeofBlocks();
  } // randomly choose an asymmetric block
  if(caseNL.mixFlag && caseNL.GetMappedBlockIdx(anode)!=-1) {return false;}
  //cout<<endl<<"Move asymmetric block in pos SP"<<endl;
  return MoveAsymmetricBlockUnit(caseNL, this->posPair, anode);
}

bool SeqPair::MoveAsymmetricBlocknegPair(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  if(!caseNL.checkAsymmetricBlockExist()) {return false;}
  int anode=rand() % caseNL.GetSizeofBlocks();
  while(caseNL.GetBlockSymmGroup(anode)>=0) {
    anode=rand() % caseNL.GetSizeofBlocks();
  } // randomly choose an asymmetric block
  if(caseNL.mixFlag && caseNL.GetMappedBlockIdx(anode)!=-1) {return false;}
  //cout<<endl<<"Move asymmetric block in neg SP"<<endl;
  return MoveAsymmetricBlockUnit(caseNL, this->negPair, anode);
}

bool SeqPair::MoveAsymmetricBlockdoublePair(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  if(!caseNL.checkAsymmetricBlockExist()) {return false;}
  int anode=rand() % caseNL.GetSizeofBlocks();
  while(caseNL.GetBlockSymmGroup(anode)>=0) {
    anode=rand() % caseNL.GetSizeofBlocks();
  } // randomly choose an asymmetric block
  if(caseNL.mixFlag && caseNL.GetMappedBlockIdx(anode)!=-1) {return false;}
  bool mark=true;
  //cout<<endl<<"Move asymmetric block in pos SP"<<endl;
  mark=mark&&MoveAsymmetricBlockUnit(caseNL, this->posPair, anode);
  //cout<<"Move asymmetric block in neg SP"<<endl;
  mark=mark&&MoveAsymmetricBlockUnit(caseNL, this->negPair, anode);
  return mark;
}

bool SeqPair::MoveAsymmetricBlockUnit(design& caseNL, vector<int>& seq, int anode) {
  /* initialize random seed: */
  //srand(time(NULL));
  vector<int> newseq;
  newseq.resize(seq.size());
  int oldpos=GetVertexIndexinSeq(seq, anode); // position of anode in original seqence
  int newpos=rand() % (int)seq.size();
  while(oldpos==newpos) {
    newpos=rand() % (int)seq.size();
  } // randomly choose a new position
  //cout<<"Aymnode-"<<anode<<" oldpos-"<<oldpos<<" newpos-"<<newpos<<endl;

  if(oldpos<newpos) {
    for(int i=0;i<oldpos;++i) 
      newseq.at(i)=seq.at(i);
    for(int i=oldpos+1;i<=newpos;++i) 
      newseq.at(i-1)=seq.at(i);
    for(int i=newpos+1;i<(int)seq.size();++i)
      newseq.at(i)=seq.at(i);
    newseq.at(newpos)=seq.at(oldpos);
  } else if (oldpos>newpos) {
    for(int i=0;i<newpos;++i)
      newseq.at(i)=seq.at(i);
    newseq.at(newpos)=seq.at(oldpos);
    for(int i=newpos+1;i<=oldpos;++i)
      newseq.at(i)=seq.at(i-1);
    for(int i=oldpos+1;i<(int)seq.size();++i)
      newseq.at(i)=seq.at(i);
  }
  seq=newseq;
  return true;
}

bool SeqPair::ChangeAsymmetricBlockOrient(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  if(!caseNL.checkAsymmetricBlockExist()) {return false;}
  int anode=rand() % caseNL.GetSizeofBlocks();
  while(caseNL.GetBlockSymmGroup(anode)>=0) {
    anode=rand() % caseNL.GetSizeofBlocks();
  } // randomly choose an asymmetric block
  if(caseNL.mixFlag && caseNL.GetMappedBlockIdx(anode)!=-1) {return false;}
  bool mark=false;
  placerDB::Omark curr_ort=orient.at(anode);
  placerDB::Omark ort;
  //cout<<endl<<"Change orientation of asymmetric block "<<anode<<endl;
  // Currently we try to keep the orientation for fin alignment
  // and prevent to change the orientation arbitrarily
  while(!mark) {
    ort=placerDB::Omark( rand() % 8 );
    switch(curr_ort) {
      case placerDB::N: if(ort==placerDB::S || ort==placerDB::FN || ort==placerDB::FS)  {orient.at(anode)=ort;mark=true; }
              break;
      case placerDB::S: if(ort==placerDB::N || ort==placerDB::FN || ort==placerDB::FS)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FN:if(ort==placerDB::N || ort==placerDB::S  || ort==placerDB::FS)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FS:if(ort==placerDB::N || ort==placerDB::S  || ort==placerDB::FN)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::E: if(ort==placerDB::W || ort==placerDB::FE || ort==placerDB::FW)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::W: if(ort==placerDB::E || ort==placerDB::FE || ort==placerDB::FW)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FE:if(ort==placerDB::E || ort==placerDB::W  || ort==placerDB::FW)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FW:if(ort==placerDB::E || ort==placerDB::W  || ort==placerDB::FE)  {orient.at(anode)=ort;mark=true; }
              break;
      default:break;
    }
  }
  return mark;
}

bool SeqPair::ChangeSymmetryBlockOrient(design& caseNL) {
  // Known limitation: due to the restricition of verical symmetry, we do not change
  // the orientation of block into E/W/FE/FW
  /* initialize random seed: */
  //srand(time(NULL));
  int sgid;
  if(caseNL.GetSizeofSBlocks()>1) {
    sgid=rand() % caseNL.GetSizeofSBlocks();
  } else if (caseNL.GetSizeofSBlocks()==1) {
    sgid=0;
  } else { return false; }
  //cout<<endl<<"Change orientation of cell in symmetry group "<<sgid<<endl;
  placerDB::Smark new_axis, self_axis;
  new_axis=symAxis.at(sgid);
  vector<int> Blist=caseNL.GetRealBlockListfromSymmGroup(sgid); // already consider mixFlag in GetRealBlockListfromSymmGroup
  if(Blist.empty()) {return false;}
  int tar;
  if((int)Blist.size()==1) {
    tar=Blist.at(0);
  } else {
    tar=Blist.at(rand() % (int)Blist.size());
  }
  // Change orientation of cells in symmetry group
  if(caseNL.SBlocks.at(sgid).selfsym.empty()) {
    //			sympair-sympair
    // 	new axis V	N/S/E/W/FN/FS/FE/FW-FN/FS/FE/FW/N/S/E/W
    // 	new axis H	N/S/E/W/FN/FS/FE/FW-FS/FN/FW/FE/S/N/W/E
    if(new_axis==placerDB::V) {
      int sa=rand()%4;
      switch(sa) {
        case 0: orient.at(tar)= placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FN; break;
        case 1: orient.at(tar)= placerDB::S;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FS; break;
        case 2: orient.at(tar)= placerDB::FN; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::N; break;
        case 3: orient.at(tar)= placerDB::FS; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::S; break;
        case 4: orient.at(tar)= placerDB::E;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FE; break;
        case 5: orient.at(tar)= placerDB::W;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FW; break;
        case 6: orient.at(tar)= placerDB::FE; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::E; break;
        case 7: orient.at(tar)= placerDB::FW; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::W; break;
        default: orient.at(tar)=placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FN;
      }
    } else if(new_axis==placerDB::H) {
       int sa=rand()%4;
       switch(sa) {
         case 0: orient.at(tar)=placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FS; break;
         case 1: orient.at(tar)=placerDB::S;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FN; break;
         case 2: orient.at(tar)=placerDB::FN; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::S; break;
         case 3: orient.at(tar)=placerDB::FS; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::N; break;
         case 4: orient.at(tar)=placerDB::E;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FW; break;
         case 5: orient.at(tar)=placerDB::W;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FE; break;
         case 6: orient.at(tar)=placerDB::FE; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::W; break;
         case 7: orient.at(tar)=placerDB::FW; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::E; break;
         default:orient.at(tar)=placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FS;
       }
    }
  } else {
    //					sympair-sympair		selfsym
    // selfsym axis H	new axis V	N/S/FN/FS-FN/FS/N/S	N/S/FN/FS
    // 			new axis H	E/W/FE/FW-FW/FE/W/E	E/W/FE/FW
    // selfsym axis V	new axis H	N/S/FN/FS-FS/FN/S/N	N/S/FN/FS
    // 			new axis V	E/W/FE/FW-FE/FW/E/W	E/W/FE/FW	
    self_axis=caseNL.SBlocks.at(sgid).selfsym.at(0).second;
    if(self_axis==placerDB::V && new_axis==placerDB::V) {
    // 			new axis V	E/W/FE/FW-FE/FW/E/W	E/W/FE/FW	
      if(caseNL.GetBlockCounterpart(tar)==-1) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::E; break;
            case 1: orient.at(tar)=placerDB::W; break;
            case 2: orient.at(tar)=placerDB::FE; break;
            case 3: orient.at(tar)=placerDB::FW; break;
            default:orient.at(tar)=placerDB::E;
          }
      } else {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::E;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FE; break;
            case 1: orient.at(tar)=placerDB::W;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FW; break;
            case 2: orient.at(tar)=placerDB::FE; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::E; break;
            case 3: orient.at(tar)=placerDB::FW; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::W; break;
            default:orient.at(tar)=placerDB::E;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FE;
          }
      }
    } else if (self_axis==placerDB::V && new_axis==placerDB::H) {
    // selfsym axis V	new axis H	N/S/FN/FS-FS/FN/S/N	N/S/FN/FS
      if(caseNL.GetBlockCounterpart(tar)==-1) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::N; break;
            case 1: orient.at(tar)=placerDB::S; break;
            case 2: orient.at(tar)=placerDB::FN; break;
            case 3: orient.at(tar)=placerDB::FS; break;
            default:orient.at(tar)=placerDB::N;
          }
      } else {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FS; break;
            case 1: orient.at(tar)=placerDB::S;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FN; break;
            case 2: orient.at(tar)=placerDB::FN; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::S; break;
            case 3: orient.at(tar)=placerDB::FS; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::N; break;
            default:orient.at(tar)=placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FS;
          }
      }
    } else if (self_axis==placerDB::H && new_axis==placerDB::H) {
    // 			new axis H	E/W/FE/FW-FW/FE/W/E	E/W/FE/FW
      if(caseNL.GetBlockCounterpart(tar)==-1) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::E; break;
            case 1: orient.at(tar)=placerDB::W; break;
            case 2: orient.at(tar)=placerDB::FE; break;
            case 3: orient.at(tar)=placerDB::FW; break;
            default:orient.at(tar)=placerDB::E;
          }
      } else {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::E;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FW; break;
            case 1: orient.at(tar)=placerDB::W;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FE; break;
            case 2: orient.at(tar)=placerDB::FE; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::W; break;
            case 3: orient.at(tar)=placerDB::FW; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::E; break;
            default:orient.at(tar)=placerDB::E;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FW;
          }
      }
    } else if (self_axis==placerDB::H && new_axis==placerDB::V) {
    // selfsym axis H	new axis V	N/S/FN/FS-FN/FS/N/S	N/S/FN/FS
      if(caseNL.GetBlockCounterpart(tar)==-1) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::N; break;
            case 1: orient.at(tar)=placerDB::S; break;
            case 2: orient.at(tar)=placerDB::FN; break;
            case 3: orient.at(tar)=placerDB::FS; break;
            default:orient.at(tar)=placerDB::N;
          }
      } else {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(tar)=placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FN; break;
            case 1: orient.at(tar)=placerDB::S;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FS; break;
            case 2: orient.at(tar)=placerDB::FN; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::N; break;
            case 3: orient.at(tar)=placerDB::FS; orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::S; break;
            default:orient.at(tar)=placerDB::N;  orient.at(caseNL.GetBlockCounterpart(tar))=placerDB::FN;
          }
      }
    }
  }
  return true;
}

bool SeqPair::ChangeSymmetryGroupOrient(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  int sgid;
  if(caseNL.GetSizeofSBlocks()>1) {
    sgid=rand() % caseNL.GetSizeofSBlocks();
  } else if (caseNL.GetSizeofSBlocks()==1) {
    sgid=0;
  } else { return false; }
  //cout<<endl<<"Change orientation of symmetry group "<<sgid<<endl;
  if(caseNL.mixFlag && caseNL.GetMappedSymmBlockIdx(sgid)!=-1) {return false;}
  placerDB::Smark new_axis, self_axis;
  new_axis=symAxis.at(sgid);
  // Change orientation of cells in symmetry group
  if(caseNL.SBlocks.at(sgid).selfsym.empty()) {
    //			sympair-sympair
    // 	new axis V	N/S/E/W/FN/FS/FE/FW-FN/FS/FE/FW/N/S/E/W
    // 	new axis H	N/S/E/W/FN/FS/FE/FW-FS/FN/FW/FE/S/N/W/E
    if(new_axis==placerDB::V) {
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%8;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FN; break;
            case 1: orient.at(pit->first)=placerDB::S;  orient.at(pit->second)=placerDB::FS; break;
            case 2: orient.at(pit->first)=placerDB::FN; orient.at(pit->second)=placerDB::N; break;
            case 3: orient.at(pit->first)=placerDB::FS; orient.at(pit->second)=placerDB::S; break;
            case 4: orient.at(pit->first)=placerDB::E;  orient.at(pit->second)=placerDB::FE; break;
            case 5: orient.at(pit->first)=placerDB::W;  orient.at(pit->second)=placerDB::FW; break;
            case 6: orient.at(pit->first)=placerDB::FE; orient.at(pit->second)=placerDB::E; break;
            case 7: orient.at(pit->first)=placerDB::FW; orient.at(pit->second)=placerDB::W; break;
            default:orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FN;
          }
        }
      }
    } else if(new_axis==placerDB::H) {
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%8;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FS; break;
            case 1: orient.at(pit->first)=placerDB::S;  orient.at(pit->second)=placerDB::FN; break;
            case 2: orient.at(pit->first)=placerDB::FN; orient.at(pit->second)=placerDB::S; break;
            case 3: orient.at(pit->first)=placerDB::FS; orient.at(pit->second)=placerDB::N; break;
            case 4: orient.at(pit->first)=placerDB::E;  orient.at(pit->second)=placerDB::FW; break;
            case 5: orient.at(pit->first)=placerDB::W;  orient.at(pit->second)=placerDB::FE; break;
            case 6: orient.at(pit->first)=placerDB::FE; orient.at(pit->second)=placerDB::W; break;
            case 7: orient.at(pit->first)=placerDB::FW; orient.at(pit->second)=placerDB::E; break;
            default:orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FS;
          }
        }
      }
    }
  } else {
    //					sympair-sympair		selfsym
    // selfsym axis H	new axis V	N/S/FN/FS-FN/FS/N/S	N/S/FN/FS
    // 			new axis H	E/W/FE/FW-FW/FE/W/E	E/W/FE/FW
    // selfsym axis V	new axis H	N/S/FN/FS-FS/FN/S/N	N/S/FN/FS
    // 			new axis V	E/W/FE/FW-FE/FW/E/W	E/W/FE/FW	
    self_axis=caseNL.SBlocks.at(sgid).selfsym.at(0).second;
    if(self_axis==placerDB::V && new_axis==placerDB::V) {
    // 			new axis V	E/W/FE/FW-FE/FW/E/W	E/W/FE/FW	
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::E; break;
            case 1: orient.at(sit->first)=placerDB::W; break;
            case 2: orient.at(sit->first)=placerDB::FE; break;
            case 3: orient.at(sit->first)=placerDB::FW; break;
            default:orient.at(sit->first)=placerDB::E;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::E; orient.at(pit->second)=placerDB::FE; break;
            case 1: orient.at(pit->first)=placerDB::W; orient.at(pit->second)=placerDB::FW; break;
            case 2: orient.at(pit->first)=placerDB::FE;orient.at(pit->second)=placerDB::E; break;
            case 3: orient.at(pit->first)=placerDB::FW;orient.at(pit->second)=placerDB::W; break;
            default:orient.at(pit->first)=placerDB::E; orient.at(pit->second)=placerDB::FE;
          }
        }
      }
    } else if (self_axis==placerDB::V && new_axis==placerDB::H) {
    // selfsym axis V	new axis H	N/S/FN/FS-FS/FN/S/N	N/S/FN/FS
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::N; break;
            case 1: orient.at(sit->first)=placerDB::S; break;
            case 2: orient.at(sit->first)=placerDB::FN; break;
            case 3: orient.at(sit->first)=placerDB::FS; break;
            default:orient.at(sit->first)=placerDB::N;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FS; break;
            case 1: orient.at(pit->first)=placerDB::S;  orient.at(pit->second)=placerDB::FN; break;
            case 2: orient.at(pit->first)=placerDB::FN; orient.at(pit->second)=placerDB::S; break;
            case 3: orient.at(pit->first)=placerDB::FS; orient.at(pit->second)=placerDB::N; break;
            default:orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FS;
          }
        }
      }
    } else if (self_axis==placerDB::H && new_axis==placerDB::H) {
    // 			new axis H	E/W/FE/FW-FW/FE/W/E	E/W/FE/FW
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::E; break;
            case 1: orient.at(sit->first)=placerDB::W; break;
            case 2: orient.at(sit->first)=placerDB::FE; break;
            case 3: orient.at(sit->first)=placerDB::FW; break;
            default:orient.at(sit->first)=placerDB::E;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::E;  orient.at(pit->second)=placerDB::FW; break;
            case 1: orient.at(pit->first)=placerDB::W;  orient.at(pit->second)=placerDB::FE; break;
            case 2: orient.at(pit->first)=placerDB::FE; orient.at(pit->second)=placerDB::W; break;
            case 3: orient.at(pit->first)=placerDB::FW; orient.at(pit->second)=placerDB::E; break;
            default:orient.at(pit->first)=placerDB::E;  orient.at(pit->second)=placerDB::FW;
          }
        }
      }
    } else if (self_axis==placerDB::H && new_axis==placerDB::V) {
    // selfsym axis H	new axis V	N/S/FN/FS-FN/FS/N/S	N/S/FN/FS
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::N; break;
            case 1: orient.at(sit->first)=placerDB::S; break;
            case 2: orient.at(sit->first)=placerDB::FN; break;
            case 3: orient.at(sit->first)=placerDB::FS; break;
            default:orient.at(sit->first)=placerDB::N;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FN; break;
            case 1: orient.at(pit->first)=placerDB::S;  orient.at(pit->second)=placerDB::FS; break;
            case 2: orient.at(pit->first)=placerDB::FN; orient.at(pit->second)=placerDB::N; break;
            case 3: orient.at(pit->first)=placerDB::FS; orient.at(pit->second)=placerDB::S; break;
            default:orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FN;
          }
        }
      }
    }
  }
  return true;
}

bool SeqPair::RotateSymmetryGroup(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  int sgid;
  if(caseNL.GetSizeofSBlocks()>1) {
    sgid=rand() % caseNL.GetSizeofSBlocks();
  } else if (caseNL.GetSizeofSBlocks()==1) {
    sgid=0;
  } else { return false; }
  if(caseNL.mixFlag && caseNL.GetMappedSymmBlockIdx(sgid)!=-1) {return false;}
  //cout<<endl<<"Rotate symmetry group "<<sgid<<endl;
  placerDB::Smark old_axis, new_axis=placerDB::V, self_axis;
  old_axis=symAxis.at(sgid); 
  if(old_axis==placerDB::V) {
    new_axis=placerDB::H;
  } else if (old_axis==placerDB::H) {
    new_axis=placerDB::V;
  }
  symAxis.at(sgid)=new_axis;
  // Change orientation of cells in symmetry group
  if(caseNL.SBlocks.at(sgid).selfsym.empty()) {
    //			sympair-sympair
    // 	new axis V	N/S/E/W/FN/FS/FE/FW-FN/FS/FE/FW/N/S/E/W
    // 	new axis H	N/S/E/W/FN/FS/FE/FW-FS/FN/FW/FE/S/N/W/E
    if(new_axis==placerDB::V) {
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%8;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FN; break;
            case 1: orient.at(pit->first)=placerDB::S;  orient.at(pit->second)=placerDB::FS; break;
            case 2: orient.at(pit->first)=placerDB::FN; orient.at(pit->second)=placerDB::N; break;
            case 3: orient.at(pit->first)=placerDB::FS; orient.at(pit->second)=placerDB::S; break;
            case 4: orient.at(pit->first)=placerDB::E;  orient.at(pit->second)=placerDB::FE; break;
            case 5: orient.at(pit->first)=placerDB::W;  orient.at(pit->second)=placerDB::FW; break;
            case 6: orient.at(pit->first)=placerDB::FE; orient.at(pit->second)=placerDB::E; break;
            case 7: orient.at(pit->first)=placerDB::FW; orient.at(pit->second)=placerDB::W; break;
            default:orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FN;
          }
        }
      }
    } else if(new_axis==placerDB::H) {
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%8;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FS; break;
            case 1: orient.at(pit->first)=placerDB::S;  orient.at(pit->second)=placerDB::FN; break;
            case 2: orient.at(pit->first)=placerDB::FN; orient.at(pit->second)=placerDB::S; break;
            case 3: orient.at(pit->first)=placerDB::FS; orient.at(pit->second)=placerDB::N; break;
            case 4: orient.at(pit->first)=placerDB::E;  orient.at(pit->second)=placerDB::FW; break;
            case 5: orient.at(pit->first)=placerDB::W;  orient.at(pit->second)=placerDB::FE; break;
            case 6: orient.at(pit->first)=placerDB::FE; orient.at(pit->second)=placerDB::W; break;
            case 7: orient.at(pit->first)=placerDB::FW; orient.at(pit->second)=placerDB::E; break;
            default:orient.at(pit->first)=placerDB::N;  orient.at(pit->second)=placerDB::FS;
          }
        }
      }
    }
  } else {
    //					sympair-sympair		selfsym
    // selfsym axis H	new axis V	N/S/FN/FS-FN/FS/N/S	N/S/FN/FS
    // 			new axis H	E/W/FE/FW-FW/FE/W/E	E/W/FE/FW
    // selfsym axis V	new axis H	N/S/FN/FS-FS/FN/S/N	N/S/FN/FS
    // 			new axis V	E/W/FE/FW-FE/FW/E/W	E/W/FE/FW	
    self_axis=caseNL.SBlocks.at(sgid).selfsym.at(0).second;
    if(self_axis==placerDB::V && new_axis==placerDB::V) {
    // 			new axis V	E/W/FE/FW-FE/FW/E/W	E/W/FE/FW	
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::E; break;
            case 1: orient.at(sit->first)=placerDB::W; break;
            case 2: orient.at(sit->first)=placerDB::FE; break;
            case 3: orient.at(sit->first)=placerDB::FW; break;
            default:orient.at(sit->first)=placerDB::E;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::E; orient.at(pit->second)=placerDB::FE; break;
            case 1: orient.at(pit->first)=placerDB::W; orient.at(pit->second)=placerDB::FW; break;
            case 2: orient.at(pit->first)=placerDB::FE;orient.at(pit->second)=placerDB::E; break;
            case 3: orient.at(pit->first)=placerDB::FW;orient.at(pit->second)=placerDB::W; break;
            default:orient.at(pit->first)=placerDB::E; orient.at(pit->second)=placerDB::FE;
          }
        }
      }
    } else if (self_axis==placerDB::V && new_axis==placerDB::H) {
    // selfsym axis V	new axis H	N/S/FN/FS-FS/FN/S/N	N/S/FN/FS
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::N; break;
            case 1: orient.at(sit->first)=placerDB::S; break;
            case 2: orient.at(sit->first)=placerDB::FN; break;
            case 3: orient.at(sit->first)=placerDB::FS; break;
            default:orient.at(sit->first)=placerDB::N;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N; orient.at(pit->second)=placerDB::FS; break;
            case 1: orient.at(pit->first)=placerDB::S; orient.at(pit->second)=placerDB::FN; break;
            case 2: orient.at(pit->first)=placerDB::FN;orient.at(pit->second)=placerDB::S; break;
            case 3: orient.at(pit->first)=placerDB::FS;orient.at(pit->second)=placerDB::N; break;
            default:orient.at(pit->first)=placerDB::N; orient.at(pit->second)=placerDB::FS;
          }
        }
      }
    } else if (self_axis==placerDB::H && new_axis==placerDB::H) {
    // 			new axis H	E/W/FE/FW-FW/FE/W/E	E/W/FE/FW
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::E; break;
            case 1: orient.at(sit->first)=placerDB::W; break;
            case 2: orient.at(sit->first)=placerDB::FE; break;
            case 3: orient.at(sit->first)=placerDB::FW; break;
            default:orient.at(sit->first)=placerDB::E;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::E; orient.at(pit->second)=placerDB::FW; break;
            case 1: orient.at(pit->first)=placerDB::W; orient.at(pit->second)=placerDB::FE; break;
            case 2: orient.at(pit->first)=placerDB::FE;orient.at(pit->second)=placerDB::W; break;
            case 3: orient.at(pit->first)=placerDB::FW;orient.at(pit->second)=placerDB::E; break;
            default:orient.at(pit->first)=placerDB::E; orient.at(pit->second)=placerDB::FW;
          }
        }
      }
    } else if (self_axis==placerDB::H && new_axis==placerDB::V) {
    // selfsym axis H	new axis V	N/S/FN/FS-FN/FS/N/S	N/S/FN/FS
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(sgid).selfsym.begin(); sit!=caseNL.SBlocks.at(sgid).selfsym.end(); ++sit) {
        if(sit->first<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand() % 4;
          switch(sa) {
            case 0: orient.at(sit->first)=placerDB::N; break;
            case 1: orient.at(sit->first)=placerDB::S; break;
            case 2: orient.at(sit->first)=placerDB::FN; break;
            case 3: orient.at(sit->first)=placerDB::FS; break;
            default:orient.at(sit->first)=placerDB::N;
          }
        }
      }
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
          int sa=rand()%4;
          switch(sa) {
            case 0: orient.at(pit->first)=placerDB::N; orient.at(pit->second)=placerDB::FN; break;
            case 1: orient.at(pit->first)=placerDB::S; orient.at(pit->second)=placerDB::FS; break;
            case 2: orient.at(pit->first)=placerDB::FN;orient.at(pit->second)=placerDB::N; break;
            case 3: orient.at(pit->first)=placerDB::FS;orient.at(pit->second)=placerDB::S; break;
            default:orient.at(pit->first)=placerDB::N; orient.at(pit->second)=placerDB::FN;
          }
        }
      }
    }
  }
  // Reverse order of symmetry group in negative sequence
  vector<int> Slist=caseNL.GetRealBlockPlusAxisListfromSymmGroup(sgid);
  vector<int> Spos=GetVerticesIndexinSeq(this->negPair, Slist);
  vector<int> newNP=this->negPair;
  int Slength=(int)Spos.size();
  for(int i=0;i<Slength;++i) {
    newNP.at(Spos.at(i))=this->negPair.at(Spos.at(Slength-1-i));
  }
  this->negPair=newNP;
  return true;
}
