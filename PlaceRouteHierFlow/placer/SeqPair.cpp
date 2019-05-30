#include "SeqPair.h"

SeqPair::SeqPair() {
  this->posPair.clear();
  this->negPair.clear();
  this->orient.clear();
  this->symAxis.clear();
}

SeqPair::SeqPair(int blockSize) {
// For testing
  for(int i=0;i<blockSize;i++) {
    posPair.push_back(i);
    negPair.push_back(i);
    orient.push_back(placerDB::N);
  }
}

SeqPair::SeqPair(string pos, string neg) {
// For testing
  vector<string> temp1=split_by_spaces(pos);
  vector<string> temp2=split_by_spaces(neg);
  for(vector<string>::iterator it=temp1.begin(); it!=temp1.end()-1; ++it) {
    posPair.push_back(stoi(*it));
  }
  for(vector<string>::iterator it=temp2.begin(); it!=temp2.end()-1; ++it) {
    negPair.push_back(stoi(*it));
  }
  for(int i=0;i<(int)posPair.size();++i) {orient.push_back(placerDB::N);}
}

SeqPair::SeqPair(const SeqPair& sp) {
  this->posPair=sp.posPair;
  this->negPair=sp.negPair;
  this->orient=sp.orient;
  this->symAxis=sp.symAxis;
}

SeqPair::SeqPair(design& caseNL) {
  placerDB::Smark axis;
  orient.resize(caseNL.GetSizeofBlocks());
  for(vector<placerDB::SymmBlock>::iterator bit=caseNL.SBlocks.begin(); bit!=caseNL.SBlocks.end(); ++bit) {
    axis=placerDB::V; // initialize veritcal symmetry
    if ( !(bit->selfsym).empty() ) {
      switch( (bit->selfsym).at(0).second ) {
        case placerDB::H: axis=placerDB::V;break;
        case placerDB::V: axis=placerDB::H;break;
      }
    }
    //cout<<"axis"<<axis<<endl;
    symAxis.push_back(axis);
    // axis==V: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - a1,...,ap, cs,...,c1, axis, bp,...,b1
    // axis==H: positive - a1,...,ap, axis, c1,...,cs, bp,...,b1
    //          negative - b1,...,bp, axis, c1,...,cs, ap,...,a1
    if(!bit->sympair.empty()) {
      for(vector< pair<int,int> >::iterator pit=bit->sympair.begin(); pit!=bit->sympair.end(); ++pit) {
        if( pit->first<(int)caseNL.GetSizeofBlocks() ) {
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
      for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
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
        for(vector< pair<int,placerDB::Smark> >::iterator sit=bit->selfsym.end()-1; sit>=bit->selfsym.begin(); --sit) {
          if ( sit->first<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(sit->first); // cs,...c1 --> negative
          }
        }
      }
      negPair.push_back(bit->dnode); // axis --> negative
      if (!bit->sympair.empty()) {
        for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
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
        for(vector< pair<int,int> >::iterator pit=bit->sympair.end()-1; pit>=bit->sympair.begin(); --pit) {
          if( pit->first<(int)caseNL.GetSizeofBlocks() ) {
            negPair.push_back(pit->first); // ap,...,a1 --> negative
          }
        }
      }
    }
  }
  for(int i=0;i<caseNL.GetSizeofBlocks();i++) {
    if(caseNL.GetBlockSymmGroup(i)==-1) {
      posPair.push_back(i);
      negPair.push_back(i);
      orient.at(i)=placerDB::N;
    }
  }
} 

SeqPair& SeqPair::operator=(const SeqPair& sp) {
  this->posPair=sp.posPair;
  this->negPair=sp.negPair;
  this->orient=sp.orient;
  this->symAxis=sp.symAxis;
  return *this;
}

void SeqPair::PrintSeqPair() {
  cout<<endl<<"=== Sequence Pair ==="<<endl;
  cout<<"Positive pair: ";
  for(int i=0;i<(int)posPair.size();i++) {
    cout<<posPair.at(i)<<" ";
  }
  cout<<endl;
  cout<<"Negative pair: ";
  for(int i=0;i<(int)negPair.size();i++) {
    cout<<negPair.at(i)<<" ";
  }
  cout<<endl;
  cout<<"Orientation: ";
  for(int i=0;i<(int)orient.size();i++) {
    cout<<orient.at(i)<<" ";
  }
  cout<<endl;
  cout<<"Symmetry axis: ";
  for(int i=0;i<(int)symAxis.size();i++) {
    if(symAxis.at(i)==0) {cout<<"H ";
    } else {cout<<"V ";}
  }
  cout<<endl;
}

vector<int> SeqPair::GetBlockIndex(int blockNo) {
  vector<int> blockIdx;
  for(int i=0;i<(int)posPair.size();i++) {
    if(posPair.at(i)==blockNo) {blockIdx.push_back(i);break;}
  }
  for(int i=0;i<(int)negPair.size();i++) {
    if(negPair.at(i)==blockNo) {blockIdx.push_back(i);break;}
  }
  return(blockIdx);
}

vector<int> SeqPair::GetRightBlock(int blockNo) {
  vector<int> blockIdx=GetBlockIndex(blockNo);
  vector<int> Rblock;
  for(int i=blockIdx.at(0)+1;i<(int)posPair.size();i++) {
    for(int j=blockIdx.at(1)+1;j<(int)negPair.size();j++) {
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
  for(int i=0; i<blockIdx.at(0); i++) {
    for(int j=0; j<blockIdx.at(1); j++) {
      if(posPair.at(i)==negPair.at(j)) {Lblock.push_back(posPair.at(i));break;}
    }
  }
  return(Lblock);
}

vector<int> SeqPair::GetAboveBlock(int blockNo) {
  vector<int> blockIdx=GetBlockIndex(blockNo);
  vector<int> Ablock;
  for(int i=0; i<blockIdx.at(0); i++) {
    for(int j=blockIdx.at(1)+1;j<(int)negPair.size();j++) {
      if(posPair.at(i)==negPair.at(j)) {Ablock.push_back(posPair.at(i));break;}
    }
  }
  return(Ablock);
}

vector<int> SeqPair::GetBelowBlock(int blockNo) {
  vector<int> blockIdx=GetBlockIndex(blockNo);
  vector<int> Bblock;
  for(int i=blockIdx.at(0)+1;i<(int)posPair.size();i++) {
    for(int j=0; j<blockIdx.at(1); j++) {
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
    case placerDB::N: if(ort==placerDB::N or ort==placerDB::S or ort==placerDB::FN or ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::S: if(ort==placerDB::N or ort==placerDB::S or ort==placerDB::FN or ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::FN:if(ort==placerDB::N or ort==placerDB::S or ort==placerDB::FN or ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::FS:if(ort==placerDB::N or ort==placerDB::S or ort==placerDB::FN or ort==placerDB::FS)  orient.at(blockNo)=ort; 
            break;
    case placerDB::E: if(ort==placerDB::E or ort==placerDB::W or ort==placerDB::FE or ort==placerDB::FW)  orient.at(blockNo)=ort;
            break;
    case placerDB::W: if(ort==placerDB::E or ort==placerDB::W or ort==placerDB::FE or ort==placerDB::FW)  orient.at(blockNo)=ort;
            break;
    case placerDB::FE:if(ort==placerDB::E or ort==placerDB::W or ort==placerDB::FE or ort==placerDB::FW)  orient.at(blockNo)=ort;
            break;
    case placerDB::FW:if(ort==placerDB::E or ort==placerDB::W or ort==placerDB::FE or ort==placerDB::FW)  orient.at(blockNo)=ort;
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
  for(int i=0;i<(int)seq.size(); i++) {
    if(seq.at(i)==v) {idx=i; break;}
  }
  return idx;
}

bool SeqPair::FastInitialScan(design& caseNL) {
// return true if any violation found, otherwise return false
// Current feature: only support scan of symmetry constraints
// Future supports: will support scan of general placement constraints
  bool mark=true;
  for(int b=0; b<(int)caseNL.GetSizeofSBlocks() and mark ; b++) {
    // for each symmetry group
    placerDB::Smark axis=symAxis.at(b);
    vector<int> posQ=FindShortSeq(caseNL, posPair, b);
    vector<int> negQ=FindShortSeq(caseNL, negPair, b);
    for(int i=0; i<(int)posQ.size() and mark ; i++) {
      for(int j=i+1; j<(int)posQ.size() and mark ; j++) { 
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
    for(int i=0; i<(int)negQ.size() and mark; i++) {
      for(int j=i+1; j<(int)negQ.size() and mark ; j++) {
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

void SeqPair::Perturbation(design& caseNL) {
  /* initialize random seed: */
  //srand(time(NULL));
  int choice;
  bool mark=false;
  //cout<<"Perturbation?"<<endl;
  while(!mark) {
    if(!caseNL.designHasAsymBlock() and caseNL.GetSymGroupSize()==1 ) {
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
  //cout<<"Swap symmetry group "<<sgA<<" and "<<sgB<<endl;
  vector<int> Alist=caseNL.GetRealBlockPlusAxisListfromSymmGroup(sgA);
  vector<int> Blist=caseNL.GetRealBlockPlusAxisListfromSymmGroup(sgB);
  this->posPair=SwapTwoListinSeq(Alist, Blist, this->posPair);
  this->negPair=SwapTwoListinSeq(Alist, Blist, this->negPair);
  return true;
}

vector<int> SeqPair::GetVerticesIndexinSeq(vector<int>& seq, vector<int>& L) {
  vector<int> idx;
  for(int i=0;i<(int)seq.size();i++) {
    for(vector<int>::iterator it=L.begin(); it!=L.end(); ++it) {
      if(seq.at(i)==*it) {idx.push_back(i);break;}
    }
  }
  return idx;
}

vector<int> SeqPair::SwapTwoListinSeq(vector<int>& Alist, vector<int>& Blist, vector<int>& seq) {
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
    for(int i=0;i<(int)Apos.size();i++) {
      newseq.at(Apos.at(i))=seq.at(Bpos.at(i)); // B --> A
      newseq.at(Bpos.at(i))=seq.at(Apos.at(i)); // A --> B
    }
  } else if (Apos.size()<Bpos.size()) {
    for(int i=0;i<(int)Apos.size();i++)
      newseq.at(Bpos.at(i))=seq.at(Apos.at(i)); // A --> B
    // Merge sort to create new Apos list
    vector<int> newApos;
    vector<int>::iterator ait=Apos.begin();
    vector<int>::iterator bit=Bpos.begin()+Apos.size();
    while(ait!=Apos.end() and bit!=Bpos.end()) {
      if( (*ait)<(*bit) ) {
        newApos.push_back(*ait); ++ait;
      } else if ( (*ait)>(*bit) ) {
        newApos.push_back(*bit); ++bit;
      } else {
        cerr<<"Placer-Error: same index for different lists!"<<endl;
      }
    }
    while(ait!=Apos.end()) { newApos.push_back(*ait); ++ait; }
    while(bit!=Bpos.end()) { newApos.push_back(*bit); ++bit; }
    for(int i=0;i<(int)Bpos.size();i++)
      newseq.at(newApos.at(i))=seq.at(Bpos.at(i)); // B--> A
  } else {
    for(int i=0;i<(int)Bpos.size();i++)
      newseq.at(Apos.at(i))=seq.at(Bpos.at(i)); // B --> A
    // Merge sort to create new Bpos list
    vector<int> newBpos;
    vector<int>::iterator ait=Apos.begin()+Bpos.size();
    vector<int>::iterator bit=Bpos.begin();
    while(ait!=Apos.end() and bit!=Bpos.end()) {
      if( (*ait)<(*bit) ) {
        newBpos.push_back(*ait); ++ait;
      } else if ( (*ait)>(*bit) ) {
        newBpos.push_back(*bit); ++bit;
      } else {
        cerr<<"Placer-Error: same index for different lists!"<<endl;
      }
    }
    while(ait!=Apos.end()) { newBpos.push_back(*ait); ++ait; }
    while(bit!=Bpos.end()) { newBpos.push_back(*bit); ++bit; }
    for(int i=0;i<(int)Apos.size();i++)
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
  vector<int> blist=caseNL.GetRealBlockListfromSymmGroup(sgid); // all real blocks in symmetry group
  //cout<<"blist size: "<<blist.size()<<endl;
  if(blist.empty() or (int)blist.size()==1) {return false;}
  if((int)blist.size()==2 and blist.at(0)==caseNL.GetBlockCounterpart(blist.at(1))) {return false;}
  int A=blist.at( rand() % (int)blist.size() );
  //while(A>=(int)caseNL.GetSizeofBlocks()) {
  //   A=blist.at( rand() % (int)blist.size() );
  //}
  int symA=caseNL.GetBlockCounterpart(A);
  int B=blist.at( rand() % (int)blist.size() );
  while(B==A or B==symA)  {
    B=blist.at( rand() % (int)blist.size() );
  }
  //while(B==A or B==symA or B>=(int)caseNL.GetSizeofBlocks() )  {
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
  vector<int> blist=caseNL.GetRealBlockListfromSymmGroup(sgid); // all real blocks in symmetry group
  //cout<<"blist size: "<<blist.size()<<endl;
  if(blist.empty() or (int)blist.size()==1) {return false;}
  if((int)blist.size()==2 and blist.at(0)==caseNL.GetBlockCounterpart(blist.at(1))) {return false;}
  for(int i=0;i<count;i++) {
    int A=blist.at( rand() % (int)blist.size() );
    //while(A>=(int)caseNL.GetSizeofBlocks()) {
    //   A=blist.at( rand() % (int)blist.size() );
    //}
    int symA=caseNL.GetBlockCounterpart(A);
    int B=blist.at( rand() % (int)blist.size() );
    while(B==A or B==symA)  {
      B=blist.at( rand() % (int)blist.size() );
    }
    //while(B==A or B==symA or B>=(int)caseNL.GetSizeofBlocks() )  {
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
    for(int i=0;i<oldpos;i++) 
      newseq.at(i)=seq.at(i);
    for(int i=oldpos+1;i<=newpos;i++) 
      newseq.at(i-1)=seq.at(i);
    for(int i=newpos+1;i<(int)seq.size();i++)
      newseq.at(i)=seq.at(i);
    newseq.at(newpos)=seq.at(oldpos);
  } else if (oldpos>newpos) {
    for(int i=0;i<newpos;i++)
      newseq.at(i)=seq.at(i);
    newseq.at(newpos)=seq.at(oldpos);
    for(int i=newpos+1;i<=oldpos;i++)
      newseq.at(i)=seq.at(i-1);
    for(int i=oldpos+1;i<(int)seq.size();i++)
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
  bool mark=false;
  placerDB::Omark curr_ort=orient.at(anode);
  placerDB::Omark ort;
  //cout<<endl<<"Change orientation of asymmetric block "<<anode<<endl;
  // Currently we try to keep the orientation for fin alignment
  // and prevent to change the orientation arbitrarily
  while(!mark) {
    ort=placerDB::Omark( rand() % 8 );
    switch(curr_ort) {
      case placerDB::N: if(ort==placerDB::S or ort==placerDB::FN or ort==placerDB::FS)  {orient.at(anode)=ort;mark=true; }
              break;
      case placerDB::S: if(ort==placerDB::N or ort==placerDB::FN or ort==placerDB::FS)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FN:if(ort==placerDB::N or ort==placerDB::S  or ort==placerDB::FS)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FS:if(ort==placerDB::N or ort==placerDB::S  or ort==placerDB::FN)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::E: if(ort==placerDB::W or ort==placerDB::FE or ort==placerDB::FW)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::W: if(ort==placerDB::E or ort==placerDB::FE or ort==placerDB::FW)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FE:if(ort==placerDB::E or ort==placerDB::W  or ort==placerDB::FW)  {orient.at(anode)=ort;mark=true; }
              break;                                                             
      case placerDB::FW:if(ort==placerDB::E or ort==placerDB::W  or ort==placerDB::FE)  {orient.at(anode)=ort;mark=true; }
              break;
      default:break;
    }
  }
  return mark;
}

bool SeqPair::ChangeSymmetryBlockOrient(design& caseNL) {
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
  vector<int> Blist=caseNL.GetRealBlockListfromSymmGroup(sgid);
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
    if(self_axis==placerDB::V and new_axis==placerDB::V) {
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
    } else if (self_axis==placerDB::V and new_axis==placerDB::H) {
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
    } else if (self_axis==placerDB::H and new_axis==placerDB::H) {
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
    } else if (self_axis==placerDB::H and new_axis==placerDB::V) {
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
  placerDB::Smark new_axis, self_axis;
  new_axis=symAxis.at(sgid);
  // Change orientation of cells in symmetry group
  if(caseNL.SBlocks.at(sgid).selfsym.empty()) {
    //			sympair-sympair
    // 	new axis V	N/S/E/W/FN/FS/FE/FW-FN/FS/FE/FW/N/S/E/W
    // 	new axis H	N/S/E/W/FN/FS/FE/FW-FS/FN/FW/FE/S/N/W/E
    if(new_axis==placerDB::V) {
      for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(sgid).sympair.begin(); pit!=caseNL.SBlocks.at(sgid).sympair.end(); ++pit) {
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    if(self_axis==placerDB::V and new_axis==placerDB::V) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    } else if (self_axis==placerDB::V and new_axis==placerDB::H) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    } else if (self_axis==placerDB::H and new_axis==placerDB::H) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    } else if (self_axis==placerDB::H and new_axis==placerDB::V) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    if(self_axis==placerDB::V and new_axis==placerDB::V) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    } else if (self_axis==placerDB::V and new_axis==placerDB::H) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    } else if (self_axis==placerDB::H and new_axis==placerDB::H) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
    } else if (self_axis==placerDB::H and new_axis==placerDB::V) {
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
        if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
  for(int i=0;i<Slength;i++) {
    newNP.at(Spos.at(i))=this->negPair.at(Spos.at(Slength-1-i));
  }
  this->negPair=newNP;
  return true;
}
