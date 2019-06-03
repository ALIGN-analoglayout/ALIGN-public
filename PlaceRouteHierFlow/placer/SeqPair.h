#ifndef SEQPAIR_h_
#define SEQPAIR_h_

#include <vector>
#include <utility>
#include <string>
#include <iostream>
#include <stdlib.h>     /* srand, rand */
#include "../PnRDB/readfile.h"
#include "Pdatatype.h"
#include "design.h"

using std::vector;
using std::pair;
using std::make_pair;
using std::string;
using std::cout;
using std::cerr;
using std::endl;

class SeqPair 
{
  private:
    vector<int> posPair;
    vector<int> negPair;
    vector<placerDB::Omark> orient;
    vector<placerDB::Smark> symAxis;
    vector<int> FindShortSeq(design& caseNL, vector<int>& seq, int idx);
    int GetVertexIndexinSeq(vector<int>& seq, int v);
    bool MoveAsymmetricBlockUnit(design& caseNL, vector<int>& seq, int anode);
    vector<int> GetVerticesIndexinSeq(vector<int>& seq, vector<int>& L);
    vector<int> SwapTwoListinSeq(vector<int>& Alist, vector<int>& Blist, vector<int>& seq);

  public:
    SeqPair();
    SeqPair(int blockSize);
    SeqPair(string pos, string neg);
    SeqPair(const SeqPair& sp);
    SeqPair(design& caseNL);
    SeqPair& operator=(const SeqPair& sp);
    vector<int> GetBlockIndex(int blockNo);
    vector<int> GetRightBlock(int blockNo);
    vector<int> GetLeftBlock(int blockNo);
    vector<int> GetAboveBlock(int blockNo);
    vector<int> GetBelowBlock(int blockNo);
    placerDB::Omark GetBlockOrient(int blockNo);
    void PrintSeqPair();
    void ChangeOrient(int blockNo, placerDB::Omark ort );
    void FlipOrient(int blockNo);
    void AdjustOrient(int blockNo, placerDB::Omark ort);
    void SwitchSingleSequence(int b1, int b2, bool flag);
    void SwitchDoubleSequence(int b1, int b2);
    bool FastInitialScan(design& caseNL);
    placerDB::Smark GetSymmBlockAxis(int SBidx);
    bool MoveAsymmetricBlockposPair(design& caseNL);
    bool MoveAsymmetricBlocknegPair(design& caseNL);
    bool MoveAsymmetricBlockdoublePair(design& caseNL);
    bool SwapTwoBlocksofSameGroup(design& caseNL);
    bool SwapMultiBlocksofSameGroup(design& caseNL);
    bool SwapTwoSymmetryGroup(design& caseNL);
    bool ChangeAsymmetricBlockOrient(design& caseNL);
    bool RotateSymmetryGroup(design& caseNL);
    bool ChangeSymmetryGroupOrient(design& caseNL);
    bool ChangeSymmetryBlockOrient(design& caseNL);
    void Perturbation(design& caseNL);
    void TestSwap();
};

#endif
