#ifndef CONSTGRAPH_h_
#define CONSTGRAPH_h_

#include <cmath>
#include <utility>
#include <vector>
#include <stack>
#include <climits>
#include <string>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */
#include "Pdatatype.h"
#include "design.h"
#include "SeqPair.h"
#include "Aplace.h"
#include "ILP_solver.h"
#include "../PnRDB/datatype.h"
#include <nlohmann/json.hpp>
#include <Python.h>

using std::vector;
using std::string;
using std::cout;
using std::cin;
using std::cerr;
using std::stack;
using std::pair;
using std::make_pair;
using std::min;
using namespace nlohmann;
//using namespace std;
//using namespace placerDB;

#define NINF -9999999


class ConstGraph
{
  private:
    friend class ILP_solver;
    struct Event {
      int node;
      int corr;
      int type; // 0: high event; 1: low event
    };
    struct EventComp {
      bool operator() (const Event& lhs, const Event& rhs) const {
        if(lhs.corr==rhs.corr) {
          if(lhs.type==rhs.type) {
            return lhs.node<rhs.node;
          } else {
            return lhs.type<rhs.type;
          }
        } else {
          return lhs.corr<rhs.corr;
        }
      }
    };
    struct dataNode {
      int node;
      int corr;
    };
    struct dataNodeComp {
      bool operator() (const dataNode& lhs, const dataNode& rhs) const {
        if(lhs.corr==rhs.corr) {
          return lhs.node<rhs.node;
        } else {
          return lhs.corr<rhs.corr;
        }
      }
    };
    struct Edge {
      int next;
      int weight;
      bool isBackward;
    };
    struct Vertex {
      //int blockIdx;
      int weight;
      int position;
      int backpost;
      int precedent;
      int backprec;
      bool isSource;
      bool isSink;
      bool isVirtual;
      vector<Edge> Edges;
    };
    int origNodeSize;
    int sourceNode;
    int sinkNode;
    vector<Vertex> HGraph;
    vector<Vertex> VGraph;

    bool AddEdgeforVertex(int current, int next, int weight, vector<Vertex> &graph);
    //bool CheckOppositeEdge(int current, int next, vector<Vertex> &graph);
    //bool CheckRelatedForwardEdge(int current, int next, vector<Vertex> &graph);
    bool CheckForwardPath(int current, int next, vector<Vertex>& graph);
    void topologicalSortUtil(int v, bool visited[], stack<int> &Stack, vector<Vertex> &graph, bool backward );
    void CalculateLongestPath(int s, vector<Vertex> &graph, bool backward);
    int GetX(int i);
    int GetY(int i);
    double CalculatePenalty(vector<Vertex> &graph);
    double CalculateWireLengthRetire(design& caseNL, SeqPair& caseSP);
    double CalculateWireLength(design& caseNL, SeqPair& caseSP);
    double CalculateWireLengthAPRetire(design& caseNL, Aplace& caseAP);
    double CalculateWireLengthAP(design& caseNL, Aplace& caseAP);
    double CalculateArea();
    double CalculateRatio();
    double CalculateDeadArea(design& caseNL, SeqPair& caseSP);
    bool CheckPositiveCycle(vector<Vertex> &graph);
    vector<int> GenerateSlack(vector<int>& x);
    void UpdateLslackElement(design& caseNL, vector< pair<int,int> >& sympair, vector< pair<int,placerDB::Smark> >& selfsym, vector<int>& Lslack, vector<int>& xL, int j, placerDB::Smark axis);
    bool CheckIfLslackViolation(vector<int>& Lslack );
    bool CheckIfSingleL2Violation(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis);
    int CheckIfL2ViolationUnit(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, placerDB::Smark axis);
    pair<int,int> CheckIfL2Violation(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis);
    int CalculateBminusY(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis);
    int CalculateBminusXminusY(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis);
    void UpdatexLwithL3(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis);
    void AlignReorganize(design& caseNL, vector< pair<int,int> >& sympair, placerDB::Smark axis, int i);
    void InitializexL(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis, int i);
    PnRDB::bbox ConvertBoundaryData(vector<placerDB::point> Bdata);
    PnRDB::point ConvertPointData(placerDB::point Pdata);
    //void UpdateWeightforVertex(int current, int weight);
    void PlaneSweepBasic(design& caseNL, Aplace& caseAP, int mode, int bias_mode, int bias_graph);
    void PlaneSweepConstraint(design& caseNL, Aplace& caseAP, int mode, int bias_mode, int bias_graph);
    void InsetSetNode(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode);
    void InsetSetNodeConstraint(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode);
    void DeleteSetNode(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode, int bias_mode, int bias_graph);
    void DeleteSetNodeConstraint(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode, int bias_mode, int bias_graph);
    void ConstructGraphwithoutConstraint(design& caseNL, Aplace& caseAP, int bias_mode);
    void ConstructGraphwithConstraint(design& caseNL, Aplace& caseAP, int bias_mode);
    bool SymmetryConstraintCore(design& caseNL, placerDB::Smark axis, int i);
    bool SymmetryConstraintCoreAxisCenter(design& caseNL, placerDB::Smark axis, int i);
    void OtherGeometricConstraintCore(design& caseNL);
    void ReverseEdge(int current, int next, vector<Vertex>& graph);
    void UpdateBlockinHierNode(design& caseNL, placerDB::Omark ort, PnRDB::hierNode& node, int i, int sel, PnRDB::Drc_info& drcInfo);
    void UpdateTerminalinHierNode(design& caseNL, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
    void RemoveOverlapEdge(design& caseNL, Aplace& caseAP);
    bool RemoveEdgeforVertex(int current, int next, vector<Vertex> &graph, bool isBackward);
  public:
    static double LAMBDA;
    static double GAMAR;
    static double BETA;
    static double SIGMA;
    static double PHI;
    static double PI;
    static double PII;
    ConstGraph();
    ConstGraph(design& caseNL, SeqPair& caseSP);
    ConstGraph(design& caseNL, SeqPair& caseSP, int mode);
    ConstGraph(design& caseNL, Aplace& caseAP, int bias_mode, int mode);
    //ConstGraph(design& caseNL, Aplace& caseAP);
    ConstGraph(const ConstGraph &cg);
    ConstGraph& operator=(const ConstGraph &cg);
    void PrintConstGraph();
    void Test(design& caseNL, SeqPair& caseSP);
    bool ConstraintHorizontalDistance(int n1, int n2, int c1, int c2 );
    bool ConstraintVerticalDistance(int n1, int n2, int c1, int c2 );
    void Update_parameters(design& caseNL, SeqPair& caseSP);
    bool ConstraintVerticalOrder(int below, int above);
    bool ConstraintHorizontalOrder(int left, int right);
    bool ConstraintGraph(design& caseNL, SeqPair& caseSP);
    bool ConstraintGraphAP(design& caseNL, Aplace& caseAP);
    double CalculateCost(design& caseNL, SeqPair& caseSP);
    double performance_fom(double curr_cost, design& caseNL, SeqPair& caseSP, PyObject *pFun_cal_fom, PyObject *sess, PyObject *X, PyObject *pred_op);
    double CalculateMatchCost(design& caseNL, SeqPair& caseSP);
    void updateTerminalCenterRetire(design& caseNL, SeqPair& caseSP);
    void updateTerminalCenter(design& caseNL, SeqPair& caseSP);
    void updateTerminalCenterAPRetire(design& caseNL, Aplace& caseAP);
    void updateTerminalCenterAP(design& caseNL, Aplace& caseAP);
    void WritePlacement(design& caseNL, SeqPair& caseSP, string outfile);
    void PlotPlacement(design& caseNL, SeqPair& caseSP, string outfile, bool plot_pin, bool plot_terminal, bool plot_net);
    void WritePlacementAP(design& caseNL, Aplace& caseAP, string outfile);
    void PlotPlacementAP(design& caseNL, Aplace& caseAP, string outfile);
    void UpdateHierNode(design& caseNL, SeqPair& caseSP, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
    void UpdateHierNodeAP(design& caseNL, Aplace& caseAP, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo);
    bool FastInitialScan();
    void AddLargePenalty();
    void UpdateDesignHierNode4AP(design& caseNL, design& reducedNL, SeqPair& reducedSP, PnRDB::hierNode& node);
    void UpdateSymmetryNetInfo(design& caseNL, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir);
    double LinearConst(design& caseNL, SeqPair& caseSP);
    double ML_LinearConst(design& caseNL, SeqPair& caseSP);
    void ExtractLength(design& caseNL, SeqPair& caseSP, std::vector<std::vector<double> > &feature_value, std::vector<std::vector<std::string> > &feature_name);
    std::vector<double> Calculate_Center_Point_feature(std::vector<std::vector<placerDB::point> > &temp_contact);
};

#endif
