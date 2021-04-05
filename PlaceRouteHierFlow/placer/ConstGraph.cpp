#include "ConstGraph.h"
#include "spdlog/spdlog.h"

//added by yg
//int bias_flag=0;
//int bias_graph=0;

//int LAMBDA=1000;
//int GAMAR=30;
//int BETA=100;
 
//
bool ConstGraph::RemoveEdgeforVertex(int current, int next, vector<Vertex> &graph, bool isBackward) {
// only remove the first matched edge
  if(current<0 or current>=(int)graph.size() or next<0 or next>=(int)graph.size() ) {return false;}
  bool mark=false;
  int iN=0;
  for(std::vector<Edge>::iterator it=graph.at(current).Edges.begin(); it!=graph.at(current).Edges.end(); ++it,++iN) {
    if(it->isBackward==isBackward && it->next==next) {mark=true; break;}
  }
  if(mark) { graph.at(current).Edges.erase(graph.at(current).Edges.begin()+iN); }
  return mark;
}

void ConstGraph::RemoveOverlapEdge(design& caseNL, Aplace& caseAP) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.RemoveOverlapEdge");

  int ix, iX, jx, jX, iy, iY, jy, jY, xOL, yOL;
  for(int i=0;i<caseNL.GetSizeofBlocks();i++) {
    ix=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth( i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i) )/2;
    iy=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i) )/2;
    iX=caseAP.GetBlockCenter(i).x+caseNL.GetBlockWidth( i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i) )/2;
    iY=caseAP.GetBlockCenter(i).y+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i) )/2;
    for(int j=i+1;j<caseNL.GetSizeofBlocks();j++) {
      jx=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth( j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j) )/2;
      jy=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j) )/2;
      jX=caseAP.GetBlockCenter(j).x+caseNL.GetBlockWidth( j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j) )/2;
      jY=caseAP.GetBlockCenter(j).y+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j) )/2;
      xOL=std::max(std::min(std::min(iX-jx, jX-ix), std::min(iX-ix, jX-jx)), 0);
      yOL=std::max(std::min(std::min(iY-jy, jY-iy), std::min(iY-iy, jY-jy)), 0);
      if(xOL>0 && yOL>0) {
        logger->debug(" overlap with {0}",j);
        if(xOL>yOL) {
          RemoveEdgeforVertex(i, j, this->HGraph, false);
          RemoveEdgeforVertex(j, i, this->HGraph, false);
        } else {
          RemoveEdgeforVertex(i, j, this->VGraph, false);
          RemoveEdgeforVertex(j, i, this->VGraph, false);
        }
      }
    }
  }
}

ConstGraph::ConstGraph(design& caseNL, Aplace& caseAP, int bias_mode, int mode) {
// BiasMode 0: graph bias; Others: no bias
// Mode 0: create unconstrained graph for LP; others: create constrained graph
  if(mode==0) {
    ConstructGraphwithoutConstraint(caseNL, caseAP, bias_mode);
  } else {
    ConstructGraphwithConstraint(caseNL, caseAP, bias_mode);
  }
}

void ConstGraph::ConstructGraphwithoutConstraint(design& caseNL, Aplace& caseAP, int bias_mode) {
  HGraph.resize(caseNL.GetSizeofBlocks());
  VGraph.resize(caseNL.GetSizeofBlocks());
  origNodeSize=(int)HGraph.size();
  for(unsigned int i=0;i<HGraph.size();i++) {
    HGraph.at(i).weight=caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i));
    HGraph.at(i).isSource=false;
    HGraph.at(i).isSink=false;
    HGraph.at(i).isVirtual=false;
  } // Initialize real blocks in horizontal graph
  for(unsigned int i=0;i<VGraph.size();i++) {
    VGraph.at(i).weight=caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i));
    VGraph.at(i).isSource=false;
    VGraph.at(i).isSink=false;
    VGraph.at(i).isVirtual=false;
  } // Initialize real blocks in vertical graph
  // Add source node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=true;
  HGraph.back().isSink=false;
  HGraph.back().isVirtual=true;
  sourceNode=(int)HGraph.size()-1;
  // Add sink node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=false;
  HGraph.back().isSink=true;
  HGraph.back().isVirtual=true;
  sinkNode=(int)HGraph.size()-1;
  // Add source node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=true;
  VGraph.back().isSink=false;
  VGraph.back().isVirtual=true;
  // Add sink node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=false;
  VGraph.back().isSink=true;
  VGraph.back().isVirtual=true;
  // Add dummy nodes for symmetry constraints
  //for(int i=0;i<(int)caseNL.GetSizeofSBlocks();i++) {
  //  HGraph.resize(HGraph.size()+1);
  //  HGraph.back().weight=0;
  //  HGraph.back().isSource=false;
  //  HGraph.back().isSink=false;
  //  HGraph.back().isVirtual=true;
  //  VGraph.resize(VGraph.size()+1);
  //  VGraph.back().weight=0;
  //  VGraph.back().isSource=false;
  //  VGraph.back().isSink=false;
  //  VGraph.back().isVirtual=true;
  //}
  // temporary variables
  int bias_Vgraph = caseNL.bias_Vgraph;
  int bias_Hgraph = caseNL.bias_Hgraph;
  PlaneSweepBasic(caseNL, caseAP, 0, bias_mode, bias_Hgraph);
  PlaneSweepBasic(caseNL, caseAP, 1, bias_mode, bias_Vgraph);
}

void ConstGraph::ConstructGraphwithConstraint(design& caseNL, Aplace& caseAP, int bias_mode) {
  HGraph.resize(caseNL.GetSizeofBlocks());
  VGraph.resize(caseNL.GetSizeofBlocks());
  origNodeSize=(int)HGraph.size();
  for(unsigned int i=0;i<HGraph.size();i++) {
    HGraph.at(i).weight=caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i));
    HGraph.at(i).isSource=false;
    HGraph.at(i).isSink=false;
    HGraph.at(i).isVirtual=false;
  } // Initialize real blocks in horizontal graph
  for(unsigned int i=0;i<VGraph.size();i++) {
    VGraph.at(i).weight=caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i));
    VGraph.at(i).isSource=false;
    VGraph.at(i).isSink=false;
    VGraph.at(i).isVirtual=false;
  } // Initialize real blocks in vertical graph
  // Add source node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=true;
  HGraph.back().isSink=false;
  HGraph.back().isVirtual=true;
  sourceNode=(int)HGraph.size()-1;
  // Add sink node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=false;
  HGraph.back().isSink=true;
  HGraph.back().isVirtual=true;
  sinkNode=(int)HGraph.size()-1;
  // Add source node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=true;
  VGraph.back().isSink=false;
  VGraph.back().isVirtual=true;
  // Add sink node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=false;
  VGraph.back().isSink=true;
  VGraph.back().isVirtual=true;
  // Add dummy nodes for symmetry constraints
  for(int i=0;i<caseNL.GetSizeofSBlocks();i++) {
    HGraph.resize(HGraph.size()+1);
    HGraph.back().weight=0;
    HGraph.back().isSource=false;
    HGraph.back().isSink=false;
    HGraph.back().isVirtual=true;
    VGraph.resize(VGraph.size()+1);
    VGraph.back().weight=0;
    VGraph.back().isSource=false;
    VGraph.back().isSink=false;
    VGraph.back().isVirtual=true;
  }
  // temporary variables
  int bias_Vgraph = caseNL.bias_Vgraph;
  int bias_Hgraph = caseNL.bias_Hgraph;
  PlaneSweepConstraint(caseNL, caseAP, 0, bias_mode, bias_Hgraph);
  PlaneSweepConstraint(caseNL, caseAP, 1, bias_mode, bias_Vgraph);
  RemoveOverlapEdge(caseNL, caseAP);
  for(int i=0;i<(int)HGraph.size();i++) {
    if( i==sourceNode or i==sinkNode ) {continue;}
    if( !CheckForwardPath(sourceNode, i, HGraph) ) { // check path from source node
      if(i>=caseNL.GetSizeofBlocks()+2) {
        AddEdgeforVertex(sourceNode, i, HGraph.at(sourceNode).weight, this->HGraph);
      } else {
        if(bias_mode==0) {
          AddEdgeforVertex(sourceNode, i, HGraph.at(sourceNode).weight+bias_Hgraph, this->HGraph);
        } else {
          AddEdgeforVertex(sourceNode, i, HGraph.at(sourceNode).weight, this->HGraph);
        }
      }
    }
    if( !CheckForwardPath(i, sinkNode, HGraph) ) { // check path to sink node
      if(i>=caseNL.GetSizeofBlocks()+2) {
        AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight, this->HGraph);
      } else {
        if(bias_mode==0) {
          AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight+bias_Hgraph, this->HGraph);
        } else {
          AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight, this->HGraph);
        }
      }
    }
  }
  for(int i=0;i<(int)VGraph.size();i++) {
    if( i==sourceNode or i==sinkNode ) {continue;}
    if( !CheckForwardPath(sourceNode, i, VGraph) ) { // check path from source node
      if(i>=caseNL.GetSizeofBlocks()+2) {
        AddEdgeforVertex(sourceNode, i, VGraph.at(sourceNode).weight, this->VGraph);
      } else {
        if(bias_mode==0) {
          AddEdgeforVertex(sourceNode, i, VGraph.at(sourceNode).weight+bias_Vgraph, this->VGraph);
        } else {
          AddEdgeforVertex(sourceNode, i, VGraph.at(sourceNode).weight, this->VGraph);
        }
      }
    }
    if( !CheckForwardPath(i, sinkNode, VGraph) ) { // check path to sink node
      if(i>=caseNL.GetSizeofBlocks()+2) {
        AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight, this->VGraph);
      } else {
        if(bias_mode==0) {
          AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight+bias_Vgraph, this->VGraph);
        } else {
          AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight, this->VGraph);
        }
      }
    }
  }
}

void ConstGraph::PlaneSweepConstraint(design& caseNL, Aplace& caseAP, int mode, int bias_mode, int bias_graph) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.PlaneSweepConstraint");

 // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
 // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
  // Create scan tree
  Event tmpEvent;
  std::set<Event, EventComp> scanT;
  for(int i=0;i<caseNL.GetSizeofBlocks();i++) {
    tmpEvent.node=i;
    tmpEvent.type=0;
    if(mode==0) {
      tmpEvent.corr=caseAP.GetBlockCenter(i).y+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    } else {
      tmpEvent.corr=caseAP.GetBlockCenter(i).x+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    }
    scanT.insert(tmpEvent);
    tmpEvent.type=1;
    if(mode==0) {
      tmpEvent.corr=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    } else {
      tmpEvent.corr=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    }
    scanT.insert(tmpEvent);
  }
  // Limitation: for the event of symmetry axis, we set the width/height as 1
  // to make it follow the rule of event sorting
  for(int i=0;i<(int)caseNL.GetSizeofSBlocks();i++) {
    tmpEvent.node=caseNL.GetSizeofBlocks()+2+i;
    tmpEvent.type=0;
    if(mode==0) {
      if(caseAP.GetSBlockDir(i)==placerDB::V) {
        tmpEvent.corr=1;
      } else if(caseAP.GetSBlockDir(i)==placerDB::H) {
        tmpEvent.corr=caseAP.GetSBlockCorr(i)+1;
      }
    } else {
      if(caseAP.GetSBlockDir(i)==placerDB::V) {
        tmpEvent.corr=caseAP.GetSBlockCorr(i)+1;
      } else if(caseAP.GetSBlockDir(i)==placerDB::H) {
        tmpEvent.corr=1;
      }
    }
    scanT.insert(tmpEvent);
    tmpEvent.type=1;
    if(mode==0) {
      if(caseAP.GetSBlockDir(i)==placerDB::V) {
        tmpEvent.corr=0;
      } else if(caseAP.GetSBlockDir(i)==placerDB::H) {
        tmpEvent.corr=caseAP.GetSBlockCorr(i);
      }
    } else {
      if(caseAP.GetSBlockDir(i)==placerDB::V) {
        tmpEvent.corr=caseAP.GetSBlockCorr(i);
      } else if(caseAP.GetSBlockDir(i)==placerDB::H) {
        tmpEvent.corr=0;
      }
    }
    scanT.insert(tmpEvent);
  }

  // Search and add edges
  std::set<dataNode, dataNodeComp> setD;
  std::vector<int> cand(caseNL.GetSizeofBlocks()+2+caseNL.GetSizeofSBlocks(), -1);
  // Add source and sink node into setD
  dataNode tmpDnode;
  tmpDnode.node=this->sourceNode;
  tmpDnode.corr=0;
  setD.insert(tmpDnode);
  tmpDnode.node=this->sinkNode;
  if(mode==0) {
    tmpDnode.corr=caseAP.GetWidth();
  } else {
    tmpDnode.corr=caseAP.GetHeight();
  }
  setD.insert(tmpDnode);

  for(std::set<Event, EventComp>::iterator it=scanT.begin(); it!=scanT.end();++it) {
    logger->debug("@Event {0} node {1} corr {2}",it->type,it->node,it->corr);
    tmpDnode.node=it->node;
    if(mode==0) {
      if(it->node<caseNL.GetSizeofBlocks()) {
        tmpDnode.corr=caseAP.GetBlockCenter(it->node).x;
      } else {
        if(caseAP.GetSBlockDir(it->node-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
          tmpDnode.corr=caseAP.GetSBlockCorr(it->node-caseNL.GetSizeofBlocks()-2);
        } else {
          tmpDnode.corr=0;
        }
      }
    } else {
      if(it->node<caseNL.GetSizeofBlocks()) {
        tmpDnode.corr=caseAP.GetBlockCenter(it->node).y;
      } else {
        if(caseAP.GetSBlockDir(it->node-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
          tmpDnode.corr=0;
        } else {
          tmpDnode.corr=caseAP.GetSBlockCorr(it->node-caseNL.GetSizeofBlocks()-2);
        }
      }
    }
    logger->debug("work on node {0} {1}",tmpDnode.node,tmpDnode.corr);
    logger->debug("before delete/insert");
    if(it->type==0) { // high event
      DeleteSetNodeConstraint(caseNL, caseAP, setD, tmpDnode, cand, mode, bias_mode, bias_graph);
      //DeleteSetNode();
    } else if (it->type==1) { // low event
      InsetSetNodeConstraint(caseNL, caseAP, setD, tmpDnode, cand, mode);
      //InsetSetNode();
    }
    logger->debug("after delete/insert");
  }
}

void ConstGraph::PlaneSweepBasic(design& caseNL, Aplace& caseAP, int mode, int bias_mode, int bias_graph) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.PlaneSweepBasic");

 // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
 // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
  // Create scan tree
  Event tmpEvent;
  std::set<Event, EventComp> scanT;
  for(int i=0;i<caseNL.GetSizeofBlocks();i++) {
    tmpEvent.node=i;
    tmpEvent.type=0;
    if(mode==0) {
      tmpEvent.corr=caseAP.GetBlockCenter(i).y+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    } else {
      tmpEvent.corr=caseAP.GetBlockCenter(i).x+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    }
    scanT.insert(tmpEvent);
    tmpEvent.type=1;
    if(mode==0) {
      tmpEvent.corr=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    } else {
      tmpEvent.corr=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
    }
    scanT.insert(tmpEvent);
  }

  // Search and add edges
  std::set<dataNode, dataNodeComp> setD;
  std::vector<int> cand(caseNL.GetSizeofBlocks()+2, -1);
  // Add source and sink node into setD
  dataNode tmpDnode;
  tmpDnode.node=this->sourceNode;
  tmpDnode.corr=0;
  setD.insert(tmpDnode);
  tmpDnode.node=this->sinkNode;
  if(mode==0) {
    tmpDnode.corr=caseAP.GetWidth();
  } else {
    tmpDnode.corr=caseAP.GetHeight();
  }
  setD.insert(tmpDnode);

  for(std::set<Event, EventComp>::iterator it=scanT.begin(); it!=scanT.end();++it) {
    logger->debug("@Event {0} node {1} corr {2}",it->type,it->node,it->corr);
    tmpDnode.node=it->node;
    if(mode==0) {
      tmpDnode.corr=caseAP.GetBlockCenter(it->node).x;
    } else {
      tmpDnode.corr=caseAP.GetBlockCenter(it->node).y;
    }
    if(it->type==0) { // high event
      DeleteSetNode(caseNL, caseAP, setD, tmpDnode, cand, mode, bias_mode, bias_graph);
      //DeleteSetNode();
    } else if (it->type==1) { // low event
      InsetSetNode(caseNL, caseAP, setD, tmpDnode, cand, mode);
      //InsetSetNode();
    }
  }
}

void ConstGraph::DeleteSetNode(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode, int bias_mode, int bias_graph) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.DeleteSetNode");

 // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
 // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
  std::set<dataNode, dataNodeComp>::iterator setIt=setD.find(Dnode);
  std::set<dataNode, dataNodeComp>::iterator lit, rit;
  bool mark=false;
  for(lit=setIt; ; --lit) {
    if(lit==setIt){continue;}
    int i=Dnode.node,j=lit->node;
    if(mode==1) { // sort in y order, check overlap along x direction
      int xi,xj;
      if(j!=this->sourceNode) {
        xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
      } else { mark=true; break;}
    } else { // sort in x order, check overlap along y direction
      int yi,yj;
      if(j!=this->sourceNode) {
        yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;}
      } else {mark=true; break;}
    }
    if(lit==setD.begin()) {break;}
  }
  if(mark) {
    if(cand.at(lit->node)==Dnode.node) {
      if(mode==1) { // sort in y order, check overlap along x direction
        if(bias_mode==0) {
          AddEdgeforVertex(lit->node, Dnode.node, VGraph.at(lit->node).weight+bias_graph, this->VGraph);
        } else {
          AddEdgeforVertex(lit->node, Dnode.node, VGraph.at(lit->node).weight, this->VGraph);
        }
      } else { // sort in x order, check overlap along y direction
        if(bias_mode==0) {
          AddEdgeforVertex(lit->node, Dnode.node, HGraph.at(lit->node).weight+bias_graph, this->HGraph);
        } else {
          AddEdgeforVertex(lit->node, Dnode.node, HGraph.at(lit->node).weight, this->HGraph);
        }
      }
    }
    //cand(lit->node)=Dnode.node;
  } else {
    logger->debug("Placer-Error: cannot find left neighbor");
  }

  mark=false;
  for(rit=setIt;rit!=setD.end();++rit) {
    if(rit==setIt) {continue;}
    int i=Dnode.node, j=rit->node;
    if(mode==1) {// sort in y order, check overlap along x direction
      int xi,xj;
      if(j!=this->sinkNode) {
        xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
      } else { mark=true; break;}
    } else {// sort in x order, check overlap along y direction
      int yi,yj;
      if(j!=this->sinkNode) {
        yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;} 
      } else {mark=true; break;}
    }
  }
  if(mark) {
    if(cand.at(Dnode.node)==rit->node) {
      if(mode==1) { // sort in y order, check overlap along x direction
        if(bias_mode==0) {
          AddEdgeforVertex(Dnode.node, rit->node, VGraph.at(Dnode.node).weight+bias_graph, this->VGraph);
        } else {
          AddEdgeforVertex(Dnode.node, rit->node, VGraph.at(Dnode.node).weight, this->VGraph);
        }
      } else { // sort in x order, check overlap along y direction
        if(bias_mode==0) {
          AddEdgeforVertex(Dnode.node, rit->node, HGraph.at(Dnode.node).weight+bias_graph, this->HGraph);
        } else {
          AddEdgeforVertex(Dnode.node, rit->node, HGraph.at(Dnode.node).weight, this->HGraph);
        }
      }
    }
    //cand.at(Dnode.node)=rit->node;
  } else {
    logger->debug("Placer-Error: cannot find right neighbor");
  }
  setD.erase(setIt);
}

void ConstGraph::DeleteSetNodeConstraint(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode, int bias_mode, int bias_graph) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.DeleteSetNodeConstraint");

 // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
 // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
  std::set<dataNode, dataNodeComp>::iterator setIt=setD.find(Dnode);
  std::set<dataNode, dataNodeComp>::iterator lit, rit;
  bool mark=false;
  for(lit=setIt; ; --lit) {
    if(lit==setIt){continue;}
    int i=Dnode.node,j=lit->node;
    if(i<caseNL.GetSizeofBlocks()) {// current node is block
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sourceNode) {
          xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj>=xi && xj<=xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sourceNode) {
          yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj>=yi && yj<=yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    } else { // current node is virtual (symmetry axis)
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sourceNode) {
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            xi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          } else {
            xi=0;
          }
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(xi>=xj && xi<=xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj==xi) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sourceNode) {
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            yi=0;
          } else {
            yi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          }
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(yi>=yj && yi<=yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj==yi) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    }
    if(lit==setD.begin()) {break;}
  }
  if(mark) {
    if(cand.at(lit->node)==Dnode.node) {
      if(mode==1) { // sort in y order, check overlap along x direction
        if(lit->node>=caseNL.GetSizeofBlocks()+2 or Dnode.node>=caseNL.GetSizeofBlocks()+2 ) {
          AddEdgeforVertex(lit->node, Dnode.node, VGraph.at(lit->node).weight, this->VGraph);
        } else {
          if(bias_mode==0) {
            AddEdgeforVertex(lit->node, Dnode.node, VGraph.at(lit->node).weight+bias_graph, this->VGraph);
          } else {
            AddEdgeforVertex(lit->node, Dnode.node, VGraph.at(lit->node).weight, this->VGraph);
          }
        }
      } else { // sort in x order, check overlap along y direction
        if(lit->node>=caseNL.GetSizeofBlocks()+2 or Dnode.node>=caseNL.GetSizeofBlocks()+2 ) {
          AddEdgeforVertex(lit->node, Dnode.node, HGraph.at(lit->node).weight, this->HGraph);
        } else {
          if(bias_mode==0) {
            AddEdgeforVertex(lit->node, Dnode.node, HGraph.at(lit->node).weight+bias_graph, this->HGraph);
          } else {
            AddEdgeforVertex(lit->node, Dnode.node, HGraph.at(lit->node).weight, this->HGraph);
          }
        }
      }
    }
    //cand(lit->node)=Dnode.node;
  } else {
    logger->debug("Placer-Error: cannot find left neighbor");
  }

  mark=false;
  for(rit=setIt;rit!=setD.end();++rit) {
    if(rit==setIt) {continue;}
    int i=Dnode.node, j=rit->node;
    if(i<caseNL.GetSizeofBlocks()) {// current node is block
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sinkNode) {
          xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj>=xi && xj<=xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sinkNode) {
          yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj>=yi && yj<=yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    } else { // current node is virtual (symmetry axis)
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sinkNode) {
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            xi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          } else {
            xi=0;
          }
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(xi>=xj && xi<=xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj==xi) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sinkNode) {
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            yi=0;
          } else {
            yi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          }
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(yi>=yj && yi<=yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj==yi) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    }
  }
  if(mark) {
    if(cand.at(Dnode.node)==rit->node) {
      if(mode==1) { // sort in y order, check overlap along x direction
        if(Dnode.node>=caseNL.GetSizeofBlocks()+2 or rit->node>=caseNL.GetSizeofBlocks()+2) {
          AddEdgeforVertex(Dnode.node, rit->node, VGraph.at(Dnode.node).weight, this->VGraph);
        } else {
          if(bias_mode==0) {
            AddEdgeforVertex(Dnode.node, rit->node, VGraph.at(Dnode.node).weight+bias_graph, this->VGraph);
          } else {
            AddEdgeforVertex(Dnode.node, rit->node, VGraph.at(Dnode.node).weight, this->VGraph);
          }
        }
      } else { // sort in x order, check overlap along y direction
        if(Dnode.node>=caseNL.GetSizeofBlocks()+2 or rit->node>=caseNL.GetSizeofBlocks()+2) {
          AddEdgeforVertex(Dnode.node, rit->node, HGraph.at(Dnode.node).weight, this->HGraph);
        } else {
          if(bias_mode==0) {
            AddEdgeforVertex(Dnode.node, rit->node, HGraph.at(Dnode.node).weight+bias_graph, this->HGraph);
          } else {
            AddEdgeforVertex(Dnode.node, rit->node, HGraph.at(Dnode.node).weight, this->HGraph);
          }
        }
      }
    }
    //cand.at(Dnode.node)=rit->node;
  } else {
    logger->debug("Placer-Error: cannot find right neighbor");
  }
  setD.erase(setIt);
}

void ConstGraph::InsetSetNodeConstraint(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.InsetSetNodeConstraint");

 // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
 // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
  //std::cout<<"start of InsetSetNodeConstraint mode "<<mode<<std::endl;
  setD.insert(Dnode);
  for(std::set<dataNode, dataNodeComp>::iterator vi=setD.begin(); vi!=setD.end();++vi) {
    logger->debug("Nnode {0} @ {1}",vi->node,vi->corr);
  }
  std::set<dataNode, dataNodeComp>::iterator setIt=setD.find(Dnode);
  std::set<dataNode, dataNodeComp>::iterator lit, rit;
  bool mark=false;
  //std::cout<<"find left"<<std::endl;
  for(lit=setIt; ; --lit) {
    if(lit==setIt) {continue;}
    int i=Dnode.node,j=lit->node;
    //std::cout<<"check "<<i<<" vs "<<j<<std::endl;
    if(i<caseNL.GetSizeofBlocks()) {// current node is block
      logger->debug("real!");
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sourceNode) {
          xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj>=xi && xj<=xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sourceNode) {
          yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj>=yi && yj<=yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    } else { // current node is virtual (symmetry axis)
      logger->debug("virtual!");
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sourceNode) {
          //std::cout<<"check j?"<<std::endl;
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            xi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          } else {
            xi=0;
          }
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(xi>=xj && xi<=xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj==xi) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
         //std::cout<<"in mode 0"<<std::endl;
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sourceNode) {
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            yi=0;
          } else {
            yi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          }
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(yi>=yj && yi<=yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj==yi) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    }
    if(lit==setD.begin()) {break;}
  }
  if(mark) {
    cand.at(lit->node)=Dnode.node;
  } else {
    logger->debug("Placer-Error: cannot find left neighbor");
  }

  //std::cout<<"find right"<<std::endl;
  mark=false;
  for(rit=setIt;rit!=setD.end();++rit) {
    if(rit==setIt) {continue;}
    int i=Dnode.node, j=rit->node;
    //std::cout<<"check "<<i<<" vs "<<j<<std::endl;
    if(i<caseNL.GetSizeofBlocks()) {// current node is block
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sinkNode) {
          xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj>=xi && xj<=xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sinkNode) {
          yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj>=yi && yj<=yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    } else { // current node is virtual (symmetry axis)
      if(mode==1) {
        // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
        int xi,xj;
        if(j!=this->sinkNode) {
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            xi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          } else {
            xi=0;
          }
          if(j<caseNL.GetSizeofBlocks()) {
            xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(xi>=xj && xi<=xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              xj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            } else {
              xj=0;
            }
            if(xj==xi) {mark=true;break;}
          }
        } else { mark=true; break;}
      } else {
        // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
        int yi,yj;
        if(j!=this->sinkNode) {
          if(caseAP.GetSBlockDir(i-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
            yi=0;
          } else {
            yi=caseAP.GetSBlockCorr(i-caseNL.GetSizeofBlocks()-2);
          }
          if(j<caseNL.GetSizeofBlocks()) {
            yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
            if(yi>=yj && yi<=yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))) {mark=true;break;}
          } else {
            if(caseAP.GetSBlockDir(j-caseNL.GetSizeofBlocks()-2)==placerDB::V) {
              yj=0;
            } else {
              yj=caseAP.GetSBlockCorr(j-caseNL.GetSizeofBlocks()-2);
            }
            if(yj==yi) {mark=true;break;}
          }
        } else {mark=true; break;}
      }
    }
  }
  if(mark) {
    cand.at(Dnode.node)=rit->node;
  } else {
    logger->debug("Placer-Error: cannot find right neighbor");
  }
}

void ConstGraph::InsetSetNode(design& caseNL, Aplace& caseAP, std::set<dataNode, dataNodeComp>& setD, dataNode& Dnode, std::vector<int>& cand, int mode) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.InsetSetNode");

 // mode-0: horizontal graph, sort blocks in x direction, check overlap along y direction
 // mode-1: vertical graph, sort blocks in y direction, check overlap along x direction
  setD.insert(Dnode);
  std::set<dataNode, dataNodeComp>::iterator setIt=setD.find(Dnode);
  std::set<dataNode, dataNodeComp>::iterator lit, rit;
  bool mark=false;
  for(lit=setIt; ; --lit) {
    if(lit==setIt) {continue;}
    int i=Dnode.node,j=lit->node;
    if(mode==1) {
      int xi,xj;
      if(j!=this->sourceNode) {
        xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
      } else { mark=true; break;}
    } else {
      int yi,yj;
      if(j!=this->sourceNode) {
        yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;}
      } else {mark=true; break;}
    }
    if(lit==setD.begin()) {break;}
  }
  if(mark) {
    cand.at(lit->node)=Dnode.node;
  } else {
    logger->debug("Placer-Error: cannot find left neighbor");
  }

  mark=false;
  for(rit=setIt;rit!=setD.end();++rit) {
    if(rit==setIt) {continue;}
    int i=Dnode.node, j=rit->node;
    if(mode==1) {
      int xi,xj;
      if(j!=this->sinkNode) {
        xi=caseAP.GetBlockCenter(i).x-caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        xj=caseAP.GetBlockCenter(j).x-caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(xi+caseNL.GetBlockWidth(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-xj, xj+caseNL.GetBlockWidth(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-xi)>0) { mark=true; break;}
      } else { mark=true; break;}
    } else {
      int yi,yj;
      if(j!=this->sinkNode) {
        yi=caseAP.GetBlockCenter(i).y-caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))/2;
        yj=caseAP.GetBlockCenter(j).y-caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))/2;
        if(std::min(yi+caseNL.GetBlockHeight(i, caseAP.GetBlockOrient(i), caseAP.GetSelectedInstance(i))-yj, yj+caseNL.GetBlockHeight(j, caseAP.GetBlockOrient(j), caseAP.GetSelectedInstance(j))-yi)>0) { mark=true; break;} 
      } else {mark=true; break;}
    }
  }
  if(mark) {
    cand.at(Dnode.node)=rit->node;
  } else {
    logger->debug("Placer-Error: cannot find right neighbor");
  }
}

ConstGraph::ConstGraph(design& caseNL, SeqPair& caseSP, int mode) {
// Mode 0: graph bias; Mode 1: graph bias + net margin; Others: no bias/margin
  //LAMBDA=1000;
  //GAMAR=30;
  //BETA=100;
  //SIGMA = 1000;
  HGraph.resize(caseNL.GetSizeofBlocks());
  VGraph.resize(caseNL.GetSizeofBlocks());
  origNodeSize=(int)HGraph.size();
  for(int i=0;i<(int)HGraph.size();i++) {
    HGraph.at(i).weight=caseNL.GetBlockWidth(i, caseSP.GetBlockOrient(i), caseSP.GetBlockSelected(i));
    HGraph.at(i).isSource=false;
    HGraph.at(i).isSink=false;
    HGraph.at(i).isVirtual=false;
  } // Initialize real blocks in horizontal graph
  for(int i=0;i<(int)VGraph.size();i++) {
    VGraph.at(i).weight=caseNL.GetBlockHeight(i, caseSP.GetBlockOrient(i), caseSP.GetBlockSelected(i));
    VGraph.at(i).isSource=false;
    VGraph.at(i).isSink=false;
    VGraph.at(i).isVirtual=false;
  } // Initialize real blocks in vertical graph
  // Add source node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=true;
  HGraph.back().isSink=false;
  HGraph.back().isVirtual=true;
  sourceNode=(int)HGraph.size()-1;
  // Add sink node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=false;
  HGraph.back().isSink=true;
  HGraph.back().isVirtual=true;
  sinkNode=(int)HGraph.size()-1;
  // Add source node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=true;
  VGraph.back().isSink=false;
  VGraph.back().isVirtual=true;
  // Add sink node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=false;
  VGraph.back().isSink=true;
  VGraph.back().isVirtual=true;
  // Add dummy nodes for symmetry constraints
  for(int i=0;i<(int)caseNL.GetSizeofSBlocks();i++) {
    HGraph.resize(HGraph.size()+1);
    HGraph.back().weight=0;
    HGraph.back().isSource=false;
    HGraph.back().isSink=false;
    HGraph.back().isVirtual=true;
    VGraph.resize(VGraph.size()+1);
    VGraph.back().weight=0;
    VGraph.back().isSource=false;
    VGraph.back().isSink=false;
    VGraph.back().isVirtual=true;
  }
  // temporary variables
  vector<int> candidate;

int bias_Vgraph = caseNL.bias_Vgraph;
int bias_Hgraph = caseNL.bias_Hgraph;
/*
	//int bias=100;
    //int bias_graph;
//added by yg
	if(bias_flag==0){
	bias_graph=0;
	cout<<"bias_flag"<<" "<<bias_flag<<endl;
	cout<<"bias"<<" "<<bias_graph<<endl;
	srand(time(NULL));
	while(bias_graph<100){	
    bias_graph = (rand()%10) *50;
    }

  //write out bias
	fstream f("bias.const",ios::out);
	f<<"bias"<<" "<<bias_graph<<endl;
	f.close();
	bias_flag=1;
	cout<<"bias_flag"<<" "<<bias_flag<<endl;
	cout<<"bias_graph"<<" "<<bias_graph<<endl;
	
}
*/
  //cout<<"bias_graph_for_edge"<<bias_graph<<endl;
  // Add initial edges in horizontal graph
  for(int i=0;i<(int)HGraph.size();i++) {
    if(i==sourceNode or i==sinkNode) {continue;}
    // check blocks right to current block
    candidate.clear(); candidate=caseSP.GetRightBlock(i);
    for(vector<int>::iterator it=candidate.begin(); it!=candidate.end(); ++it) {
      //tmpE.weight=HGraph.at(i).weight;
      //tmpE.next=(*it);
      //HGraph.at(i).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks() && *it<caseNL.GetSizeofBlocks() ) {
        if(mode==0) {
          AddEdgeforVertex(i, *it, HGraph.at(i).weight+bias_Hgraph, this->HGraph);
        } else if (mode==1) {
          AddEdgeforVertex(i, *it, HGraph.at(i).weight+bias_Hgraph+caseNL.GetBlockMargin(i,*it), this->HGraph);
        } else {
          AddEdgeforVertex(i, *it, HGraph.at(i).weight, this->HGraph);
        }
      } else {
        AddEdgeforVertex(i, *it, HGraph.at(i).weight, this->HGraph);
      }
    } // add edges conncting blocks right to current one
    if(candidate.empty()) {
      //tmpE.weight=HGraph.at(i).weight;
      //tmpE.next=sinkNode;
      //HGraph.at(i).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
        if(mode==0 or mode==1) {
          AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight+bias_Hgraph, this->HGraph);
        } else {
          AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight, this->HGraph);
        }
      } else {
        AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight, this->HGraph);
      }
    } // if no right blocks, add edge to sink
    candidate.clear(); candidate=caseSP.GetLeftBlock(i);
    if(candidate.empty()) {
      //tmpE.weight=0;
      //tmpE.next=i;
      //HGraph.at(sourceNode).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
        if(mode==0 or mode==1) {
          AddEdgeforVertex(sourceNode, i, 0+bias_Hgraph, this->HGraph);
        } else {
          AddEdgeforVertex(sourceNode, i, 0, this->HGraph);
        }
      } else {
        AddEdgeforVertex(sourceNode, i, 0, this->HGraph);
      }
    } // if no left blocks, add edge from source
  }

  // Add initial edges in vertical graph
  for(int i=0;i<(int)VGraph.size();i++) {
    if(i==sourceNode or i==sinkNode) {continue;}
    // check blocks above current block
    candidate.clear(); candidate=caseSP.GetAboveBlock(i);
    for(vector<int>::iterator it=candidate.begin(); it!=candidate.end(); ++it) {
      //tmpE.weight=VGraph.at(i).weight;
      //tmpE.next=(*it);
      //VGraph.at(i).Edges.push_back(tmpE);

      //while(bias<150){	
    //bias = (rand()%10) *50;
    //}
      if(i<caseNL.GetSizeofBlocks() && *it<caseNL.GetSizeofBlocks() ) {
        if(mode==0 ) {
          AddEdgeforVertex(i, *it, VGraph.at(i).weight+bias_Vgraph, this->VGraph);
        } else if (mode ==1) {
          AddEdgeforVertex(i, *it, VGraph.at(i).weight+bias_Vgraph+caseNL.GetBlockMargin(i,*it), this->VGraph);
        } else {
          AddEdgeforVertex(i, *it, VGraph.at(i).weight, this->VGraph);
        }
      } else {
        AddEdgeforVertex(i, *it, VGraph.at(i).weight, this->VGraph);
      }
    } // add edges conncting blocks above current one
    if(candidate.empty()) {
      //tmpE.weight=VGraph.at(i).weight;
      //tmpE.next=sinkNode;
      //VGraph.at(i).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
        if(mode==0 or mode==1) {
          AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight+bias_Vgraph, this->VGraph);
        } else {
          AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight, this->VGraph);
        }
      } else {
        AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight, this->VGraph);
      }
    } // if no above blocks, add edge to sink
    candidate.clear(); candidate=caseSP.GetBelowBlock(i);
    if(candidate.empty()) {
      //tmpE.weight=0;
      //tmpE.next=i;
      //VGraph.at(sourceNode).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
        if(mode==0 or mode==1) {
          AddEdgeforVertex(sourceNode, i, 0+bias_Vgraph, this->VGraph);
        } else {
          AddEdgeforVertex(sourceNode, i, 0, this->VGraph);
        }
      } else {
        AddEdgeforVertex(sourceNode, i, 0, this->VGraph);
      }
    } // if no below blocks, add edge from source
  }
}


void ConstGraph::AddLargePenalty() {
  AddEdgeforVertex(sinkNode, sourceNode, -99999, this->HGraph);
  AddEdgeforVertex(sinkNode, sourceNode, -99999, this->VGraph);
}

ConstGraph::ConstGraph() {
  origNodeSize=-1;
  sourceNode=-1;
  sinkNode=-1;
  HGraph.clear();
  VGraph.clear();
  //LAMBDA=1000;
  //GAMAR=30;
  //BETA=100;
  //SIGMA=1000;
}

ConstGraph::ConstGraph(design& caseNL, SeqPair& caseSP) {
  //LAMBDA=1000;
  //GAMAR=30;
  //BETA=100;
  //SIGMA = 1000;
  HGraph.resize(caseNL.GetSizeofBlocks());
  VGraph.resize(caseNL.GetSizeofBlocks());
  origNodeSize=(int)HGraph.size();
  for(int i=0;i<(int)HGraph.size();i++) {
    HGraph.at(i).weight=caseNL.GetBlockWidth(i, caseSP.GetBlockOrient(i), caseSP.GetBlockSelected(i));
    HGraph.at(i).isSource=false;
    HGraph.at(i).isSink=false;
    HGraph.at(i).isVirtual=false;
  } // Initialize real blocks in horizontal graph
  for(int i=0;i<(int)VGraph.size();i++) {
    VGraph.at(i).weight=caseNL.GetBlockHeight(i, caseSP.GetBlockOrient(i), caseSP.GetBlockSelected(i));
    VGraph.at(i).isSource=false;
    VGraph.at(i).isSink=false;
    VGraph.at(i).isVirtual=false;
  } // Initialize real blocks in vertical graph
  // Add source node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=true;
  HGraph.back().isSink=false;
  HGraph.back().isVirtual=true;
  sourceNode=(int)HGraph.size()-1;
  // Add sink node in horizontal graph
  HGraph.resize(HGraph.size()+1);
  HGraph.back().weight=0;
  HGraph.back().isSource=false;
  HGraph.back().isSink=true;
  HGraph.back().isVirtual=true;
  sinkNode=(int)HGraph.size()-1;
  // Add source node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=true;
  VGraph.back().isSink=false;
  VGraph.back().isVirtual=true;
  // Add sink node in vertical graph
  VGraph.resize(VGraph.size()+1);
  VGraph.back().weight=0;
  VGraph.back().isSource=false;
  VGraph.back().isSink=true;
  VGraph.back().isVirtual=true;
  // Add dummy nodes for symmetry constraints
  for(int i=0;i<(int)caseNL.GetSizeofSBlocks();i++) {
    HGraph.resize(HGraph.size()+1);
    HGraph.back().weight=0;
    HGraph.back().isSource=false;
    HGraph.back().isSink=false;
    HGraph.back().isVirtual=true;
    VGraph.resize(VGraph.size()+1);
    VGraph.back().weight=0;
    VGraph.back().isSource=false;
    VGraph.back().isSink=false;
    VGraph.back().isVirtual=true;
  }
  // temporary variables
  vector<int> candidate;

int bias_Vgraph = caseNL.bias_Vgraph;
int bias_Hgraph = caseNL.bias_Hgraph;
/*
	//int bias=100;
    //int bias_graph;
//added by yg
	if(bias_flag==0){
	bias_graph=0;
	cout<<"bias_flag"<<" "<<bias_flag<<endl;
	cout<<"bias"<<" "<<bias_graph<<endl;
	srand(time(NULL));
	while(bias_graph<100){	
    bias_graph = (rand()%10) *50;
    }

  //write out bias
	fstream f("bias.const",ios::out);
	f<<"bias"<<" "<<bias_graph<<endl;
	f.close();
	bias_flag=1;
	cout<<"bias_flag"<<" "<<bias_flag<<endl;
	cout<<"bias_graph"<<" "<<bias_graph<<endl;
	
}
*/
  //cout<<"bias_graph_for_edge"<<bias_graph<<endl;
  // Add initial edges in horizontal graph
  for(int i=0;i<(int)HGraph.size();i++) {
    if(i==sourceNode or i==sinkNode) {continue;}
    // check blocks right to current block
    candidate.clear(); candidate=caseSP.GetRightBlock(i);
    for(vector<int>::iterator it=candidate.begin(); it!=candidate.end(); ++it) {
      //tmpE.weight=HGraph.at(i).weight;
      //tmpE.next=(*it);
      //HGraph.at(i).Edges.push_back(tmpE);

     

      if(i<caseNL.GetSizeofBlocks() && *it<caseNL.GetSizeofBlocks() ) {
        AddEdgeforVertex(i, *it, HGraph.at(i).weight+bias_Hgraph, this->HGraph);
      } else {
        AddEdgeforVertex(i, *it, HGraph.at(i).weight, this->HGraph);
      }
    } // add edges conncting blocks right to current one
    if(candidate.empty()) {
      //tmpE.weight=HGraph.at(i).weight;
      //tmpE.next=sinkNode;
      //HGraph.at(i).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
      AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight+bias_Hgraph, this->HGraph);
      } else {
      AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight, this->HGraph);
      }
    } // if no right blocks, add edge to sink
    candidate.clear(); candidate=caseSP.GetLeftBlock(i);
    if(candidate.empty()) {
      //tmpE.weight=0;
      //tmpE.next=i;
      //HGraph.at(sourceNode).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
      AddEdgeforVertex(sourceNode, i, 0+bias_Hgraph, this->HGraph);
      } else {
      AddEdgeforVertex(sourceNode, i, 0, this->HGraph);
      }
    } // if no left blocks, add edge from source
  }

  // Add initial edges in vertical graph
  for(int i=0;i<(int)VGraph.size();i++) {
    if(i==sourceNode or i==sinkNode) {continue;}
    // check blocks above current block
    candidate.clear(); candidate=caseSP.GetAboveBlock(i);
    for(vector<int>::iterator it=candidate.begin(); it!=candidate.end(); ++it) {
      //tmpE.weight=VGraph.at(i).weight;
      //tmpE.next=(*it);
      //VGraph.at(i).Edges.push_back(tmpE);

      //while(bias<150){	
    //bias = (rand()%10) *50;
    //}


      if(i<caseNL.GetSizeofBlocks() && *it<caseNL.GetSizeofBlocks() ) {
        AddEdgeforVertex(i, *it, VGraph.at(i).weight+bias_Vgraph, this->VGraph);
      } else {
        AddEdgeforVertex(i, *it, VGraph.at(i).weight, this->VGraph);
      }
    } // add edges conncting blocks above current one
    if(candidate.empty()) {
      //tmpE.weight=VGraph.at(i).weight;
      //tmpE.next=sinkNode;
      //VGraph.at(i).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
      AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight+bias_Vgraph, this->VGraph);
      } else {
      AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight, this->VGraph);
      }
    } // if no above blocks, add edge to sink
    candidate.clear(); candidate=caseSP.GetBelowBlock(i);
    if(candidate.empty()) {
      //tmpE.weight=0;
      //tmpE.next=i;
      //VGraph.at(sourceNode).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
      AddEdgeforVertex(sourceNode, i, 0+bias_Vgraph, this->VGraph);
      } else {
      AddEdgeforVertex(sourceNode, i, 0, this->VGraph);
      }
    } // if no below blocks, add edge from source
  }

}

ConstGraph::ConstGraph(const ConstGraph &cg) {
  //LAMBDA=cg.LAMBDA;
  //GAMAR=cg.GAMAR;
  //BETA=cg.BETA;
  //SIGMA=cg.SIGMA;
  origNodeSize=cg.origNodeSize;
  sourceNode=cg.sourceNode;
  sinkNode=cg.sinkNode;
  HGraph=cg.HGraph;
  VGraph=cg.VGraph;
}

ConstGraph& ConstGraph::operator=(const ConstGraph &cg) {
  //LAMBDA=cg.LAMBDA;
  //GAMAR=cg.GAMAR;
  //BETA=cg.BETA;
  //SIGMA=cg.SIGMA;
  origNodeSize=cg.origNodeSize;
  sourceNode=cg.sourceNode;
  sinkNode=cg.sinkNode;
  HGraph=cg.HGraph;
  VGraph=cg.VGraph;
  return *this;
}

void ConstGraph::PrintConstGraph() {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.PrintConstGraph");

  logger->debug("== Constraint Graph ==");
  logger->debug("LAMBDA {0} GARMAR {1}  BETA {2} origNodeSize {3} sourceNode {4} sinkNode {5}",LAMBDA,GAMAR,BETA,origNodeSize,sourceNode,sinkNode);
  logger->debug("Horizontal graph");
  for(int i=0;i<(int)HGraph.size();i++) {
    logger->debug("Node {0} weight {1} isSource",i,HGraph.at(i).weight);
    logger->debug("{0} isSink {1}",HGraph.at(i).isSource,HGraph.at(i).isSink);
    logger->debug("isVirtual- {0} position {1} << {2} backpost {3} << {4}",HGraph.at(i).isVirtual,HGraph.at(i).position,HGraph.at(i).precedent,HGraph.at(i).backpost,HGraph.at(i).backprec);
    for(int j=0;j<(int)HGraph.at(i).Edges.size();j++) {
      logger->debug("Edge to {0} weight {1} isbackward {2}",HGraph.at(i).Edges.at(j).next,HGraph.at(i).Edges.at(j).weight,HGraph.at(i).Edges.at(j).isBackward);
    }
  }
  logger->debug("Vertical graph");
  for(int i=0;i<(int)VGraph.size();i++) {
    logger->debug("Node {0} weight {1} isSource",i,VGraph.at(i).weight);
    logger->debug("{0} isSink {1}",VGraph.at(i).isSource,VGraph.at(i).isSink);
    logger->debug("isVirtual- {0} position {1} << {2} backpost {3} << {4}",VGraph.at(i).isVirtual,VGraph.at(i).position,VGraph.at(i).precedent,VGraph.at(i).backpost,VGraph.at(i).backprec);
    for(int j=0;j<(int)VGraph.at(i).Edges.size();j++) {
      logger->debug("Edge to {0} weight {1} isbackward {2}",VGraph.at(i).Edges.at(j).next,VGraph.at(i).Edges.at(j).weight,VGraph.at(i).Edges.at(j).isBackward);
    }
  }
}

bool ConstGraph::AddEdgeforVertex(int current, int next, int weight, vector<Vertex> &graph) {
  Edge tmpE;
  tmpE.next=next;
  tmpE.weight=weight;
  if( CheckForwardPath(next, current, graph) ) {tmpE.isBackward=true;
  //if(CheckRelatedForwardEdge(current, next, graph)) {tmpE.isBackward=true;
  } else { tmpE.isBackward=false; }
  bool mark=false;
  if(current>=0 && current<(int)graph.size() && next>=0 && next<(int)graph.size() ) {
    graph.at(current).Edges.push_back(tmpE);
    mark=true;
  }
  return mark;
}

/* not available in new version
bool ConstGraph::CheckRelatedForwardEdge(int current, int next, vector<Vertex> &graph) {
  // checking edge: current --> next
  // return true if corresponding forward edge exists, otherwise return false
  bool mark=false;
  if(current>=0 && current<(int)graph.size() && next>=0 && next<(int)graph.size()) {
    for(int i=0;i<(int)graph.at(next).Edges.size();i++ ) {
      if(graph.at(next).Edges.at(i).next==current && !graph.at(next).Edges.at(i).isBackward) {
        mark=true; break;
      }
    }
  }
  return mark;
}

bool ConstGraph::CheckOppositeEdge(int current, int next, vector<Vertex> &graph) {
  // checking edge: current --> next
  // return True if opposite edge exists, otherwise return False
  bool mark=false;
  if(current>=0 && current<(int)graph.size() && next>=0 && next<(int)graph.size()) {
    for(int i=0;i<(int)graph.at(next).Edges.size();i++ ) {
      if(graph.at(next).Edges.at(i).next==current) {
        mark=true; break;
      }
    }
  }
  return mark;
}
*/

bool ConstGraph::CheckForwardPath(int current, int next, vector<Vertex>& graph) {
  // return true if there is a forward path from current to next node
  stack<int> Stack;
  bool *visited =new bool[graph.size()];
  for(unsigned int i=0;i<graph.size();++i) {visited[i]=false;}
  topologicalSortUtil(current, visited, Stack, graph, false);
  bool mark;
  if(visited[next]) {mark=true;} else {mark=false;}
  delete[] visited;
  return mark;
}

void ConstGraph::topologicalSortUtil(int v, bool visited[], stack<int> &Stack, vector<Vertex> &graph, bool backward ) {
  visited[v] = true;
  for(vector<Edge>::iterator it=graph.at(v).Edges.begin(); it!=graph.at(v).Edges.end(); ++it) {
    if (!backward ) { // forward sorting
      if( !it->isBackward &&  !visited[it->next]) { topologicalSortUtil(it->next, visited, Stack, graph, backward);}
    } else { // backward sorting
      if(  it->isBackward &&  !visited[it->next]) { topologicalSortUtil(it->next, visited, Stack, graph, backward);}
    }
  }
  Stack.push(v);
}

void ConstGraph::CalculateLongestPath(int s, vector<Vertex> &graph, bool backward) {
  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.CalculateLongestPath");
  stack<int> Stack;
  //int dist[(int)graph.size()];
  // Mark all vertices as not visited
  bool *visited =new bool[(int)graph.size()];
  for(unsigned int i=0;i<graph.size();++i)
    visited[i]=false;
  // Call the recursive helper function to store Topological
  // Sort starting from all vertices one by one
  for(unsigned int i=0;i<graph.size();++i)
    if(!visited[i]) 
      topologicalSortUtil(i, visited, Stack, graph, backward);
  // Initialize distances to all vertices as infinite and 
  // distance to source as 0
  if(!backward) {
    for(unsigned int i=0;i<graph.size();++i) {
      graph.at(i).position=NINF;
      graph.at(i).precedent=-1;
    }
    graph.at(s).position=0;
  } else {
    for(unsigned int i=0;i<graph.size();++i) {
      graph.at(i).backpost=NINF;
      graph.at(i).backprec=-1;
    }
    graph.at(s).backpost=0;
  }
  // Process vertices in topological order
  while(!Stack.empty()) {
    //cout<<Stack.top() <<" ";
    // Get the next vertex from topological order
    int u=Stack.top();
    Stack.pop();
    // Update distances of all adjacent vertices
    if(!backward) {
      if(graph[u].position!=NINF) {
        for(vector<Edge>::iterator it=graph[u].Edges.begin(); it!=graph[u].Edges.end(); ++it) {
          logger->debug("current node and next node {0} {1}",u,it->next);
          //if(!it->isBackward && graph[it->next].position<graph[u].position+it->weight) {
          if(graph[it->next].position<graph[u].position+it->weight) {
            logger->debug("next node {0} position {1}  updated to {2}",it->next,graph[it->next].position,graph[u].position + it->weight);
            graph[it->next].position=graph[u].position + it->weight;
            graph[it->next].precedent=u;
            //std::cout<<it->next<<" prec "<<u<<" pos "<<graph[it->next].position<<std::endl;
          }
        }
      }
    } else {
      if(graph[u].backpost!=NINF) {
        for(vector<Edge>::iterator it=graph[u].Edges.begin(); it!=graph[u].Edges.end(); ++it) {
          //if( it->isBackward && graph[it->next].backpost<graph[u].backpost+it->weight) {
          if(graph[it->next].backpost<graph[u].backpost+it->weight) {
            graph[it->next].backpost=graph[u].backpost + it->weight;
            graph[it->next].backprec=u;
            //std::cout<<it->next<<" backprec "<<u<<" pos "<<graph[it->next].backpost<<std::endl;
          }
        }
      }
    }
  }
  delete[] visited;
  //cout<<endl;
  //for(int i=0;i<(int)graph.size();++i) 
  //  (graph[i].position==NINF)? cout<<i<<":INF ": cout<<i<<":"<<graph[i].position<<" ";
  //cout<<endl;
}

bool ConstGraph::FastInitialScan() {
  bool fastscan_H = CheckPositiveCycle(this->HGraph);
  bool fastscan_V = CheckPositiveCycle(this->VGraph);
  if( fastscan_H or fastscan_V){
    return true;
  }else{
    return false;
  }
  // return true if any violation found, otherwise return false
  //if(CheckPositiveCycle(this->HGraph)) return true;
  //return CheckPositiveCycle(this->VGraph);
}

bool ConstGraph::CheckPositiveCycle(vector<Vertex> &graph) {
// return true when there exists positive cycle in constraint graph
  CalculateLongestPath(sourceNode, graph, false);
  bool mark=false;
  //int sum=0;
  for(unsigned int i=0;i<graph.size() && !mark ;++i) {
    for(vector<Edge>::iterator ei=graph.at(i).Edges.begin(); ei!=graph.at(i).Edges.end() && !mark ; ++ei) {
      int dist=min(graph.at(ei->next).position-graph.at(i).position-ei->weight, 0);
      if(dist!=0) {mark=true;}
      //sum+=dist*dist;
    }
  }
  return mark;
}

double ConstGraph::CalculatePenalty(vector<Vertex> &graph) {
  //CalculateLongestPath(sourceNode, graph, false);
  double sum=0;
  for(unsigned int i=0;i<graph.size();++i) {
    for(vector<Edge>::iterator ei=graph.at(i).Edges.begin(); ei!=graph.at(i).Edges.end(); ++ei) {
      int dist=min(graph.at(ei->next).position-graph.at(i).position-ei->weight, 0);
      sum+=dist*dist;
    }
  }
  return sum;
}

int ConstGraph::GetX(int i) {
  return this->HGraph.at(i).position;
}

int ConstGraph::GetY(int i) {
  return this->VGraph.at(i).position;
}

double ConstGraph::CalculateRatio() {
  //int sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  if((double)(this->HGraph.at(sinkNode).position)/(this->VGraph.at(sinkNode).position)>=1)
  return (double)(this->HGraph.at(sinkNode).position)/(this->VGraph.at(sinkNode).position);
  else
  return (double)(this->VGraph.at(sinkNode).position)/(this->HGraph.at(sinkNode).position);
}

double ConstGraph::CalculateWireLengthAP(design& caseNL, Aplace& caseAP) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.CalculateWireLengthAP");

  double sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  vector<placerDB::point> pos; placerDB::point p, bp; int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each net
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    pos.clear();
    if((ni->priority).compare("min")==0) { alpha=4;
    } else if((ni->priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=ni->weight; // add weight to reflect the modification for bigMacros
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
        for(unsigned int i=0;i<pos_pin.size();i++){
          p = pos_pin[i];
          pos.push_back(p);
	}
      }
    }
    int x=0; int y=0;
    for(vector<placerDB::point>::iterator pi=pos.begin(); pi!=pos.end(); ++pi) {
      for(vector<placerDB::point>::iterator qi=pi+1; qi!=pos.end(); ++qi) {
        if( abs((pi->x)-(qi->x))>x ) {x=abs((pi->x)-(qi->x));}
        if( abs((pi->y)-(qi->y))>y ) {y=abs((pi->y)-(qi->y));}
      }
    }
    sum+=((x+y)*alpha);
  }
  // for each terminal
  for(int i=0;i<(int)caseNL.GetSizeofTerminals();++i) {
    if(solved_terminals.find(i)!=solved_terminals.end()) {continue;}
    solved_terminals.insert(i);
    int netIdx=caseNL.Terminals.at(i).netIter;
    int sbIdx=caseNL.Terminals.at(i).SBidx;
    int cp=caseNL.Terminals.at(i).counterpart;
    if(netIdx<0 or netIdx>=caseNL.GetSizeofNets()) {
      logger->info("Placer-Warning: terminal {0} is dangling; set it on origin", i);
      //caseNL.Terminals.at(i).center.x = 0;
      //caseNL.Terminals.at(i).center.y = 0;
      continue;
    }
    //pos.clear();
    if((caseNL.Nets.at(netIdx).priority).compare("min")==0) { alpha=4;
    } else if((caseNL.Nets.at(netIdx).priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=caseNL.Nets.at(netIdx).weight; // add weight to reflect the modification for bigMacros
    if(sbIdx!=-1) { // in symmetry group
      placerDB::Smark axis=caseAP.GetSBlockDir(sbIdx);
      if(cp==i) { // self-symmetric
        if(axis==placerDB::V) {
          int distTerm=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTerm) {distTerm=p.y;}
                if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
              }
            }
          }
          sum+=distTerm*alpha;
        } else if(axis==placerDB::H) {
          int distTerm=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++) {
                p = pos_pin[k];
                if(p.x<distTerm) {distTerm=p.x;}
                if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              }
            }
          }
          sum+=distTerm*alpha;
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      } else { // symmetry pair
        if(solved_terminals.find(cp)!=solved_terminals.end()) {logger->debug("Placer-Error: terminal {0} and {1} are not solved simultaneously!",i,cp); continue;}
        solved_terminals.insert(cp);
        int netIdx2=caseNL.Terminals.at(cp).netIter;
        if(netIdx2<0 or netIdx2>=caseNL.GetSizeofNets()) {
          logger->debug("Placer-Error: terminal {0} is not dangling, but its counterpart {1} is dangling; set them on origin",i,cp);
          //caseNL.Terminals.at(i).center.x = 0;
          //caseNL.Terminals.at(i).center.y = 0;
          //caseNL.Terminals.at(cp).center.x = 0;
          //caseNL.Terminals.at(cp).center.y = 0;
          continue;
        }
        int alpha2;
        if((caseNL.Nets.at(netIdx2).priority).compare("min")==0) { alpha2=4;
        } else if((caseNL.Nets.at(netIdx2).priority).compare("mid")==0) { alpha2=2;
        } else { alpha2=1; }
        alpha2*=caseNL.Nets.at(netIdx2).weight; // add weight to reflect the modification for bigMacros
        if(axis==placerDB::V) {
          int distTermL=INT_MAX, distTermR=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL) {distTermL=p.x;}
                if(Xmax-p.x<distTermR) {distTermR=Xmax-p.x;}
              }
            }
          }
          int distTermL2=INT_MAX, distTermR2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL2) {distTermL2=p.x;}
                if(Xmax-p.x<distTermR2) {distTermR2=Xmax-p.x;}
              }
            }
          }
          if(distTermL*alpha+distTermR2*alpha2<distTermR*alpha+distTermL2*alpha2) {
            sum+=(distTermL*alpha+distTermR2*alpha2);
          } else {
            sum+=(distTermR*alpha+distTermL2*alpha2);
          }
        } else if (axis==placerDB::H) {
          int distTermL=INT_MAX, distTermU=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL) {distTermL=p.y;}
                if(Ymax-p.y<distTermU) {distTermU=Ymax-p.y;}
              }
            }
          }
          int distTermL2=INT_MAX, distTermU2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL2) {distTermL2=p.y;}
                if(Ymax-p.y<distTermU2) {distTermU2=Ymax-p.y;}
              }
            }
          }
          if(distTermL*alpha+distTermU2*alpha2<distTermU*alpha+distTermL2*alpha2) {
            sum+=(distTermL*alpha+distTermU2*alpha2);
          } else {
            sum+=(distTermU*alpha+distTermL2*alpha2);
          }
        } else {
          logger->debug("Placer-Error: incorrect axis direction");
        }
      }
    } else { // not in symmetry group
      int tar=-1;
      for(unsigned int j=0;j<caseNL.Port_Location.size();++j) {
        if(caseNL.Port_Location.at(j).tid==i) {tar=j; break;}
      }
      if(tar!=-1) { // specifiy PortLocation constraint
        int x1=Xmax/3, x2=Xmax*2/3, x3=Xmax;
        int y1=Ymax/3, y2=Ymax*2/3, y3=Ymax;
        pos.clear();
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              pos.push_back(p);
            }
          }
        }
        int shot=-1;
        int distTerm=INT_MAX;
        for(unsigned int k=0;k<pos.size();++k) {
          p=pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch(caseNL.Port_Location.at(tar).pos) {
            case placerDB::TL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-0)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-0)+Ymax-p.y; shot=k;}
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;}
                 }
                 break;
            case placerDB::TC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;}
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;}
                 }
                 break;
            case placerDB::TR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;}
                   if( std::abs(p.x-x3)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x3)+Ymax-p.y; shot=k;}
                 }
                 break;
            case placerDB::RT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;}
                   if( std::abs(p.y-y3)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y3)+Xmax-p.x; shot=k;}
                 }
                 break;
            case placerDB::RC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;}
                 }
                 break;
            case placerDB::RB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-0)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-0)+Xmax-p.x; shot=k;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;}
                 }
                 break;
            case placerDB::BL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-0)+p.y<distTerm ) {distTerm=std::abs(p.x-0)+p.y; shot=k;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;}
                 }
                 break;
            case placerDB::BC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;}
                 }
                 break;
            case placerDB::BR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;}
                   if( std::abs(p.x-x3)+p.y<distTerm ) {distTerm=std::abs(p.x-x3)+p.y; shot=k;}
                 }
                 break;
            case placerDB::LT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;}
                   if( std::abs(p.y-y3)+p.x<distTerm ) {distTerm=std::abs(p.y-y3)+p.x; shot=k;}
                 }
                 break;
            case placerDB::LC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;}
                 }
                 break;
            case placerDB::LB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-0)+p.x<distTerm ) {distTerm=std::abs(p.y-0)+p.x; shot=k;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;}
                 }
                 break;
            default :
                 logger->debug("Placer-Warning: incorrect port position");
          }
        }
        if(shot!=-1) {sum+=distTerm*alpha;}
      } else { // no constraint
        int distTerm=INT_MAX;
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              if(p.x<distTerm) {distTerm=p.x;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              if(p.y<distTerm) {distTerm=p.y;}
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
            }
          }
        }
        sum+=distTerm*alpha;
      }
    }
  }
  return sum;
}


double ConstGraph::CalculateWireLengthAPRetire(design& caseNL, Aplace& caseAP) {
  double sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  vector<placerDB::point> pos; placerDB::point p, bp; int alpha;
  vector<placerDB::point> pos_pin;
  //vector<vector<placerDB::point> > pos_pin_all;
  // for each net
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    pos.clear();
    //pos_pin_all.clear();
    bool hasTerminal=false;
    int distTerm=-1*NINF;
    if((ni->priority).compare("min")==0) { alpha=4;
    } else if((ni->priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=ni->weight; // add weight to reflect the modification for bigMacros
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        //placerDB::Omark ort=caseSP.GetBlockOrient(ci->iter2);
        //p.x=caseNL.GetBlockWidth(ci->iter2, ort)/2;
        //p.y=caseNL.GetBlockHeight(ci->iter2, ort)/2;
        //p.x+=this->HGraph.at(ci->iter2).position;
        //p.y+=this->VGraph.at(ci->iter2).position;
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
	//pos_pin_all.push_back(pos_pin);	
          for(unsigned int i=0;i<pos_pin.size();i++){
			p = pos_pin[i];
            pos.push_back(p);
            if( caseNL.GetBlockSymmGroup(ci->iter2)==-1  ) { // not in any symmetry group
              if(p.x<distTerm) {distTerm=p.x;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              if(p.y<distTerm) {distTerm=p.y;}
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
            } else { // if in symmetry group
              if ( caseAP.GetSBlockDir(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::V  ) {
                if(p.x<distTerm) {distTerm=p.x;}
                if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              } else if ( caseAP.GetSBlockDir(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::H  ) {
                if(p.y<distTerm) {distTerm=p.y;}
                if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
              }
            }
	       }
          } else if (ci->type==placerDB::Terminal) {
            //cout<<"Terminal "<<ci->iter<<" ";
            hasTerminal=true;
          }
        }
    int x=0; int y=0;
    for(vector<placerDB::point>::iterator pi=pos.begin(); pi!=pos.end(); ++pi) {
      for(vector<placerDB::point>::iterator qi=pi+1; qi!=pos.end(); ++qi) {
        if( abs((pi->x)-(qi->x))>x ) {x=abs((pi->x)-(qi->x));}
        if( abs((pi->y)-(qi->y))>y ) {y=abs((pi->y)-(qi->y));}
        //sum+=abs((pi->x)-(qi->x));
        //sum+=abs((pi->y)-(qi->y));
      }
    }
    sum+=((x+y)*alpha);
    if(hasTerminal) {sum+=(distTerm*alpha);}//cout<<"; range: "<<distTerm<<endl;}
  }
  return sum;
}


double ConstGraph::CalculateWireLengthRetire(design& caseNL, SeqPair& caseSP) {
  double sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  vector<placerDB::point> pos; placerDB::point p, bp; int alpha;
  vector<placerDB::point> pos_pin;
  //vector<vector<placerDB::point> > pos_pin_all;
  // for each net
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    pos.clear();
    //pos_pin_all.clear();
    bool hasTerminal=false;
    int distTerm=-1*NINF;
    if((ni->priority).compare("min")==0) { alpha=4;
    } else if((ni->priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=ni->weight; // add weight to reflect the modification for bigMacros
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        //placerDB::Omark ort=caseSP.GetBlockOrient(ci->iter2);
        //p.x=caseNL.GetBlockWidth(ci->iter2, ort)/2;
        //p.y=caseNL.GetBlockHeight(ci->iter2, ort)/2;
        //p.x+=this->HGraph.at(ci->iter2).position;
        //p.y+=this->VGraph.at(ci->iter2).position;
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
	//pos_pin_all.push_back(pos_pin);	
          for(unsigned int i=0;i<pos_pin.size();i++){
			p = pos_pin[i];
            pos.push_back(p);
            if( caseNL.GetBlockSymmGroup(ci->iter2)==-1  ) { // not in any symmetry group
              if(p.x<distTerm) {distTerm=p.x;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              if(p.y<distTerm) {distTerm=p.y;}
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
            } else { // if in symmetry group
              if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::V  ) {
                if(p.x<distTerm) {distTerm=p.x;}
                if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              } else if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::H  ) {
                if(p.y<distTerm) {distTerm=p.y;}
                if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
              }
            }
	  }
      } else if (ci->type==placerDB::Terminal) {
        //cout<<"Terminal "<<ci->iter<<" ";
        hasTerminal=true;
      }
    }
    int x=0; int y=0;
    for(vector<placerDB::point>::iterator pi=pos.begin(); pi!=pos.end(); ++pi) {
      for(vector<placerDB::point>::iterator qi=pi+1; qi!=pos.end(); ++qi) {
        if( abs((pi->x)-(qi->x))>x ) {x=abs((pi->x)-(qi->x));}
        if( abs((pi->y)-(qi->y))>y ) {y=abs((pi->y)-(qi->y));}
        //sum+=abs((pi->x)-(qi->x));
        //sum+=abs((pi->y)-(qi->y));
      }
    }
    sum+=((x+y)*alpha);
    if(hasTerminal) {sum+=(distTerm*alpha);}//cout<<"; range: "<<distTerm<<endl;}
  }
  return sum;
}

double ConstGraph::LinearConst(design& caseNL, SeqPair& caseSP){

  double sum = 0;
  std::vector<std::vector<double> > feature_value;
  std::vector<std::vector<std::string> > feature_name;
  ExtractLength(caseNL, caseSP, feature_value, feature_name);

  for(int i=0;i< caseNL.Nets.size(); i++){
     double temp_sum = 0;
     for(int j=0;j<caseNL.Nets[i].connected.size();j++){
        //std::cout<<"LinearConst Cost"<<caseNL.Nets[i].connected[j].alpha<<" "<<caseNL.Nets[i].upperBound<<std::endl;
        temp_sum += caseNL.Nets[i].connected[j].alpha*feature_value[i][j];
        //std::cout<<"LinearConst Cost"<<caseNL.Nets[i].connected[j].alpha*feature_value[i][j]<<std::endl;
     }
     if(temp_sum<=caseNL.Nets[i].upperBound){
        temp_sum = 0;

     }else{
        temp_sum = temp_sum - caseNL.Nets[i].upperBound;
     }
     sum += temp_sum;
  }

  return sum;

}

double ConstGraph::ML_LinearConst(design& caseNL, SeqPair& caseSP){

  double sum = 0;
  std::vector<std::vector<double> > feature_value;
  std::vector<std::vector<std::string> > feature_name;
  ExtractLength(caseNL, caseSP, feature_value, feature_name);

  for(int i =0; i<feature_value.size();i++){
     
     for(int j=0;j<feature_value[i].size();j++){
        //std::cout<<feature_value[i][j]<<" ";
     }
     //std::cout<<std::endl;

  }

  for(int i =0; i<feature_name.size();i++){

     for(int j=0;j<feature_name[i].size();j++){
        //std::cout<<feature_name[i][j]<<" ";
     }
     //std::cout<<std::endl;

  }


  for(int i=0;i<caseNL.ML_Constraints.size();i++){
     double temp_sum = 0;
     for(int j=0;j<caseNL.ML_Constraints[i].Multi_linearConst.size();j++){

        for(int k=0;k<caseNL.ML_Constraints[i].Multi_linearConst[j].pins.size();k++){
           int index_i=0;
           int index_j=0;
           //std::cout<<"ML Linear "<<caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].first<<" "<<caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].second<<std::endl;
           for(int m=0;m<caseNL.Nets.size();m++){
               for(int n=0;n<caseNL.Nets[m].connected.size();n++){

                  //std::cout<<"searching" <<m<<" "<<n<<" "<<caseNL.Nets[m].connected[n].iter << " "<< caseNL.Nets[m].connected[n].iter2 << " " << caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].first << " " << caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].second<<std::endl;

                  if(caseNL.Nets[m].connected[n].iter2 == caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].first && caseNL.Nets[m].connected[n].iter == caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].second){

                     //std::cout<<" found " <<caseNL.Nets[m].connected[n].iter2 << " "<< caseNL.Nets[m].connected[n].iter << " " << caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].first << " " << caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].second<<std::endl;

                     index_i=m;
                     index_j=n;
                     break;
                  }
               }
              }
         //std::cout<< caseNL.Nets[index_i].connected[index_j].iter2 << " "<< caseNL.Nets[index_i].connected[index_j].iter << " " << caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].first << " " << caseNL.ML_Constraints[i].Multi_linearConst[j].pins[k].second<<std::endl;
         //std::cout<<"MLLinearConst Cost: alpha "<<caseNL.ML_Constraints[i].Multi_linearConst[j].alpha[k]<<" upperbound "<<caseNL.ML_Constraints[i].upperBound<<" block idex "<<caseNL.Nets[index_i].connected[index_j].iter2<<" pin idx "<<caseNL.Nets[index_i].connected[index_j].iter<<" index_i "<<index_i<<" index_j "<<index_j<<" dist "<<feature_value[index_i][index_j]<<" alpha*dist "<<caseNL.ML_Constraints[i].Multi_linearConst[j].alpha[k]*feature_value[index_i][index_j]<<" pin_name "<<feature_name[index_i][index_j]<<std::endl;
         temp_sum += caseNL.ML_Constraints[i].Multi_linearConst[j].alpha[k]*feature_value[index_i][index_j];
         
        }

     }
     if(temp_sum<=caseNL.ML_Constraints[i].upperBound){
        temp_sum = 0;
     }else{
        temp_sum = caseNL.ML_Constraints[i].upperBound;
     }
     sum += temp_sum;
  }

  return sum;

}


void ConstGraph::ExtractLength(design& caseNL, SeqPair& caseSP, std::vector<std::vector<double> > &feature_value, std::vector<std::vector<std::string> > &feature_name){

  vector<placerDB::point> pos; placerDB::point p, bp;
  vector<placerDB::point> pos_pin;
  std::map<string, std::vector<placerDB::point> > pin_maps;
  std::string pin_name;


  // for each net
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    // for each pin
    int net_pin_number = 0;
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      pos.clear();
      if(ci->type==placerDB::Block) {
        pin_name = ni->name + "_" + caseNL.Blocks[ci->iter2].back().name + "_" + std::to_string(net_pin_number);
        //pin_name = ni->name + "_" + caseNL.Blocks[ci->iter2].back().name;
        net_pin_number = net_pin_number + 1;
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
        //std::cout<<"Print Pin Contact Info"<<std::endl;
        for(unsigned int i=0;i<pos_pin.size();i++){
          p = pos_pin[i];
          //std::cout<<"Pin Center (x, y)"<<p.x<<" "<<p.y<<std::endl;
          pos.push_back(p);
	}
        pin_maps.insert(map<string, std::vector<placerDB::point> >::value_type (pin_name, pos));
      }
    }
  }

  updateTerminalCenter(caseNL, caseSP);

    // for each net
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    // for each terminal
      int net_terminal_number = 0;
      for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      pos.clear();
      if(ci->type==placerDB::Terminal) {
        pin_name = ni->name +"_"+std::to_string(net_terminal_number);
        net_terminal_number = net_terminal_number + 1;
        //std::cout<<"Terminal center (x,y) "<<caseNL.Terminals[ci->iter].center.x<<" "<<caseNL.Terminals[ci->iter].center.y<<std::endl;
        pos.push_back(caseNL.Terminals[ci->iter].center);
        pin_maps.insert(map<string, std::vector<placerDB::point> >::value_type (pin_name, pos));
      }
    }
  }


  std::vector<std::vector<placerDB::point> > center_points_all;
  //extract pin_name, feature_value
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    // for each pin
    string net_name = ni->name;
    int net_pin_number = 0;
    int net_terminal_number = 0;
    std::vector<std::vector<placerDB::point> > center_points;
    std::vector<std::string> temp_feature_name;
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        pin_name = net_name + "_" + caseNL.Blocks[ci->iter2].back().name+"_"+std::to_string(net_pin_number);
        //pin_name = net_name + "_" + caseNL.Blocks[ci->iter2].back().name;
        net_pin_number = net_pin_number + 1;
        temp_feature_name.push_back(pin_name);
        //std::cout<<"Sorted Pin name "<<pin_name<<" pin contact size "<<pin_maps[pin_name].size()<<std::endl;
        center_points.push_back(pin_maps[pin_name]);
        center_points_all.push_back(pin_maps[pin_name]);
      }else if(ci->type==placerDB::Terminal) {
        pin_name = net_name +"_" + std::to_string(net_terminal_number);
        net_terminal_number = net_terminal_number + 1;
        temp_feature_name.push_back(pin_name);
        //std::cout<<"Sorted terminal name "<<pin_name<<" terminal contact size "<<pin_maps[pin_name].size()<<std::endl;
        center_points.push_back(pin_maps[pin_name]);
        center_points_all.push_back(pin_maps[pin_name]);
      }
     
    }
    feature_name.push_back(temp_feature_name);

    std::vector<double> temp_feature = Calculate_Center_Point_feature(center_points);
    feature_value.push_back(temp_feature);
    
  }


}

std::vector<double> ConstGraph::Calculate_Center_Point_feature(std::vector<std::vector<placerDB::point> > &temp_contact){

  std::vector<double> temp_x;
  std::vector<double> temp_y;
  double temp_value_x;
  double temp_value_y;
  std::vector<double> feature;
  double sum_x;
  double sum_y;

  for(int i = 0;i < temp_contact.size();i++){

     sum_x = 0;
     sum_y = 0;

     for(int j=0;j < temp_contact[i].size();j++){
       sum_x = sum_x + (double) temp_contact[i][j].x;
       sum_y = sum_y + (double) temp_contact[i][j].y;
     }

    sum_x = sum_x / (double) temp_contact[i].size();
    sum_y = sum_y / (double) temp_contact[i].size();
    temp_x.push_back(sum_x);
    temp_y.push_back(sum_y);

  }

  sum_x=0;
  sum_y=0;

  for(int i=0; i< temp_x.size();i++){

    sum_x = sum_x + temp_x[i];
    sum_y = sum_y + temp_y[i];

  }

  double center_x = sum_x/ (double) temp_x.size();
  double center_y = sum_y/ (double) temp_y.size();

  for(int i=0;i<temp_x.size();i++){

     feature.push_back( abs(center_x - (double) temp_x[i]) + abs(center_y - (double) temp_y[i]) );

  }

  return feature;

}


double ConstGraph::CalculateWireLength(design& caseNL, SeqPair& caseSP) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.CalculateWireLength");

  double sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  vector<placerDB::point> pos; placerDB::point p, bp; int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each net
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    pos.clear();
    if((ni->priority).compare("min")==0) { alpha=4;
    } else if((ni->priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=ni->weight; // add weight to reflect the modification for bigMacros
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
        for(unsigned int i=0;i<pos_pin.size();i++){
          p = pos_pin[i];
          pos.push_back(p);
	}
      }
    }
    int x=0; int y=0;
    for(vector<placerDB::point>::iterator pi=pos.begin(); pi!=pos.end(); ++pi) {
      for(vector<placerDB::point>::iterator qi=pi+1; qi!=pos.end(); ++qi) {
        if( abs((pi->x)-(qi->x))>x ) {x=abs((pi->x)-(qi->x));}
        if( abs((pi->y)-(qi->y))>y ) {y=abs((pi->y)-(qi->y));}
      }
    }
    sum+=((x+y)*alpha);
  }
  // for each terminal
  for(int i=0;i<(int)caseNL.GetSizeofTerminals();++i) {
    if(solved_terminals.find(i)!=solved_terminals.end()) {continue;}
    solved_terminals.insert(i);
    int netIdx=caseNL.Terminals.at(i).netIter;
    int sbIdx=caseNL.Terminals.at(i).SBidx;
    int cp=caseNL.Terminals.at(i).counterpart;
    if(netIdx<0 or netIdx>=caseNL.GetSizeofNets()) {
      logger->debug("Placer-Warning: terminal {0} is dangling; set it on origin",i);
      //caseNL.Terminals.at(i).center.x = 0;
      //caseNL.Terminals.at(i).center.y = 0;
      continue;
    }
    //pos.clear();
    if((caseNL.Nets.at(netIdx).priority).compare("min")==0) { alpha=4;
    } else if((caseNL.Nets.at(netIdx).priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=caseNL.Nets.at(netIdx).weight; // add weight to reflect the modification for bigMacros
    if(sbIdx!=-1) { // in symmetry group
      placerDB::Smark axis=caseSP.GetSymmBlockAxis(sbIdx);
      if(cp==i) { // self-symmetric
        if(axis==placerDB::V) {
          int distTerm=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTerm) {distTerm=p.y;}
                if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
              }
            }
          }
          sum+=distTerm*alpha;
        } else if(axis==placerDB::H) {
          int distTerm=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++) {
                p = pos_pin[k];
                if(p.x<distTerm) {distTerm=p.x;}
                if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              }
            }
          }
          sum+=distTerm*alpha;
        } else {
          logger->debug("Placer-Error: incorrect axis direction");
        }
      } else { // symmetry pair
        if(solved_terminals.find(cp)!=solved_terminals.end()) {logger->debug("Placer-Error: terminal {0} and {1} are not solved simultaneously!",i,cp); continue;}
        solved_terminals.insert(cp);
        int netIdx2=caseNL.Terminals.at(cp).netIter;
        if(netIdx2<0 or netIdx2>=caseNL.GetSizeofNets()) {
          logger->debug("Placer-Error: terminal {0} is not dangling, but its counterpart {1} is dangling",i,cp);
          //caseNL.Terminals.at(i).center.x = 0;
          //caseNL.Terminals.at(i).center.y = 0;
          continue;
        }
        int alpha2;
        if((caseNL.Nets.at(netIdx2).priority).compare("min")==0) { alpha2=4;
        } else if((caseNL.Nets.at(netIdx2).priority).compare("mid")==0) { alpha2=2;
        } else { alpha2=1; }
        alpha2*=caseNL.Nets.at(netIdx2).weight; // add weight to reflect the modification for bigMacros
        if(axis==placerDB::V) {
          int distTermL=INT_MAX, distTermR=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL) {distTermL=p.x;}
                if(Xmax-p.x<distTermR) {distTermR=Xmax-p.x;}
              }
            }
          }
          int distTermL2=INT_MAX, distTermR2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL2) {distTermL2=p.x;}
                if(Xmax-p.x<distTermR2) {distTermR2=Xmax-p.x;}
              }
            }
          }
          if(distTermL*alpha+distTermR2*alpha2<distTermR*alpha+distTermL2*alpha2) {
            sum+=(distTermL*alpha+distTermR2*alpha2);
          } else {
            sum+=(distTermR*alpha+distTermL2*alpha2);
          }
        } else if (axis==placerDB::H) {
          int distTermL=INT_MAX, distTermU=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL) {distTermL=p.y;}
                if(Ymax-p.y<distTermU) {distTermU=Ymax-p.y;}
              }
            }
          }
          int distTermL2=INT_MAX, distTermU2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL2) {distTermL2=p.y;}
                if(Ymax-p.y<distTermU2) {distTermU2=Ymax-p.y;}
              }
            }
          }
          if(distTermL*alpha+distTermU2*alpha2<distTermU*alpha+distTermL2*alpha2) {
            sum+=(distTermL*alpha+distTermU2*alpha2);
          } else {
            sum+=(distTermU*alpha+distTermL2*alpha2);
          }
        } else {
          logger->debug("Placer-Error: incorrect axis direction");
        }
      }
    } else { // not in symmetry group
      int tar=-1;
      for(unsigned int j=0;j<caseNL.Port_Location.size();++j) {
        if(caseNL.Port_Location.at(j).tid==i) {tar=j; break;}
      }
      if(tar!=-1) { // specifiy PortLocation constraint
        int x1=Xmax/3, x2=Xmax*2/3, x3=Xmax;
        int y1=Ymax/3, y2=Ymax*2/3, y3=Ymax;
        pos.clear();
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              pos.push_back(p);
            }
          }
        }
        int shot=-1;
        int distTerm=INT_MAX;
        for(unsigned int k=0;k<pos.size();++k) {
          p=pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch(caseNL.Port_Location.at(tar).pos) {
            case placerDB::TL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-0)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-0)+Ymax-p.y; shot=k;}
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;}
                 }
                 break;
            case placerDB::TC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;}
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;}
                 }
                 break;
            case placerDB::TR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;}
                   if( std::abs(p.x-x3)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x3)+Ymax-p.y; shot=k;}
                 }
                 break;
            case placerDB::RT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;}
                   if( std::abs(p.y-y3)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y3)+Xmax-p.x; shot=k;}
                 }
                 break;
            case placerDB::RC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;}
                 }
                 break;
            case placerDB::RB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-0)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-0)+Xmax-p.x; shot=k;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;}
                 }
                 break;
            case placerDB::BL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-0)+p.y<distTerm ) {distTerm=std::abs(p.x-0)+p.y; shot=k;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;}
                 }
                 break;
            case placerDB::BC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;}
                 }
                 break;
            case placerDB::BR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;}
                   if( std::abs(p.x-x3)+p.y<distTerm ) {distTerm=std::abs(p.x-x3)+p.y; shot=k;}
                 }
                 break;
            case placerDB::LT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;}
                   if( std::abs(p.y-y3)+p.x<distTerm ) {distTerm=std::abs(p.y-y3)+p.x; shot=k;}
                 }
                 break;
            case placerDB::LC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;}
                 }
                 break;
            case placerDB::LB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;}
                 } else {
                   if( std::abs(p.y-0)+p.x<distTerm ) {distTerm=std::abs(p.y-0)+p.x; shot=k;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;}
                 }
                 break;
            default :
                 logger->debug("Placer-Warning: incorrect port position");
          }
        }
        if(shot!=-1) {sum+=distTerm*alpha;}
      } else { // no constraint
        int distTerm=INT_MAX;
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              if(p.x<distTerm) {distTerm=p.x;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;}
              if(p.y<distTerm) {distTerm=p.y;}
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;}
            }
          }
        }
        sum+=distTerm*alpha;
      }
    }
  }
  return sum;
}



//added by yg
double ConstGraph::CalculateMatchCost(design& caseNL, SeqPair& caseSP) {
	double sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  // for each net
  for(unsigned int i=0;i<caseNL.Match_blocks.size();i++) {
  int x1,y1,x2,y2;
        x1=this->HGraph.at(caseNL.Match_blocks[i].blockid1).position;
        y1=this->VGraph.at(caseNL.Match_blocks[i].blockid1).position;
	x2=this->HGraph.at(caseNL.Match_blocks[i].blockid2).position;
        y2=this->VGraph.at(caseNL.Match_blocks[i].blockid2).position;
	sum =sum + abs(x1-x2)+abs(y1-y2);
        }
  return sum;
}


double ConstGraph::CalculateDeadArea(design& caseNL, SeqPair& caseSP) {
  double cellArea=0;
  for(unsigned int i=0;i<caseNL.Blocks.size();++i) {
    int sel=caseSP.GetBlockSelected(i);
    int w=caseNL.GetBlockWidth(i, caseSP.GetBlockOrient(i), sel); // Get width of block when it's placed
    int h=caseNL.GetBlockHeight(i, caseSP.GetBlockOrient(i), sel); // Get height of block when it's placed
    cellArea+=(w*h);
  }
  return 1-cellArea/CalculateArea();
}


double ConstGraph::CalculateArea() {
  //int sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  return (double)(this->HGraph.at(sinkNode).position)*(this->VGraph.at(sinkNode).position);
}

double ConstGraph::CalculateCost(design& caseNL, SeqPair& caseSP) {
  double cost=0;
  CalculateLongestPath(sourceNode, this->HGraph, false);
  CalculateLongestPath(sourceNode, this->VGraph, false);
  cost += (CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph))*GAMAR;
  cost += CalculateWireLength(caseNL, caseSP)*LAMBDA;
  cost += CalculateMatchCost(caseNL, caseSP)*BETA;
  cost += CalculateRatio()*SIGMA;
  cost += CalculateArea();
  cost += CalculateDeadArea(caseNL, caseSP)*PHI;
  cost += LinearConst(caseNL, caseSP)*PI;
  cost += ML_LinearConst(caseNL, caseSP)*PII;
  //cout<<"GAMAR:"<<GAMAR<<" BETA "<<BETA<<"LAMBDA "<<LAMBDA<<endl;
  //cout<<"Penalt: "<<  (CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph))*GAMAR<<" vs "<< (CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph)) << endl;
  //cout<<"WL: "<<CalculateWireLength(caseNL, caseSP)*LAMBDA<<" vs "<<CalculateWireLength(caseNL, caseSP)<<endl;
  //cout<<"Area: "<<CalculateArea()<<endl;
  //cout<<"MAtch: "<<CalculateMatchCost(caseNL, caseSP)*BETA<<" vs "<< CalculateMatchCost(caseNL, caseSP) <<endl;
  //cout<<"Ratio: "<<CalculateRatio()*SIGMA<<" vs "<<CalculateRatio() <<endl;
  //cout<<"DeadArea: "<<CalculateDeadArea(caseNL, caseSP)*PHI<<" vs "<<CalculateDeadArea(caseNL, caseSP)<<endl;
  return cost;
}

void ConstGraph::Update_parameters(design& caseNL, SeqPair& caseSP) {
  //cout<<"Placer-Info: Update parameters"<<endl;
  //cout<<"OLD GAMAR:"<<GAMAR<<" BETA:"<<BETA<<" LAMBDA:"<<LAMBDA<<" SIGMA:"<<SIGMA<<endl;
  //cout<<"OLD_LAMBDA:"<<LAMBDA<<endl;
  //cout<<"OLD_BETA:"<<BETA<<endl;
  double cost=0;
  CalculateLongestPath(sourceNode, this->HGraph, false);
  CalculateLongestPath(sourceNode, this->VGraph, false);
  cost += (CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph))*GAMAR;
  cost += CalculateWireLength(caseNL, caseSP)*LAMBDA;
  cost += CalculateMatchCost(caseNL, caseSP)*BETA;
  cost += CalculateRatio()*SIGMA;
  cost += CalculateArea();
  cost += CalculateDeadArea(caseNL, caseSP)*PHI;
  cost += LinearConst(caseNL, caseSP)*PI;
  cost += ML_LinearConst(caseNL, caseSP)*PII;
  if(CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph)>0){
  GAMAR=cost/(CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph));
  }
  if(CalculateWireLength(caseNL, caseSP)>0){
  LAMBDA =cost/CalculateWireLength(caseNL, caseSP);
  }
  if(CalculateMatchCost(caseNL, caseSP)){
  BETA = cost/CalculateMatchCost(caseNL, caseSP);
  }
  if(CalculateRatio()){
  SIGMA = cost/CalculateRatio()*1.5;
  }
  if(CalculateDeadArea(caseNL, caseSP)) {
  PHI = cost/CalculateDeadArea(caseNL, caseSP) *1.8;
  }
  if(LinearConst(caseNL, caseSP)>0){
  PI = cost/LinearConst(caseNL, caseSP) * 2.0;
  }
  if(ML_LinearConst(caseNL, caseSP)>0){
  PII = cost/ML_LinearConst(caseNL, caseSP) * 2.0;
  }
  //cout<<"NEW GAMAR:"<<GAMAR<<" BETA:"<<BETA<<" LAMBDA:"<<LAMBDA<<" SIGMA:"<<SIGMA<<" PHI:"<<PHI<<endl;
  //cout<<"NEW_BETA:"<<BETA<<endl;

}

bool ConstGraph::ConstraintHorizontalDistance(int n1, int n2, int c1, int c2 ) {
  bool mark=true;
  mark = (mark && AddEdgeforVertex(n1, n2, c1, HGraph) );
  mark = (mark && AddEdgeforVertex(n1, n2, -1*c2, HGraph) );
  return mark;
  //return (AddEdgeforVertex(n1, n2, c1, HGraph) or AddEdgeforVertex(n1, n2, -1*c2, HGraph));
}

bool ConstGraph::ConstraintVerticalDistance(int n1, int n2, int c1, int c2 ) {
  bool mark=true;
  mark = (mark && AddEdgeforVertex(n1, n2, c1, VGraph) );
  mark = (mark && AddEdgeforVertex(n1, n2, -1*c2, VGraph) );
  return mark;
  //return (AddEdgeforVertex(n1, n2, c1, VGraph) or AddEdgeforVertex(n1, n2, -1*c2, VGraph));
}

bool ConstGraph::ConstraintVerticalOrder(int below, int above) {
  return AddEdgeforVertex(below, above, VGraph.at(below).weight, VGraph);
}

bool ConstGraph::ConstraintHorizontalOrder(int left, int right) {
  return AddEdgeforVertex(left, right, HGraph.at(left).weight, HGraph);
}

vector<int> ConstGraph::GenerateSlack(vector<int>& x) {
  vector<int> newx;
  if(!x.empty()) {
    int MAX=x.at(0);
    for(vector<int>::iterator it=x.begin(); it!=x.end(); ++it)
      if(*it>MAX) { MAX=*it; }
    for(vector<int>::iterator it=x.begin(); it!=x.end(); ++it)
      newx.push_back( MAX-(*it) );
  }
  return newx;
}

void ConstGraph::AlignReorganize(design& caseNL, vector< pair<int,int> >& sympair, placerDB::Smark axis, int i) {
  // Keep all symmetry pairs aligned in vertical(horizontal) graph and reorganize the symmetry pairs
  pair<int,int> tp;
  /*
  if(caseNL.SBlocks.at(i).sympair.size()!=0 or caseNL.SBlocks.at(i).selfsym.size()!=0){
    tp.first=sourceNode; tp.second=sinkNode;
    sympair.push_back(tp);
  }
  */

  if(axis==placerDB::V) {
    // Vertical symmetry axis
    CalculateLongestPath(sourceNode, this->HGraph, false);
    for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(i).sympair.begin(); pit!=caseNL.SBlocks.at(i).sympair.end(); ++pit) {
      if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
        // block pair
        // *  VGraph constraints BEGIN
        CalculateLongestPath(sourceNode, this->VGraph, false);
        if(VGraph.at(pit->first).position >= VGraph.at(pit->second).position) {
          AddEdgeforVertex(pit->first, pit->second, 0, VGraph);
          AddEdgeforVertex(pit->second, pit->first, 0, VGraph);
        } else {
          AddEdgeforVertex(pit->second, pit->first, 0, VGraph);
          AddEdgeforVertex(pit->first, pit->second, 0, VGraph);
        }
        // * VGraph constraints END
        // Save new symmetry pair according to the topological order
        if( HGraph.at(pit->first).position > HGraph.at(pit->second).position ) {
          tp.first=pit->second; tp.second=pit->first;
        } else if ( HGraph.at(pit->first).position < HGraph.at(pit->second).position ) {
          tp.first=pit->first; tp.second=pit->second;
        } else {
          int choice=rand() % 2;
          switch(choice) {
            case 0: tp.first=pit->first; tp.second=pit->second; break;
            case 1: tp.first=pit->second; tp.second=pit->first; break;
            default:tp.first=pit->first; tp.second=pit->second;
          }
        }
        sympair.push_back(tp);
      } else if(pit->first>(int)caseNL.GetSizeofBlocks() && pit->second>(int)caseNL.GetSizeofBlocks()) {
        // terminal pair
        tp.first=sourceNode; tp.second=sinkNode;
        sympair.push_back(tp);
      }
    }
  } else if(axis==placerDB::H) {
    // Horizontal symmetry axis
    CalculateLongestPath(sourceNode, this->VGraph, false);
    for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(i).sympair.begin(); pit!=caseNL.SBlocks.at(i).sympair.end(); ++pit) {
      if(pit->first<(int)caseNL.GetSizeofBlocks() && pit->second<(int)caseNL.GetSizeofBlocks()) {
        // block pair
        // *  HGraph constraints BEGIN
        CalculateLongestPath(sourceNode, this->HGraph, false);
        if(HGraph.at(pit->first).position >= HGraph.at(pit->second).position) {
          AddEdgeforVertex(pit->first, pit->second, 0, HGraph);
          AddEdgeforVertex(pit->second, pit->first, 0, HGraph);
        } else {
          AddEdgeforVertex(pit->second, pit->first, 0, HGraph);
          AddEdgeforVertex(pit->first, pit->second, 0, HGraph);
        }
        // * HGraph constraints END
        // Save new symmetry pair according to the topological order
        if( VGraph.at(pit->first).position > VGraph.at(pit->second).position ) {
          tp.first=pit->second; tp.second=pit->first;
        } else if ( VGraph.at(pit->first).position < VGraph.at(pit->second).position ) {
          tp.first=pit->first; tp.second=pit->second;
        } else {
          int choice=rand() % 2;
          switch(choice) {
            case 0: tp.first=pit->first; tp.second=pit->second; break;
            case 1: tp.first=pit->second; tp.second=pit->first; break;
            default:tp.first=pit->first; tp.second=pit->second;
          }
        }
        sympair.push_back(tp);
      } else if(pit->first>(int)caseNL.GetSizeofBlocks() && pit->second>(int)caseNL.GetSizeofBlocks()) {
        // terminal pair
        tp.first=sourceNode; tp.second=sinkNode;
        sympair.push_back(tp);
      }
    }
  }
}


void ConstGraph::InitializexL(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis, int i) {
  // Initialzie xL with L1
    if(axis==placerDB::V) {
      // Vertical symmetry axis
      for(int j=0;j<(int)sympair.size();j++) {
        int tmpx=0;
        // x_ij >= w(Yj)
        if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() && sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) { // block pair
          tmpx=HGraph.at(sympair.at(j).second).weight;
        } else if( sympair.at(j).first==sourceNode && sympair.at(j).second==sinkNode ) { // terminal pair
          tmpx=0;
        }
        // L1: Xj(first) -> Yj(second) -> di(axis) -> Xj(first)
        // x_ij >= ( dist(Xj, Yj)+w(Yj) ) / 2
        // forward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->HGraph, false);
        if(HGraph.at(sympair.at(j).second).position!=NINF) {
          int magrin=0;
          if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
            magrin=( HGraph.at(sympair.at(j).second).position + HGraph.at(sympair.at(j).second).weight ) / 2;
          } else if (sympair.at(j).second==sinkNode) { magrin=HGraph.at(sympair.at(j).second).position/2; }
          if(magrin>tmpx) {tmpx=magrin;}
        }
        // backward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->HGraph, true);
        if(HGraph.at(sympair.at(j).second).backpost!=NINF) {
          int magrin=0;
          if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
            magrin=( HGraph.at(sympair.at(j).second).backpost + HGraph.at(sympair.at(j).second).weight ) / 2;
          } else if (sympair.at(j).second==sinkNode) { magrin=HGraph.at(sympair.at(j).second).backpost/2; }
          if(magrin>tmpx) {tmpx=magrin;}
        }
        for(vector< pair<int,placerDB::Smark> >::iterator zit=caseNL.SBlocks.at(i).selfsym.begin(); zit!=caseNL.SBlocks.at(i).selfsym.end(); ++zit) {
          // L1: Xj(first) -> Zk(zit) -> di(axis) -> Xj(first)
          // x_ij >= dist(Xj,Zk)+w(Zk)/2
          // forward graph constraint
          CalculateLongestPath(sympair.at(j).first, this->HGraph, false);
          if( HGraph.at(zit->first).position!=NINF ) {
            int magrin=HGraph.at(zit->first).position;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(zit->first).weight/2;}
            if(magrin>tmpx) {tmpx=magrin;}
          }
          // backward graph constraint
          CalculateLongestPath(sympair.at(j).first, this->HGraph, true);
          if( HGraph.at(zit->first).backpost!=NINF ) {
            int magrin=HGraph.at(zit->first).backpost;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(zit->first).weight/2;}
            if(magrin>tmpx) {tmpx=magrin;}
          }
          // L1: Zk(zit) -> Yj(second) ->di(axis) ->Zk(zit)
          // x_ij >= dist(Zk,Yj)-w(Zk)/2+w(Yj)
          // forward graph constraint
          CalculateLongestPath(zit->first, this->HGraph, false);
          if( HGraph.at(sympair.at(j).second).position != NINF) {
            int magrin=HGraph.at(sympair.at(j).second).position;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin-=HGraph.at(zit->first).weight/2;}
            if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=HGraph.at(sympair.at(j).second).weight; }
            if(magrin>tmpx) {tmpx=magrin;}
          }
          // backward graph constraint
          CalculateLongestPath(zit->first, this->HGraph, true);
          if( HGraph.at(sympair.at(j).second).backpost != NINF) {
            int magrin=HGraph.at(sympair.at(j).second).backpost;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin-=HGraph.at(zit->first).weight/2;}
            if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(j).second).weight; }
            if(magrin>tmpx) {tmpx=magrin;}
          }
        }
        xL.at(j)=tmpx;
      }
    } else if (axis==placerDB::H) {
      // Horizontal symmetry axis
      for(int j=0;j<(int)sympair.size();j++) {
        int tmpx=0;
        // x_ij >= w(Yj)
        if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() && sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) { // block pair
          tmpx=VGraph.at(sympair.at(j).second).weight;
        } else if( sympair.at(j).first==sourceNode && sympair.at(j).second==sinkNode ) { // terminal pair
          tmpx=0;
        }
        // L1: Xj(first) -> Yj(second) -> di(axis) -> Xj(first)
        // x_ij >= ( dist(Xj, Yj)+w(Yj) ) / 2
        // forward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->VGraph, false);
        if(VGraph.at(sympair.at(j).second).position!=NINF) {
          int magrin=0;
          if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
            magrin=( VGraph.at(sympair.at(j).second).position + VGraph.at(sympair.at(j).second).weight ) / 2;
          } else if (sympair.at(j).second==sinkNode) { magrin=VGraph.at(sympair.at(j).second).position/2; }
          if(magrin>tmpx) {tmpx=magrin;}
        }
        // backward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->VGraph, true);
        if(VGraph.at(sympair.at(j).second).backpost!=NINF) {
          int magrin=0;
          if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
            magrin=( VGraph.at(sympair.at(j).second).backpost + VGraph.at(sympair.at(j).second).weight ) / 2;
          } else if (sympair.at(j).second==sinkNode) { magrin=VGraph.at(sympair.at(j).second).backpost/2; }
          if(magrin>tmpx) {tmpx=magrin;}
        }
        for(vector< pair<int,placerDB::Smark> >::iterator zit=caseNL.SBlocks.at(i).selfsym.begin(); zit!=caseNL.SBlocks.at(i).selfsym.end(); ++zit) {
          // L1: Xj(first) -> Zk(zit) -> di(axis) -> Xj(first)
          // x_ij >= dist(Xj,Zk)+w(Zk)/2
          // forward graph constraint
          CalculateLongestPath(sympair.at(j).first, this->VGraph, false);
          if( VGraph.at(zit->first).position!=NINF ) {
            int magrin=VGraph.at(zit->first).position;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(zit->first).weight/2;}
            if(magrin>tmpx) {tmpx=magrin;}
          }
          // backward graph constraint
          CalculateLongestPath(sympair.at(j).first, this->VGraph, true);
          if( VGraph.at(zit->first).backpost!=NINF ) {
            int magrin=VGraph.at(zit->first).backpost;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(zit->first).weight/2;}
            if(magrin>tmpx) {tmpx=magrin;}
          }
          // L1: Zk(zit) -> Yj(second) ->di(axis) ->Zk(zit)
          // x_ij >= dist(Zk,Yj)-w(Zk)/2+w(Yj)
          // forward graph constraint
          CalculateLongestPath(zit->first, this->VGraph, false);
          if( VGraph.at(sympair.at(j).second).position != NINF) {
            int magrin=VGraph.at(sympair.at(j).second).position;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin-=VGraph.at(zit->first).weight/2;}
            if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=VGraph.at(sympair.at(j).second).weight; }
            if(magrin>tmpx) {tmpx=magrin;}
          }
          // backward graph constraint
          CalculateLongestPath(zit->first, this->VGraph, true);
          if( VGraph.at(sympair.at(j).second).backpost != NINF) {
            int magrin=VGraph.at(sympair.at(j).second).backpost;
            if(zit->first<(int)caseNL.GetSizeofBlocks()) {magrin-=VGraph.at(zit->first).weight/2;}
            if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(j).second).weight; }
            if(magrin>tmpx) {tmpx=magrin;}
          }
        }
        xL.at(j)=tmpx;
      }
    }
}

bool ConstGraph::SymmetryConstraintCoreAxisCenter(design& caseNL, placerDB::Smark axis, int i) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.SymmetryConstraintCoreAxisCenter");

  vector< pair<int,int> > sympair;
  vector<int> xL, slack, Lslack; 
  pair<int,int> tp;
  pair<int,int> vio;
  int dnode;
    // for i-th symmetry group
    //axis=caseSP.GetSymmBlockAxis(i);
    dnode=caseNL.SBlocks.at(i).dnode;
    sympair.clear(); xL.clear(); slack.clear(); Lslack.clear();

    // first, keep all symmetry pairs aligned in vertical graph and reorganize the symmetry pairs
    AlignReorganize(caseNL, sympair, axis, i);
    xL.resize(sympair.size());
    slack.resize(sympair.size());
    Lslack.resize(sympair.size());

    // second, add edges for symmetry pairs in horizontal graph
    // 1. Initialize xL by L1 constraints
    InitializexL(caseNL, sympair, xL, axis, i);
    // 2. Update xL according to L3 constraints
    UpdatexLwithL3(caseNL, sympair, xL, axis);
    // 3. Generate slack(x)
    slack=GenerateSlack(xL);
    // 4. Initialze largest possible slack Lslack(x)
    for(int j=0;j<(int)sympair.size(); j++) 
      Lslack.at(j)=-1*NINF;
    // 5. Update Lslack(x) according to U1,U2
    for(int j=0;j<(int)sympair.size(); j++) 
      UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
    if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
    // 6. while some constraints in L2 are not satisfied
    while( (vio=CheckIfL2Violation(caseNL, sympair, xL, axis)).first !=-1 ) {
     // for any violation on L2 constraint x+y>=b
      if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      // if x+y<b
      // x = min{x+slack(x), x+Lslack(x), b-y}
      int newxL=xL.at(vio.first)+slack.at(vio.first);
      if( xL.at(vio.first)+Lslack.at(vio.first)<newxL ) {newxL=xL.at(vio.first)+Lslack.at(vio.first);}
      int B_y=CalculateBminusY(caseNL, sympair, xL, vio.first, vio.second, axis);
      if( B_y<newxL ) {newxL=B_y;}
      xL.at(vio.first)=newxL;
      // Update xL list
      UpdatexLwithL3(caseNL, sympair, xL, axis);
      // Update Lslack list
      for(int j=0;j<(int)sympair.size(); j++) 
        UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
      // Update slack list
      slack.clear(); slack=GenerateSlack(xL);
      //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints

      if( CheckIfSingleL2Violation(caseNL, sympair, xL, vio.first, vio.second, axis) ) {
        // y = min{y+slack(y), y+Lslack(y), b-x}
        int newxL=xL.at(vio.second)+slack.at(vio.second);
        if( xL.at(vio.second)+Lslack.at(vio.second)<newxL ) {newxL=xL.at(vio.second)+Lslack.at(vio.second);}
        int B_y=CalculateBminusY(caseNL, sympair, xL, vio.second, vio.first, axis);
        if( B_y<newxL ) {newxL=B_y;}
        xL.at(vio.second)=newxL;
        // Update xL list
        UpdatexLwithL3(caseNL, sympair, xL, axis);
        // Update Lslack list
        for(int j=0;j<(int)sympair.size(); j++) 
          UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
        // Update slack list
        slack.clear(); slack=GenerateSlack(xL);
        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      }

      if( CheckIfSingleL2Violation(caseNL, sympair, xL, vio.first, vio.second, axis) ) {
        // x, y = (b-x-y)/2
        int B_x_y=CalculateBminusXminusY(caseNL, sympair, xL, vio.first, vio.second, axis) / 2;
        xL.at(vio.first)+=B_x_y;
        xL.at(vio.second)+=B_x_y;
        // Update xL list
        UpdatexLwithL3(caseNL, sympair, xL, axis);
        // Update Lslack list
        for(int j=0;j<(int)sympair.size(); j++) 
          UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
        // Update slack list
        slack.clear(); slack=GenerateSlack(xL);
        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      }
    }
    // 7. Add edges for symmetry pairs
    for(int j=0;j<(int)sympair.size();j++) {
      if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() && sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
         if(axis==placerDB::V) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j)-HGraph.at(sympair.at(j).second).weight, HGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j)+HGraph.at(sympair.at(j).second).weight, HGraph);
         } else if(axis==placerDB::H) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j)-VGraph.at(sympair.at(j).second).weight, VGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j)+VGraph.at(sympair.at(j).second).weight, VGraph);
         }
      } else if (sympair.at(j).first==sourceNode && sympair.at(j).second==sinkNode) {
         if(axis==placerDB::V) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j), HGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j), HGraph);
         } else if(axis==placerDB::H) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j), VGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j), VGraph);
         }
      }
    }

    //cout<<"xL:";
    //for(vector<int>::iterator tmpit=xL.begin(); tmpit!=xL.end(); ++tmpit) {cout<<" "<<*tmpit;}
    //cout<<endl;
    //cout<<"slack:";
    //for(vector<int>::iterator tmpit=slack.begin(); tmpit!=slack.end(); ++tmpit) {cout<<" "<<*tmpit;}
    //cout<<endl;
    //cout<<"Lslack:";
    //for(vector<int>::iterator tmpit=Lslack.begin(); tmpit!=Lslack.end(); ++tmpit) {cout<<" "<<*tmpit;}
    //cout<<endl;

    // third, add edges for self-symmetric blocks in horizontal graph
    if(axis==placerDB::V) {
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(i).selfsym.begin(); sit!=caseNL.SBlocks.at(i).selfsym.end(); ++sit) {
        if(sit->first>=(int)caseNL.GetSizeofBlocks()) {continue;}
        CalculateLongestPath(sourceNode, this->HGraph, false);
        if(HGraph.at(sit->first).position+HGraph.at(sit->first).weight/2 >= HGraph.at(dnode).position) {
          AddEdgeforVertex(sit->first, dnode, HGraph.at(sit->first).weight/2, HGraph);
          AddEdgeforVertex(dnode, sit->first, -1*HGraph.at(sit->first).weight/2, HGraph);
        } else {
          AddEdgeforVertex(dnode, sit->first, -1*HGraph.at(sit->first).weight/2, HGraph);
          AddEdgeforVertex(sit->first, dnode, HGraph.at(sit->first).weight/2, HGraph);
        }
      }
    } else if (axis==placerDB::H) {
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(i).selfsym.begin(); sit!=caseNL.SBlocks.at(i).selfsym.end(); ++sit) {
        if(sit->first>=(int)caseNL.GetSizeofBlocks()) {continue;}
        CalculateLongestPath(sourceNode, this->VGraph, false);
        if(VGraph.at(sit->first).position+VGraph.at(sit->first).weight/2 >= VGraph.at(dnode).position) {
          AddEdgeforVertex(sit->first, dnode, VGraph.at(sit->first).weight/2, VGraph);
          AddEdgeforVertex(dnode, sit->first, -1*VGraph.at(sit->first).weight/2, VGraph);
        } else {
          AddEdgeforVertex(dnode, sit->first, -1*VGraph.at(sit->first).weight/2, VGraph);
          AddEdgeforVertex(sit->first, dnode, VGraph.at(sit->first).weight/2, VGraph);
        }
      }
    }
    logger->debug("After symmetry check");
    CalculateLongestPath(sourceNode, this->HGraph, false);
    //std::cout<<"Vgraph\n";
    CalculateLongestPath(sourceNode, this->VGraph, false);
    PrintConstGraph();
    // forth, revise edges
    for(int j=0;j<(int)sympair.size();j++) {
      if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() && sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
         if(axis==placerDB::V) {
           if(HGraph.at(dnode).precedent!=sympair.at(j).first) {
             ReverseEdge(sympair.at(j).first, dnode, HGraph);
             ReverseEdge(dnode, sympair.at(j).first, HGraph);
           }
         } else if(axis==placerDB::H) {
           if(VGraph.at(dnode).precedent!=sympair.at(j).first) {
             ReverseEdge(sympair.at(j).first, dnode, VGraph);
             ReverseEdge(dnode, sympair.at(j).first, VGraph);
           }
         }
      }
    }
  return true;
}

void ConstGraph::ReverseEdge(int current, int next, vector<Vertex>& graph) {
  for(int i=0;i<(int)graph.at(current).Edges.size();i++) {
    if(graph.at(current).Edges.at(i).next==next) {
      //graph.at(current).Edges.at(i).weight*=-1;
      if(graph.at(current).Edges.at(i).isBackward) { graph.at(current).Edges.at(i).isBackward=false;
      } else { graph.at(current).Edges.at(i).isBackward=true;}
      break;
    }
  }
}

bool ConstGraph::SymmetryConstraintCore(design& caseNL, placerDB::Smark axis, int i) {
  vector< pair<int,int> > sympair;
  vector<int> xL, slack, Lslack; 
  pair<int,int> tp;
  pair<int,int> vio;
  int dnode;
    // for i-th symmetry group
    //axis=caseSP.GetSymmBlockAxis(i);
    dnode=caseNL.SBlocks.at(i).dnode;
    sympair.clear(); xL.clear(); slack.clear(); Lslack.clear();

    // first, keep all symmetry pairs aligned in vertical graph and reorganize the symmetry pairs
    AlignReorganize(caseNL, sympair, axis, i);
    xL.resize(sympair.size());
    slack.resize(sympair.size());
    Lslack.resize(sympair.size());

    // second, add edges for symmetry pairs in horizontal graph
    // 1. Initialize xL by L1 constraints
    InitializexL(caseNL, sympair, xL, axis, i);
    // 2. Update xL according to L3 constraints
    UpdatexLwithL3(caseNL, sympair, xL, axis);
    // 3. Generate slack(x)
    slack=GenerateSlack(xL);
    // 4. Initialze largest possible slack Lslack(x)
    for(int j=0;j<(int)sympair.size(); j++) 
      Lslack.at(j)=-1*NINF;
    // 5. Update Lslack(x) according to U1,U2
    for(int j=0;j<(int)sympair.size(); j++) 
      UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
    if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
    // 6. while some constraints in L2 are not satisfied
    while( (vio=CheckIfL2Violation(caseNL, sympair, xL, axis)).first !=-1 ) {
     // for any violation on L2 constraint x+y>=b
      if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      // if x+y<b
      // x = min{x+slack(x), x+Lslack(x), b-y}
      int newxL=xL.at(vio.first)+slack.at(vio.first);
      if( xL.at(vio.first)+Lslack.at(vio.first)<newxL ) {newxL=xL.at(vio.first)+Lslack.at(vio.first);}
      int B_y=CalculateBminusY(caseNL, sympair, xL, vio.first, vio.second, axis);
      if( B_y<newxL ) {newxL=B_y;}
      xL.at(vio.first)=newxL;
      // Update xL list
      UpdatexLwithL3(caseNL, sympair, xL, axis);
      // Update Lslack list
      for(int j=0;j<(int)sympair.size(); j++) 
        UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
      // Update slack list
      slack.clear(); slack=GenerateSlack(xL);
      //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints

      if( CheckIfSingleL2Violation(caseNL, sympair, xL, vio.first, vio.second, axis) ) {
        // y = min{y+slack(y), y+Lslack(y), b-x}
        int newxL=xL.at(vio.second)+slack.at(vio.second);
        if( xL.at(vio.second)+Lslack.at(vio.second)<newxL ) {newxL=xL.at(vio.second)+Lslack.at(vio.second);}
        int B_y=CalculateBminusY(caseNL, sympair, xL, vio.second, vio.first, axis);
        if( B_y<newxL ) {newxL=B_y;}
        xL.at(vio.second)=newxL;
        // Update xL list
        UpdatexLwithL3(caseNL, sympair, xL, axis);
        // Update Lslack list
        for(int j=0;j<(int)sympair.size(); j++) 
          UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
        // Update slack list
        slack.clear(); slack=GenerateSlack(xL);
        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      }

      if( CheckIfSingleL2Violation(caseNL, sympair, xL, vio.first, vio.second, axis) ) {
        // x, y = (b-x-y)/2
        int B_x_y=CalculateBminusXminusY(caseNL, sympair, xL, vio.first, vio.second, axis) / 2;
        xL.at(vio.first)+=B_x_y;
        xL.at(vio.second)+=B_x_y;
        // Update xL list
        UpdatexLwithL3(caseNL, sympair, xL, axis);
        // Update Lslack list
        for(int j=0;j<(int)sympair.size(); j++) 
          UpdateLslackElement(caseNL, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
        // Update slack list
        slack.clear(); slack=GenerateSlack(xL);
        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      }
    }
    // 7. Add edges for symmetry pairs
    for(unsigned int j=0;j<sympair.size();j++) {
      if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() && sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
         if(axis==placerDB::V) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j)-HGraph.at(sympair.at(j).second).weight, HGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j)+HGraph.at(sympair.at(j).second).weight, HGraph);
         } else if(axis==placerDB::H) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j)-VGraph.at(sympair.at(j).second).weight, VGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j)+VGraph.at(sympair.at(j).second).weight, VGraph);
         }
      } else if (sympair.at(j).first==sourceNode && sympair.at(j).second==sinkNode) {
         if(axis==placerDB::V) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), HGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j), HGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j), HGraph);
         } else if(axis==placerDB::H) {
           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), VGraph);
           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j), VGraph);
           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j), VGraph);
         }
      }
    }

    //cout<<"xL:";
    //for(vector<int>::iterator tmpit=xL.begin(); tmpit!=xL.end(); ++tmpit) {cout<<" "<<*tmpit;}
    //cout<<endl;
    //cout<<"slack:";
    //for(vector<int>::iterator tmpit=slack.begin(); tmpit!=slack.end(); ++tmpit) {cout<<" "<<*tmpit;}
    //cout<<endl;
    //cout<<"Lslack:";
    //for(vector<int>::iterator tmpit=Lslack.begin(); tmpit!=Lslack.end(); ++tmpit) {cout<<" "<<*tmpit;}
    //cout<<endl;

    // third, add edges for self-symmetric blocks in horizontal graph
    if(axis==placerDB::V) {
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(i).selfsym.begin(); sit!=caseNL.SBlocks.at(i).selfsym.end(); ++sit) {
        if(sit->first>=(int)caseNL.GetSizeofBlocks()) {continue;}
        CalculateLongestPath(sourceNode, this->HGraph, false);
        if(HGraph.at(sit->first).position+HGraph.at(sit->first).weight/2 >= HGraph.at(dnode).position) {
          AddEdgeforVertex(sit->first, dnode, HGraph.at(sit->first).weight/2, HGraph);
          AddEdgeforVertex(dnode, sit->first, -1*HGraph.at(sit->first).weight/2, HGraph);
        } else {
          AddEdgeforVertex(dnode, sit->first, -1*HGraph.at(sit->first).weight/2, HGraph);
          AddEdgeforVertex(sit->first, dnode, HGraph.at(sit->first).weight/2, HGraph);
        }
      }
      CalculateLongestPath(sourceNode, this->HGraph, false);
      CalculateLongestPath(sourceNode, this->HGraph, true);
    } else if (axis==placerDB::H) {
      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(i).selfsym.begin(); sit!=caseNL.SBlocks.at(i).selfsym.end(); ++sit) {
        if(sit->first>=(int)caseNL.GetSizeofBlocks()) {continue;}
        CalculateLongestPath(sourceNode, this->VGraph, false);
        if(VGraph.at(sit->first).position+VGraph.at(sit->first).weight/2 >= VGraph.at(dnode).position) {
          AddEdgeforVertex(sit->first, dnode, VGraph.at(sit->first).weight/2, VGraph);
          AddEdgeforVertex(dnode, sit->first, -1*VGraph.at(sit->first).weight/2, VGraph);
        } else {
          AddEdgeforVertex(dnode, sit->first, -1*VGraph.at(sit->first).weight/2, VGraph);
          AddEdgeforVertex(sit->first, dnode, VGraph.at(sit->first).weight/2, VGraph);
        }
      }
      CalculateLongestPath(sourceNode, this->VGraph, false);
      CalculateLongestPath(sourceNode, this->VGraph, true);
    }
  return true;
}

void ConstGraph::OtherGeometricConstraintCore(design& caseNL) {
  if(!caseNL.Align_blocks.empty()) {
    for(unsigned int i=0;i<caseNL.Align_blocks.size();i++) {
      if(caseNL.Align_blocks.at(i).horizon==1) { // horizontal
        CalculateLongestPath(sourceNode, this->VGraph, false);
        int LL=INT_MIN, MM=-1;
        for(unsigned int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
          if(VGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position>LL) {
            MM=caseNL.Align_blocks.at(i).blocks.at(j);
            LL=VGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position;
          }
        }
        for(unsigned int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
          if(caseNL.Align_blocks.at(i).blocks.at(j)!=MM) {
            AddEdgeforVertex(MM, caseNL.Align_blocks.at(i).blocks.at(j), 0, VGraph);
            AddEdgeforVertex(caseNL.Align_blocks.at(i).blocks.at(j), MM, 0, VGraph);
          }
        }
      } else if(caseNL.Align_blocks.at(i).horizon==0)  { // veritcal
        CalculateLongestPath(sourceNode, this->HGraph, false);
        int LL=INT_MIN, MM=-1;
        for(unsigned int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
          if(HGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position>LL) {
            MM=caseNL.Align_blocks.at(i).blocks.at(j);
            LL=HGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position;
          }
        }
        for(unsigned int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
          if(caseNL.Align_blocks.at(i).blocks.at(j)!=MM) {
            AddEdgeforVertex(MM, caseNL.Align_blocks.at(i).blocks.at(j), 0, HGraph);
            AddEdgeforVertex(caseNL.Align_blocks.at(i).blocks.at(j), MM, 0, HGraph);
          }
        }
      }
    }
  } 
  //added by yg
  //adding edges for preplace, abument, and alignment
  if(!caseNL.Preplace_blocks.empty()){
      for(unsigned int i=0;i<caseNL.Preplace_blocks.size();i++){
	  //AddEdgeforVertex(sourceNode, caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].distance, VGraph);  
          //cout<<"adds a preblaced blocks"<<endl;
          if(caseNL.Preplace_blocks[i].horizon==0)
          AddEdgeforVertex(caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].blockid2, caseNL.Preplace_blocks[i].distance, VGraph);
           else
           AddEdgeforVertex(caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].blockid2, caseNL.Preplace_blocks[i].distance, HGraph);
	  }
  }
  if(!caseNL.Alignment_blocks.empty()){
	  for(unsigned int i=0;i<caseNL.Alignment_blocks.size();i++){
//cout<<"adds a alignment blocks"<<endl;
                  if(caseNL.Alignment_blocks[i].horizon==0)
		  AddEdgeforVertex(caseNL.Alignment_blocks[i].blockid1, caseNL.Alignment_blocks[i].blockid2, caseNL.Alignment_blocks[i].distance, VGraph);
		   else
                   AddEdgeforVertex(caseNL.Alignment_blocks[i].blockid1, caseNL.Alignment_blocks[i].blockid2, caseNL.Alignment_blocks[i].distance, HGraph);
	  }
  }
  // Following codes need to be updated if used in the future - AspectRatio feature 20190629 wbxu
//  if(!caseNL.Abument_blocks.empty()){
//          for(int i=0;i<caseNL.Abument_blocks.size();i++){
////cout<<"adds a abument blocks"<<endl;
//        	if(caseNL.Abument_blocks[i].horizon==0){
//        	  AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Abument_blocks[i].distance, VGraph);
//                 AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Blocks[caseNL.Abument_blocks[i].blockid1].width, HGraph);
//                     }
//else
//{
//AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Abument_blocks[i].distance, HGraph);
//                 AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Blocks[caseNL.Abument_blocks[i].blockid1].height, VGraph);
//}
//          }
//
//  }


}

bool ConstGraph::ConstraintGraphAP(design& caseNL, Aplace& caseAP) {
  placerDB::Smark axis;
  //vector< pair<int,int> > sympair;
  //vector<int> xL, slack, Lslack; 
  //pair<int,int> tp;
  //pair<int,int> vio;
  //int dnode;
  /* initialize random seed: */
  //srand(time(NULL));
  for(int i=0;i<(int)caseNL.SBlocks.size();i++) {
    axis=caseAP.GetSBlockDir(i);
    if(!SymmetryConstraintCoreAxisCenter(caseNL, axis, i)) {return false;}
  }

  //cout<<!caseNL.Preplace_blocks.empty()<<endl;
  OtherGeometricConstraintCore(caseNL);

  return true;
}

bool ConstGraph::ConstraintGraph(design& caseNL, SeqPair& caseSP) {
  placerDB::Smark axis;
  //vector< pair<int,int> > sympair;
  //vector<int> xL, slack, Lslack; 
  //pair<int,int> tp;
  //pair<int,int> vio;
  //int dnode;
  /* initialize random seed: */
  //srand(time(NULL));
  for(int i=0;i<(int)caseNL.SBlocks.size();i++) {
    axis=caseSP.GetSymmBlockAxis(i);
    if(!SymmetryConstraintCore(caseNL, axis, i)) {return false;}
  }

  //cout<<!caseNL.Preplace_blocks.empty()<<endl;
  OtherGeometricConstraintCore(caseNL);

  return true;
}

//bool ConstGraph::ConstraintGraph(design& caseNL, SeqPair& caseSP) {
//  placerDB::Smark axis;
//  vector< pair<int,int> > sympair;
//  vector<int> xL, slack, Lslack; 
//  pair<int,int> tp;
//  pair<int,int> vio;
//  //int dnode;
//  /* initialize random seed: */
//  //srand(time(NULL));
//  for(int i=0;i<(int)caseNL.SBlocks.size();i++) {
//    // for i-th symmetry group
//    axis=caseSP.GetSymmBlockAxis(i);
//    int dnode=caseNL.SBlocks.at(i).dnode;
//    sympair.clear(); xL.clear(); slack.clear(); Lslack.clear();
//
//    // first, keep all symmetry pairs aligned in vertical graph and reorganize the symmetry pairs
//    AlignReorganize(caseNL, sympair, axis, i);
//    xL.resize(sympair.size());
//    slack.resize(sympair.size());
//    Lslack.resize(sympair.size());
//
//    // second, add edges for symmetry pairs in horizontal graph
//    // 1. Initialize xL by L1 constraints
//    InitializexL(caseNL, sympair, xL, axis, i);
//    // 2. Update xL according to L3 constraints
//    UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
//    // 3. Generate slack(x)
//    slack=GenerateSlack(xL);
//    // 4. Initialze largest possible slack Lslack(x)
//    for(int j=0;j<(int)sympair.size(); j++) 
//      Lslack.at(j)=-1*NINF;
//    // 5. Update Lslack(x) according to U1,U2
//    for(int j=0;j<(int)sympair.size(); j++) 
//      UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
//    if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
//    // 6. while some constraints in L2 are not satisfied
//    while( (vio=CheckIfL2Violation(caseNL, caseSP, sympair, xL, axis)).first !=-1 ) {
//     // for any violation on L2 constraint x+y>=b
//      if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
//      // if x+y<b
//      // x = min{x+slack(x), x+Lslack(x), b-y}
//      int newxL=xL.at(vio.first)+slack.at(vio.first);
//      if( xL.at(vio.first)+Lslack.at(vio.first)<newxL ) {newxL=xL.at(vio.first)+Lslack.at(vio.first);}
//      int B_y=CalculateBminusY(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis);
//      if( B_y<newxL ) {newxL=B_y;}
//      xL.at(vio.first)=newxL;
//      // Update xL list
//      UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
//      // Update Lslack list
//      for(int j=0;j<(int)sympair.size(); j++) 
//        UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
//      // Update slack list
//      slack.clear(); slack=GenerateSlack(xL);
//      //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
//
//      if( CheckIfSingleL2Violation(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis) ) {
//        // y = min{y+slack(y), y+Lslack(y), b-x}
//        int newxL=xL.at(vio.second)+slack.at(vio.second);
//        if( xL.at(vio.second)+Lslack.at(vio.second)<newxL ) {newxL=xL.at(vio.second)+Lslack.at(vio.second);}
//        int B_y=CalculateBminusY(caseNL, caseSP, sympair, xL, vio.second, vio.first, axis);
//        if( B_y<newxL ) {newxL=B_y;}
//        xL.at(vio.second)=newxL;
//        // Update xL list
//        UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
//        // Update Lslack list
//        for(int j=0;j<(int)sympair.size(); j++) 
//          UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
//        // Update slack list
//        slack.clear(); slack=GenerateSlack(xL);
//        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
//      }
//
//      if( CheckIfSingleL2Violation(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis) ) {
//        // x, y = (b-x-y)/2
//        int B_x_y=CalculateBminusXminusY(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis) / 2;
//        xL.at(vio.first)+=B_x_y;
//        xL.at(vio.second)+=B_x_y;
//        // Update xL list
//        UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
//        // Update Lslack list
//        for(int j=0;j<(int)sympair.size(); j++) 
//          UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
//        // Update slack list
//        slack.clear(); slack=GenerateSlack(xL);
//        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
//      }
//    }
//    // 7. Add edges for symmetry pairs
//    for(int j=0;j<(int)sympair.size();j++) {
//      if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() && sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
//         if(axis==placerDB::V) {
//           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), HGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), HGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j)-HGraph.at(sympair.at(j).second).weight, HGraph);
//           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j)+HGraph.at(sympair.at(j).second).weight, HGraph);
//         } else if(axis==placerDB::H) {
//           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), VGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), VGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j)-VGraph.at(sympair.at(j).second).weight, VGraph);
//           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j)+VGraph.at(sympair.at(j).second).weight, VGraph);
//         }
//      } else if (sympair.at(j).first==sourceNode && sympair.at(j).second==sinkNode) {
//         if(axis==placerDB::V) {
//           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), HGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), HGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j), HGraph);
//           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j), HGraph);
//         } else if(axis==placerDB::H) {
//           AddEdgeforVertex(sympair.at(j).first, dnode, xL.at(j), VGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).first, -1*xL.at(j), VGraph);
//           AddEdgeforVertex(dnode, sympair.at(j).second, xL.at(j), VGraph);
//           AddEdgeforVertex(sympair.at(j).second, dnode, -1*xL.at(j), VGraph);
//         }
//      }
//    }
//
//    //cout<<"xL:";
//    //for(vector<int>::iterator tmpit=xL.begin(); tmpit!=xL.end(); ++tmpit) {cout<<" "<<*tmpit;}
//    //cout<<endl;
//    //cout<<"slack:";
//    //for(vector<int>::iterator tmpit=slack.begin(); tmpit!=slack.end(); ++tmpit) {cout<<" "<<*tmpit;}
//    //cout<<endl;
//    //cout<<"Lslack:";
//    //for(vector<int>::iterator tmpit=Lslack.begin(); tmpit!=Lslack.end(); ++tmpit) {cout<<" "<<*tmpit;}
//    //cout<<endl;
//
//    // third, add edges for self-symmetric blocks in horizontal graph
//    if(axis==placerDB::V) {
//      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(i).selfsym.begin(); sit!=caseNL.SBlocks.at(i).selfsym.end(); ++sit) {
//        if(sit->first>=(int)caseNL.GetSizeofBlocks()) {continue;}
//        CalculateLongestPath(sourceNode, this->HGraph, false);
//        if(HGraph.at(sit->first).position+HGraph.at(sit->first).weight/2 >= HGraph.at(dnode).position) {
//          AddEdgeforVertex(sit->first, dnode, HGraph.at(sit->first).weight/2, HGraph);
//          AddEdgeforVertex(dnode, sit->first, -1*HGraph.at(sit->first).weight/2, HGraph);
//        } else {
//          AddEdgeforVertex(dnode, sit->first, -1*HGraph.at(sit->first).weight/2, HGraph);
//          AddEdgeforVertex(sit->first, dnode, HGraph.at(sit->first).weight/2, HGraph);
//        }
//      }
//    } else if (axis==placerDB::H) {
//      for(vector< pair<int,placerDB::Smark> >::iterator sit=caseNL.SBlocks.at(i).selfsym.begin(); sit!=caseNL.SBlocks.at(i).selfsym.end(); ++sit) {
//        if(sit->first>=(int)caseNL.GetSizeofBlocks()) {continue;}
//        CalculateLongestPath(sourceNode, this->VGraph, false);
//        if(VGraph.at(sit->first).position+VGraph.at(sit->first).weight/2 >= VGraph.at(dnode).position) {
//          AddEdgeforVertex(sit->first, dnode, VGraph.at(sit->first).weight/2, VGraph);
//          AddEdgeforVertex(dnode, sit->first, -1*VGraph.at(sit->first).weight/2, VGraph);
//        } else {
//          AddEdgeforVertex(dnode, sit->first, -1*VGraph.at(sit->first).weight/2, VGraph);
//          AddEdgeforVertex(sit->first, dnode, VGraph.at(sit->first).weight/2, VGraph);
//        }
//      }
//    }
//  }
//
//  //cout<<!caseNL.Preplace_blocks.empty()<<endl;
//  if(!caseNL.Align_blocks.empty()) {
//    for(int i=0;i<caseNL.Align_blocks.size();i++) {
//      if(caseNL.Align_blocks.at(i).horizon==1) { // horizontal
//        CalculateLongestPath(sourceNode, this->VGraph, false);
//        int LL=INT_MIN, MM=-1;
//        for(int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
//          if(VGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position>LL) {
//            MM=caseNL.Align_blocks.at(i).blocks.at(j);
//            LL=VGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position;
//          }
//        }
//        for(int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
//          if(caseNL.Align_blocks.at(i).blocks.at(j)!=MM) {
//            AddEdgeforVertex(MM, caseNL.Align_blocks.at(i).blocks.at(j), 0, VGraph);
//            AddEdgeforVertex(caseNL.Align_blocks.at(i).blocks.at(j), MM, 0, VGraph);
//          }
//        }
//      } else if(caseNL.Align_blocks.at(i).horizon==0)  { // veritcal
//        CalculateLongestPath(sourceNode, this->HGraph, false);
//        int LL=INT_MIN, MM=-1;
//        for(int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
//          if(HGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position>LL) {
//            MM=caseNL.Align_blocks.at(i).blocks.at(j);
//            LL=HGraph.at(caseNL.Align_blocks.at(i).blocks.at(j)).position;
//          }
//        }
//        for(int j=0;j<caseNL.Align_blocks.at(i).blocks.size();j++) {
//          if(caseNL.Align_blocks.at(i).blocks.at(j)!=MM) {
//            AddEdgeforVertex(MM, caseNL.Align_blocks.at(i).blocks.at(j), 0, HGraph);
//            AddEdgeforVertex(caseNL.Align_blocks.at(i).blocks.at(j), MM, 0, HGraph);
//          }
//        }
//      }
//    }
//  } 
//  //added by yg
//  //adding edges for preplace, abument, and alignment
//  if(!caseNL.Preplace_blocks.empty()){
//      for(int i=0;i<caseNL.Preplace_blocks.size();i++){
//	  //AddEdgeforVertex(sourceNode, caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].distance, VGraph);  
//          //cout<<"adds a preblaced blocks"<<endl;
//          if(caseNL.Preplace_blocks[i].horizon==0)
//          AddEdgeforVertex(caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].blockid2, caseNL.Preplace_blocks[i].distance, VGraph);
//           else
//           AddEdgeforVertex(caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].blockid2, caseNL.Preplace_blocks[i].distance, HGraph);
//	  }
//  }
//  if(!caseNL.Alignment_blocks.empty()){
//	  for(int i=0;i<caseNL.Alignment_blocks.size();i++){
////cout<<"adds a alignment blocks"<<endl;
//                  if(caseNL.Alignment_blocks[i].horizon==0)
//		  AddEdgeforVertex(caseNL.Alignment_blocks[i].blockid1, caseNL.Alignment_blocks[i].blockid2, caseNL.Alignment_blocks[i].distance, VGraph);
//		   else
//                   AddEdgeforVertex(caseNL.Alignment_blocks[i].blockid1, caseNL.Alignment_blocks[i].blockid2, caseNL.Alignment_blocks[i].distance, HGraph);
//	  }
//  }
//  if(!caseNL.Abument_blocks.empty()){
//	  for(int i=0;i<caseNL.Abument_blocks.size();i++){
////cout<<"adds a abument blocks"<<endl;
//		if(caseNL.Abument_blocks[i].horizon==0){
//		  AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Abument_blocks[i].distance, VGraph);
//                 AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Blocks[caseNL.Abument_blocks[i].blockid1].width, HGraph);
//                     }
//else
//{
//AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Abument_blocks[i].distance, HGraph);
//                 AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Blocks[caseNL.Abument_blocks[i].blockid1].height, VGraph);
//}
//	  }
//
//  }
//
//
//
//  return true;
//}

void ConstGraph::UpdatexLwithL3(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis) {
  for(int j=0;j<(int)sympair.size();j++) {
    for(int k=0;k<(int)sympair.size();k++) {
      if(j==k) {continue;}
      if(axis==placerDB::V) {
      // Vertical symmetry axis
        // L3: Xj(j.first) -> Xk(k.first) -> di(axis) -> Xj(j.first)
        // x_ij >= dist(Xj, Xk) + x_ik
        // forward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->HGraph, false);
        if(HGraph.at(sympair.at(k).first).position!=NINF) {
          int magrin=HGraph.at(sympair.at(k).first).position+xL.at(k);
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
        // backward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->HGraph, true);
        if(HGraph.at(sympair.at(k).first).backpost!=NINF) {
          int magrin=HGraph.at(sympair.at(k).first).backpost+xL.at(k);
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
        // L3: Yj(j.second) -> di(axis) -> Yk(k.second) -> Yj(j.second)
        // x_ij >= x_ik + w(Yj) - w(Yk) + dist(Yk, Yj);
        // forward graph constraint
        CalculateLongestPath(sympair.at(k).second, this->HGraph, false);
        if(HGraph.at(sympair.at(j).second).position!=NINF) {
          int magrin=xL.at(k)+HGraph.at(sympair.at(j).second).position;
          if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=HGraph.at(sympair.at(j).second).weight; }
          //if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=caseNL.GetBlockWidth(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
          if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=HGraph.at(sympair.at(k).second).weight; }
          //if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second)); }
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
        // backward graph constraint
        CalculateLongestPath(sympair.at(k).second, this->HGraph, true);
        if(HGraph.at(sympair.at(j).second).backpost!=NINF) {
          int magrin=xL.at(k)+HGraph.at(sympair.at(j).second).backpost;
          if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=HGraph.at(sympair.at(j).second).weight; }
          //if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=caseNL.GetBlockWidth(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
          if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=HGraph.at(sympair.at(k).second).weight; }
          //if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second)); }
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
      } else if(axis==placerDB::H) {
      // Horizontal symmetry axis
        // L3: Xj(j.first) -> Xk(k.first) -> di(axis) -> Xj(j.first)
        // x_ij >= dist(Xj, Xk) + x_ik
        // forward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->VGraph, false);
        if(VGraph.at(sympair.at(k).first).position!=NINF) {
          int magrin=VGraph.at(sympair.at(k).first).position+xL.at(k);
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
        // backward graph constraint
        CalculateLongestPath(sympair.at(j).first, this->VGraph, true);
        if(VGraph.at(sympair.at(k).first).backpost!=NINF) {
          int magrin=VGraph.at(sympair.at(k).first).backpost+xL.at(k);
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
        // L3: Yj(j.second) -> di(axis) -> Yk(k.second) -> Yj(j.second)
        // x_ij >= x_ik + w(Yj) - w(Yk) + dist(Yk, Yj);
        // forward graph constraint
        CalculateLongestPath(sympair.at(k).second, this->VGraph, false);
        if(VGraph.at(sympair.at(j).second).position!=NINF) {
          int magrin=xL.at(k)+VGraph.at(sympair.at(j).second).position;
          if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=VGraph.at(sympair.at(j).second).weight; }
          //if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=caseNL.GetBlockHeight(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
          if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=VGraph.at(sympair.at(k).second).weight; }
          //if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second)); }
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
        // backward graph constraint
        CalculateLongestPath(sympair.at(k).second, this->VGraph, true);
        if(VGraph.at(sympair.at(j).second).backpost!=NINF) {
          int magrin=xL.at(k)+VGraph.at(sympair.at(j).second).backpost;
          if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=VGraph.at(sympair.at(j).second).weight; }
          //if( sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) {magrin+=caseNL.GetBlockHeight(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
          if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=VGraph.at(sympair.at(k).second).weight; }
          //if( sympair.at(k).second<(int)caseNL.GetSizeofBlocks() ) {magrin-=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second)); }
          if(magrin>xL.at(j)) {xL.at(j)=magrin;}
        }
      }
    }
  }
}

int ConstGraph::CalculateBminusXminusY(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis) {
  int M=-1;
  if(axis==placerDB::V) { // vertical symmetry
    // L2: Xj(j.first) -> Yk(k.second) -> di(axis) -> Xj(j.first)
    // x_ij + x_ik >= w(Yk) + dist(Xj,Yk)  
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->HGraph, false);
    if(HGraph.at(sympair.at(k).second).position!=NINF) {
      int magrin=HGraph.at(sympair.at(k).second).position;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) { M=magrin-xL.at(k)-xL.at(j); }
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->HGraph, true);
    if(HGraph.at(sympair.at(k).second).backpost!=NINF) {
      int magrin=HGraph.at(sympair.at(k).second).backpost;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) { M=magrin-xL.at(k)-xL.at(j); }
    }
  } else { // horizontal symmetry
    // L2: Xj(j.first) -> Yk(k.second) -> di(axis) -> Xj(j.first)
    // x_ij + x_ik >= w(Yk) + dist(Xj,Yk)  
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->VGraph, false);
    if(VGraph.at(sympair.at(k).second).position!=NINF) {
      int magrin=VGraph.at(sympair.at(k).second).position;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) {M=magrin-xL.at(k)-xL.at(j);}
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->VGraph, true);
    if(VGraph.at(sympair.at(k).second).backpost!=NINF) {
      int magrin=VGraph.at(sympair.at(k).second).backpost;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) {M=magrin-xL.at(k)-xL.at(j);}
    }
  }
  return M;
  
}

int ConstGraph::CalculateBminusY(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis) {
  int M=-1*NINF;
  if(axis==placerDB::V) { // vertical symmetry
    // L2: Xj(j.first) -> Yk(k.second) -> di(axis) -> Xj(j.first)
    // x_ij + x_ik >= w(Yk) + dist(Xj,Yk)  
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->HGraph, false);
    if(HGraph.at(sympair.at(k).second).position!=NINF) {
      int magrin=HGraph.at(sympair.at(k).second).position;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) { if(magrin-xL.at(k)<M) { M=magrin-xL.at(k); } }
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->HGraph, true);
    if(HGraph.at(sympair.at(k).second).backpost!=NINF) {
      int magrin=HGraph.at(sympair.at(k).second).backpost;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) { if(magrin-xL.at(k)<M) { M=magrin-xL.at(k); } }
    }
  } else { // horizontal symmetry
    // L2: Xj(j.first) -> Yk(k.second) -> di(axis) -> Xj(j.first)
    // x_ij + x_ik >= w(Yk) + dist(Xj,Yk)  
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->VGraph, false);
    if(VGraph.at(sympair.at(k).second).position!=NINF) {
      int magrin=VGraph.at(sympair.at(k).second).position;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) { if(magrin-xL.at(k)<M) { M=magrin-xL.at(k); } }
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->VGraph, true);
    if(VGraph.at(sympair.at(k).second).backpost!=NINF) {
      int magrin=VGraph.at(sympair.at(k).second).backpost;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) { if(magrin-xL.at(k)<M) { M=magrin-xL.at(k); } }
    }
  }
  return M;
}

bool ConstGraph::CheckIfSingleL2Violation(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis) {
  // return true if k-th L2 constraint violates
  // otherwise return false
  if(axis==placerDB::V) { // vertical symmetry axis
    // L2: Xj(j.first) -> Yk(k.second) -> di(axis) -> Xj(j.first)
    // x_ij + x_ik >= w(Yk) + dist(Xj,Yk)  
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->HGraph, false);
    if(HGraph.at(sympair.at(k).second).position!=NINF) {
      int magrin=HGraph.at(sympair.at(k).second).position;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) {return true;}
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->HGraph, true);
    if(HGraph.at(sympair.at(k).second).backpost!=NINF) {
      int magrin=HGraph.at(sympair.at(k).second).backpost;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) {return true;}
    }
  } else if (axis==placerDB::H) { // horizontal symmetry axis
    // L2: Xj(j.first) -> Yk(k.second) -> di(axis) -> Xj(j.first)
    // x_ij + x_ik >= w(Yk) + dist(Xj,Yk)  
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->VGraph, false);
    if(VGraph.at(sympair.at(k).second).position!=NINF) {
      int magrin=VGraph.at(sympair.at(k).second).position;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) {return true;}
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).first, this->VGraph, true);
    if(VGraph.at(sympair.at(k).second).backpost!=NINF) {
      int magrin=VGraph.at(sympair.at(k).second).backpost;
      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
      //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
      if(xL.at(j)+xL.at(k)<magrin) {return true;}
    }
  }
  return false;
}

pair<int,int> ConstGraph::CheckIfL2Violation(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis) {
  for(int j=0;j<(int)sympair.size();j++) {
  int vio;
    if( (vio=CheckIfL2ViolationUnit(caseNL, sympair, xL, j, axis))!=-1 ) {return make_pair(j,vio);}
  }
  return make_pair(-1,-1);
}

int ConstGraph::CheckIfL2ViolationUnit(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, int j, placerDB::Smark axis) {
  // return the index of correlated pair if any violation on L2 constraints
  // otherwise return -1
  for(int k=0;k<(int)sympair.size();k++) {
    if(j==k) {continue;}
    if( CheckIfSingleL2Violation(caseNL, sympair, xL, j, k, axis) ) { return k; }
  }
  return -1; 
  //if(axis==V) {
  //  for(int k=0;k<(int)sympair.size();k++) {
  //    if(j==k) {continue;}
  //    // L2: Xj(j.first) -> Yk(k.second) -> di(axis) -> Xj(j.first)
  //    // x_ij + x_ik >= w(Yk) + dist(Xj,Yk)  
  //    // forward graph constraint
  //    CalculateLongestPath(sympair.at(j).first, this->HGraph, false);
  //    if(HGraph.at(sympair.at(k).second).position!=NINF) {
  //      int magrin=HGraph.at(sympair.at(k).second).position;
  //      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
  //      if(xL.at(j)+xL.at(k)<magrin) {return k;}
  //    }
  //    // backward graph constraint
  //    CalculateLongestPath(sympair.at(j).first, this->HGraph, true);
  //    if(HGraph.at(sympair.at(k).second).backpost!=NINF) {
  //      int magrin=HGraph.at(sympair.at(k).second).backpost;
  //      if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
  //      if(xL.at(j)+xL.at(k)<magrin) {return k;}
  //    }
  //  }
  //} else {
  //}
}

bool ConstGraph::CheckIfLslackViolation(vector<int>& Lslack ) {
  for(vector<int>::iterator it=Lslack.begin(); it!=Lslack.end(); ++it) {
    if(*it<0) return true;
  }
  return false;
}

void ConstGraph::UpdateLslackElement(design& caseNL, vector< pair<int,int> >& sympair, vector< pair<int,placerDB::Smark> >& selfsym, vector<int>& Lslack, vector<int>& xL, int j, placerDB::Smark axis) {
  if(axis==placerDB::V) {
  // vertical symmetry axis
    // U1: Yj(second) -> Xj(first) -> di(axis) -> Yj(second)
    // x_ij <= (w(Yj)-dist(Yj,Xj))/2
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).second, this->HGraph, false);
    if( HGraph.at(sympair.at(j).first).position!=NINF ) {
      int magrin=-1*HGraph.at(sympair.at(j).first).position;
      if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(j).second).weight;}
      //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second));}
      magrin=magrin/2; magrin-=xL.at(j);
      if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).second, this->HGraph, true);
    if( HGraph.at(sympair.at(j).first).backpost!=NINF ) {
      int magrin=-1*HGraph.at(sympair.at(j).first).backpost;
      if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(j).second).weight;}
      //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second));}
      magrin=magrin/2; magrin-=xL.at(j);
      if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
    }
    for(vector< pair<int,placerDB::Smark> >::iterator zit=selfsym.begin(); zit!=selfsym.end(); ++zit) {
      // U1: Zk(zit) -> Xj(first) -> di(axis) -> Zk(zit)
      // x_ij <= w(Zk)/2 - dist(Zk,Xj)
      // forward graph constraint
      CalculateLongestPath(zit->first, this->HGraph, false);
      if(HGraph.at(sympair.at(j).first).position!=NINF) {
        int magrin=-1*HGraph.at(sympair.at(j).first).position+HGraph.at(zit->first).weight/2-xL.at(j);
        //int magrin=-1*HGraph.at(sympair.at(j).first).position+caseNL.GetBlockWidth(zit->first, caseSP.GetBlockOrient(zit->first))/2-xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // backward graph constraint
      CalculateLongestPath(zit->first, this->HGraph, true);
      if(HGraph.at(sympair.at(j).first).backpost!=NINF) {
        int magrin=-1*HGraph.at(sympair.at(j).first).backpost+HGraph.at(zit->first).weight/2-xL.at(j);
        //int magrin=-1*HGraph.at(sympair.at(j).first).backpost+caseNL.GetBlockWidth(zit->first, caseSP.GetBlockOrient(zit->first))/2-xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // U1: Yj(second) -> Zk(zit) -> di(axis) -> Yj(second)
      // x_ij <= w(Yj) - w(Zk)/2 - dist(Yj,Zk)
      // forward graph constraint
      CalculateLongestPath(sympair.at(j).second, this->HGraph, false);
      if(HGraph.at(zit->first).position!=NINF) {
        int magrin=-1*HGraph.at(zit->first).position-HGraph.at(zit->first).weight/2;
        //int magrin=-1*HGraph.at(zit->first).position-caseNL.GetBlockWidth(zit->first, caseSP.GetBlockOrient(zit->first))/2;
        if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(j).second).weight; }
        //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // backward graph constraint
      CalculateLongestPath(sympair.at(j).second, this->HGraph, true);
      if(HGraph.at(zit->first).backpost!=NINF) {
        int magrin=-1*HGraph.at(zit->first).backpost-HGraph.at(zit->first).weight/2;
        //int magrin=-1*HGraph.at(zit->first).backpost-caseNL.GetBlockWidth(zit->first, caseSP.GetBlockOrient(zit->first))/2;
        if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(j).second).weight; }
        //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
    }
    for(int k=0;k<(int)sympair.size();k++) {
      if(j==k) {continue;}
      // U2: Yk(k.second) -> Xj(j.first) -> di(axis) -> Yk(k.second)
      // x_ij <= w(Yk) - dist(Yk,Xj) - x_ik
      // forward graph constraint
      CalculateLongestPath(sympair.at(k).second, this->HGraph, false);
      if(HGraph.at(sympair.at(j).first).position!=NINF) {
        int magrin=-1*HGraph.at(sympair.at(j).first).position-xL.at(k);
        if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
        //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // backward graph constraint
      CalculateLongestPath(sympair.at(k).second, this->HGraph, true);
      if(HGraph.at(sympair.at(j).first).backpost!=NINF) {
        int magrin=-1*HGraph.at(sympair.at(j).first).backpost-xL.at(k);
        if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=HGraph.at(sympair.at(k).second).weight;}
        //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockWidth(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
    }
  } else if(axis==placerDB::H) {
  // Horizontal symmetry axis
    // U1: Yj(second) -> Xj(first) -> di(axis) -> Yj(second)
    // x_ij <= (w(Yj)-dist(Yj,Xj))/2
    // forward graph constraint
    CalculateLongestPath(sympair.at(j).second, this->VGraph, false);
    if( VGraph.at(sympair.at(j).first).position!=NINF ) {
      int magrin=-1*VGraph.at(sympair.at(j).first).position;
      if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(j).second).weight;}
      //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second));}
      magrin=magrin/2; magrin-=xL.at(j);
      if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
    }
    // backward graph constraint
    CalculateLongestPath(sympair.at(j).second, this->VGraph, true);
    if( VGraph.at(sympair.at(j).first).backpost!=NINF ) {
      int magrin=-1*VGraph.at(sympair.at(j).first).backpost;
      if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(j).second).weight;}
      //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second));}
      magrin=magrin/2; magrin-=xL.at(j);
      if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
    }
    for(vector< pair<int,placerDB::Smark> >::iterator zit=selfsym.begin(); zit!=selfsym.end(); ++zit) {
      // U1: Zk(zit) -> Xj(first) -> di(axis) -> Zk(zit)
      // x_ij <= w(Zk)/2 - dist(Zk,Xj)
      // forward graph constraint
      CalculateLongestPath(zit->first, this->VGraph, false);
      if(VGraph.at(sympair.at(j).first).position!=NINF) {
        int magrin=-1*VGraph.at(sympair.at(j).first).position+VGraph.at(zit->first).weight/2-xL.at(j);
        //int magrin=-1*VGraph.at(sympair.at(j).first).position+caseNL.GetBlockHeight(zit->first, caseSP.GetBlockOrient(zit->first))/2-xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // backward graph constraint
      CalculateLongestPath(zit->first, this->VGraph, true);
      if(VGraph.at(sympair.at(j).first).backpost!=NINF) {
        int magrin=-1*VGraph.at(sympair.at(j).first).backpost+VGraph.at(zit->first).weight/2-xL.at(j);
        //int magrin=-1*VGraph.at(sympair.at(j).first).backpost+caseNL.GetBlockHeight(zit->first, caseSP.GetBlockOrient(zit->first))/2-xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // U1: Yj(second) -> Zk(zit) -> di(axis) -> Yj(second)
      // x_ij <= w(Yj) - w(Zk)/2 - dist(Yj,Zk)
      // forward graph constraint
      CalculateLongestPath(sympair.at(j).second, this->VGraph, false);
      if(VGraph.at(zit->first).position!=NINF) {
        int magrin=-1*VGraph.at(zit->first).position-VGraph.at(zit->first).weight/2;
        //int magrin=-1*VGraph.at(zit->first).position-caseNL.GetBlockHeight(zit->first, caseSP.GetBlockOrient(zit->first))/2;
        if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(j).second).weight; }
        //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // backward graph constraint
      CalculateLongestPath(sympair.at(j).second, this->VGraph, true);
      if(VGraph.at(zit->first).backpost!=NINF) {
        int magrin=-1*VGraph.at(zit->first).backpost-VGraph.at(zit->first).weight/2;
        //int magrin=-1*VGraph.at(zit->first).backpost-caseNL.GetBlockHeight(zit->first, caseSP.GetBlockOrient(zit->first))/2;
        if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(j).second).weight; }
        //if(sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(j).second, caseSP.GetBlockOrient(sympair.at(j).second)); }
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
    }
    for(int k=0;k<(int)sympair.size();k++) {
      if(j==k) {continue;}
      // U2: Yk(k.second) -> Xj(j.first) -> di(axis) -> Yk(k.second)
      // x_ij <= w(Yk) - dist(Yk,Xj) - x_ik
      // forward graph constraint
      CalculateLongestPath(sympair.at(k).second, this->VGraph, false);
      if(VGraph.at(sympair.at(j).first).position!=NINF) {
        int magrin=-1*VGraph.at(sympair.at(j).first).position-xL.at(k);
        if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
        //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
      // backward graph constraint
      CalculateLongestPath(sympair.at(k).second, this->VGraph, true);
      if(VGraph.at(sympair.at(j).first).backpost!=NINF) {
        int magrin=-1*VGraph.at(sympair.at(j).first).backpost-xL.at(k);
        if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=VGraph.at(sympair.at(k).second).weight;}
        //if(sympair.at(k).second<(int)caseNL.GetSizeofBlocks()) {magrin+=caseNL.GetBlockHeight(sympair.at(k).second, caseSP.GetBlockOrient(sympair.at(k).second));}
        magrin-=xL.at(j);
        if(Lslack.at(j)>magrin) {Lslack.at(j)=magrin;}
      }
    }
  }
}

void ConstGraph::Test(design& caseNL, SeqPair& caseSP) {
  //AddEdgeforVertex(9, 1, -229, HGraph);
  CalculateLongestPath(sourceNode, this->HGraph, false);
  CalculateLongestPath(sourceNode, this->VGraph, false);
  PrintConstGraph();
  CalculateLongestPath(5, this->HGraph, true);
  CalculateLongestPath(5, this->VGraph, true);
  PrintConstGraph();
  //cout<<"Penalt: "<<  CalculatePenalty(this->HGraph) << endl;
  //cout<<"WL: "<<CalculateWireLength(caseNL, caseSP)<<endl;
  //cout<<"Area: "<<CalculateArea()<<endl;
}

PnRDB::bbox ConstGraph::ConvertBoundaryData(vector<placerDB::point> Bdata) {
  PnRDB::bbox newBdata;
  PnRDB::point tmpp;
  int x=Bdata.at(0).x, X=Bdata.at(0).x, y=Bdata.at(0).y, Y=Bdata.at(0).y;
  for(vector<placerDB::point>::iterator it=Bdata.begin();it!=Bdata.end();++it) {
    tmpp.x=it->x; tmpp.y=it->y;
    if((it->x)<x) {x=it->x;}
    if((it->x)>X) {X=it->x;}
    if((it->y)<y) {y=it->y;}
    if((it->y)>Y) {Y=it->y;}
  }
  newBdata.LL.x=x; newBdata.LL.y=y;
  newBdata.UR.x=X; newBdata.UR.y=Y;
  return newBdata;
}

PnRDB::point ConstGraph::ConvertPointData(placerDB::point Pdata) {
  PnRDB::point newPdata;
  newPdata.x=Pdata.x; newPdata.y=Pdata.y;
  return newPdata;
}

void ConstGraph::UpdateDesignHierNode4AP(design& caseNL, design& reducedNL, SeqPair& reducedSP, PnRDB::hierNode& node) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.UpdateDesignHierNode4AP");

  //vector<vector<placerDB::point> > boundary;
  //vector<placerDB::point> center;
  vector<placerDB::point> bbox;
  placerDB::point bpoint;
  placerDB::point LL;
  placerDB::Omark ort;

  node.width=HGraph.at(sinkNode).position;
  node.height=VGraph.at(sinkNode).position;
  //cout<<"W: "<<node.width<<" H: "<<node.height<<endl;
  // 1. update all blocks according to results of reduced design
  for(int j=0;j<caseNL.GetSizeofBlocks();++j) {
    //cout<<"Blocks "<<j<<endl;
    int i=caseNL.GetMappedBlockIdx(j); // index in reduced design
    if(i!=-1) {
      //cout<<"Reduced blocks "<<i<<endl;
      int sel=reducedSP.GetBlockSelected(i);
      int x=HGraph.at(i).position;
      int y=VGraph.at(i).position;
      LL={x,y};
      ort=reducedSP.GetBlockOrient(i);
      bbox=reducedNL.GetPlacedBlockAbsBoundary(i, ort, LL, sel);
      bpoint=reducedNL.GetBlockAbsCenter(i, ort, LL, sel);
      node.Blocks.at(j).selectedInstance=sel;
      node.Blocks.at(j).instance.at(sel).orient=PnRDB::Omark(ort);
      node.Blocks.at(j).instance.at(sel).placedBox=ConvertBoundaryData(bbox);
      node.Blocks.at(j).instance.at(sel).placedCenter=ConvertPointData(bpoint);
    } else {
      int sel=0;
      int x=node.width/2-caseNL.GetBlockWidth(j, placerDB::N, sel)/2;
      int y=node.height/2-caseNL.GetBlockHeight(j, placerDB::N, sel)/2;
      //cout<<node.Blocks.at(j).instance.name<<" X: "<<x<<" Y: "<<y<<endl;
      LL={x,y};
      ort=placerDB::N;
      bbox=caseNL.GetPlacedBlockAbsBoundary(j, ort, LL, sel);
      bpoint=caseNL.GetBlockAbsCenter(j, ort, LL, sel);
      node.Blocks.at(j).selectedInstance=sel;
      node.Blocks.at(j).instance.at(sel).orient=PnRDB::Omark(ort);
      node.Blocks.at(j).instance.at(sel).placedBox=ConvertBoundaryData(bbox);
      node.Blocks.at(j).instance.at(sel).placedCenter=ConvertPointData(bpoint);
    }
  }
  // 2. update blocks in symmetry groups
  for(int j=0;j<caseNL.GetSizeofSBlocks();j++) {
    int i=caseNL.GetMappedSymmBlockIdx(j);
    if(i==-1) { // no corresponding symmgroup in reduced design
      // Choose the vertical symmetry axis in the middile of the die
      placerDB::Smark axis_dir=placerDB::V;
      if(!caseNL.SBlocks.at(j).selfsym.empty()) {
        if(caseNL.SBlocks.at(j).selfsym.at(0).second==placerDB::V) {
          axis_dir=placerDB::H;
        } else if (caseNL.SBlocks.at(j).selfsym.at(0).second==placerDB::H) {
          axis_dir=placerDB::V;
        }
      }
      caseNL.SBlocks.at(j).axis_dir=axis_dir;
      if(axis_dir==placerDB::V) {
        caseNL.SBlocks.at(j).axis_coor=node.width/2;
      } else if(axis_dir==placerDB::H) {
        caseNL.SBlocks.at(j).axis_coor=node.height/2;
      } else {
        logger->debug("Placer-Error: incorrect symmetry axis direction");
      }
      for(std::vector< pair<int,placerDB::Smark> >::iterator it=caseNL.SBlocks.at(j).selfsym.begin(); it!=caseNL.SBlocks.at(j).selfsym.end(); ++it ) {
        if(it->first>=caseNL.GetSizeofBlocks()) {continue;}
        int sel=node.Blocks.at(it->first).selectedInstance;
        if(axis_dir==placerDB::V) {
          ort=placerDB::N;
          int x=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockWidth(it->first, ort, sel)/2;
          int y=node.height/2-caseNL.GetBlockHeight(it->first, ort, sel)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel);
          node.Blocks.at(it->first).instance.at(sel).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel).placedCenter=ConvertPointData(bpoint);
        } else if(axis_dir==placerDB::H) {
          ort=placerDB::N;
          int x=node.width/2-caseNL.GetBlockWidth(it->first, ort, sel)/2;
          int y=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockHeight(it->first, ort, sel)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel);
          node.Blocks.at(it->first).instance.at(sel).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel).placedCenter=ConvertPointData(bpoint);
        } else {
          logger->debug("Placer-Error: incorrect symmetry axis direction");
        }
      }
      for( std::vector< pair<int,int> >::iterator it=caseNL.SBlocks.at(j).sympair.begin(); it!=caseNL.SBlocks.at(j).sympair.end(); ++it) {
        if(it->first>=caseNL.GetSizeofBlocks() or it->second>=caseNL.GetSizeofBlocks()) {continue;}
        int sel1=node.Blocks.at(it->first).selectedInstance;
        int sel2=node.Blocks.at(it->second).selectedInstance;
        if(axis_dir==placerDB::V) {
          ort=placerDB::N;
          int x=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockWidth(it->first, ort, sel1)/2;
          int y=node.height/2-caseNL.GetBlockHeight(it->first, ort, sel1)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel1);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel1);
          node.Blocks.at(it->first).instance.at(sel1).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel1).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel1).placedCenter=ConvertPointData(bpoint);

          ort=placerDB::FN;
          x=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockWidth(it->second, ort, sel2)/2;
          y=node.height/2-caseNL.GetBlockHeight(it->second, ort, sel2)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->second, ort, LL, sel2);
          bpoint=caseNL.GetBlockAbsCenter(it->second, ort, LL, sel2);
          node.Blocks.at(it->second).instance.at(sel2).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->second).instance.at(sel2).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->second).instance.at(sel2).placedCenter=ConvertPointData(bpoint);
        } else if (axis_dir==placerDB::H) {
          ort=placerDB::N;
          int x=node.width/2-caseNL.GetBlockWidth(it->first, ort, sel1)/2;
          int y=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockHeight(it->first, ort, sel1)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel1);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel1);
          node.Blocks.at(it->first).instance.at(sel1).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel1).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel1).placedCenter=ConvertPointData(bpoint);

          ort=placerDB::FS;
          x=node.width/2-caseNL.GetBlockWidth(it->second, ort, sel2)/2;
          y=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockHeight(it->second, ort, sel2)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->second, ort, LL, sel2);
          bpoint=caseNL.GetBlockAbsCenter(it->second, ort, LL, sel2);
          node.Blocks.at(it->second).instance.at(sel2).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->second).instance.at(sel2).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->second).instance.at(sel2).placedCenter=ConvertPointData(bpoint);
        } else {
          logger->debug("Placer-Error: incorrect symmetry axis direction");
        }
      }
    } else {
      placerDB::Smark axis_dir=reducedSP.GetSymmBlockAxis(i);
      int dnode=reducedNL.GetBlockSymmGroupDnode(i);
      caseNL.SBlocks.at(j).axis_dir=axis_dir;
      if(axis_dir==placerDB::V) {
        caseNL.SBlocks.at(j).axis_coor=HGraph.at(dnode).position;
      } else if(axis_dir==placerDB::H) {
        caseNL.SBlocks.at(j).axis_coor=VGraph.at(dnode).position;
      } else {
        logger->debug("Placer-Error: incorrect symmetry axis direction");
      }
      std::vector<placerDB::SymmBlock> tmpSB=caseNL.SplitSymmBlock(reducedNL, j);
      placerDB::SymmBlock diff=tmpSB.at(1);
      for(std::vector< pair<int,placerDB::Smark> >::iterator it=diff.selfsym.begin(); it!=diff.selfsym.end(); ++it ) {
        if(it->first>=caseNL.GetSizeofBlocks()) {continue;}
        int sel1=node.Blocks.at(it->first).selectedInstance;
        if(axis_dir==placerDB::V) {
          ort=placerDB::N;
          int x=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockWidth(it->first, ort, sel1)/2;
          int y=node.height/2-caseNL.GetBlockHeight(it->first, ort, sel1)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel1);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel1);
          node.Blocks.at(it->first).instance.at(sel1).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel1).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel1).placedCenter=ConvertPointData(bpoint);
        } else if(axis_dir==placerDB::H) {
          ort=placerDB::N;
          int x=node.width/2-caseNL.GetBlockWidth(it->first, ort, sel1)/2;
          int y=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockHeight(it->first, ort, sel1)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel1);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel1);
          node.Blocks.at(it->first).instance.at(sel1).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel1).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel1).placedCenter=ConvertPointData(bpoint);
        } else {
          logger->debug("Placer-Error: incorrect symmetry axis direction");
        }
      }
      for( std::vector< pair<int,int> >::iterator it=diff.sympair.begin(); it!=diff.sympair.end(); ++it) {
        if(it->first>=caseNL.GetSizeofBlocks() or it->second>=caseNL.GetSizeofBlocks()) {continue;}
        int sel1=node.Blocks.at(it->first).selectedInstance;
        int sel2=node.Blocks.at(it->second).selectedInstance;
        if(axis_dir==placerDB::V) {
          ort=placerDB::N;
          int x=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockWidth(it->first, ort, sel1)/2;
          int y=node.height/2-caseNL.GetBlockHeight(it->first, ort, sel1)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel1);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel1);
          node.Blocks.at(it->first).instance.at(sel1).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel1).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel1).placedCenter=ConvertPointData(bpoint);

          ort=placerDB::FN;
          x=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockWidth(it->second, ort, sel2)/2;
          y=node.height/2-caseNL.GetBlockHeight(it->second, ort, sel2)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->second, ort, LL, sel2);
          bpoint=caseNL.GetBlockAbsCenter(it->second, ort, LL, sel2);
          node.Blocks.at(it->second).instance.at(sel2).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->second).instance.at(sel2).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->second).instance.at(sel2).placedCenter=ConvertPointData(bpoint);
        } else if (axis_dir==placerDB::H) {
          ort=placerDB::N;
          int x=node.width/2-caseNL.GetBlockWidth(it->first, ort, sel1)/2;
          int y=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockHeight(it->first, ort, sel1)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->first, ort, LL, sel1);
          bpoint=caseNL.GetBlockAbsCenter(it->first, ort, LL, sel1);
          node.Blocks.at(it->first).instance.at(sel1).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->first).instance.at(sel1).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->first).instance.at(sel1).placedCenter=ConvertPointData(bpoint);

          ort=placerDB::FS;
          x=node.width/2-caseNL.GetBlockWidth(it->second, ort, sel2)/2;
          y=caseNL.SBlocks.at(j).axis_coor-caseNL.GetBlockHeight(it->second, ort, sel2)/2;
          LL={x,y};
          bbox=caseNL.GetPlacedBlockAbsBoundary(it->second, ort, LL, sel2);
          bpoint=caseNL.GetBlockAbsCenter(it->second, ort, LL, sel2);
          node.Blocks.at(it->second).instance.at(sel2).orient=PnRDB::Omark(ort);
          node.Blocks.at(it->second).instance.at(sel2).placedBox=ConvertBoundaryData(bbox);
          node.Blocks.at(it->second).instance.at(sel2).placedCenter=ConvertPointData(bpoint);
        } else {
          logger->debug("Placer-Error: incorrect symmetry axis direction");
        }
      }
    }
  }
}

void ConstGraph::UpdateBlockinHierNode(design& caseNL, placerDB::Omark ort, PnRDB::hierNode& node, int i, int sel, PnRDB::Drc_info& drcInfo) {
  vector<vector<placerDB::point> > boundary;
  vector<placerDB::point> center;
  vector<placerDB::point> bbox;
  placerDB::point bpoint;

    int x=HGraph.at(i).position;
    int y=VGraph.at(i).position;


    //SMB Hack
    auto roundup = []( int& v, int pitch) {
      v = pitch*((v+pitch-1)/pitch);
    };

    int v_metal_index = -1;
    int h_metal_index = -1;
    
    for(unsigned int i=0;i<drcInfo.Metal_info.size();++i){
        if(drcInfo.Metal_info[i].direct==0){
          v_metal_index = i;
          break;
        }
    }

    for(unsigned int i=0;i<drcInfo.Metal_info.size();++i){
        if(drcInfo.Metal_info[i].direct==1){
          h_metal_index = i;
          break;
        }
    }


    int x_pitch = drcInfo.Metal_info[v_metal_index].grid_unit_x;
    int y_pitch = drcInfo.Metal_info[h_metal_index].grid_unit_y;

    roundup( x, x_pitch);
    roundup( y, y_pitch);

    placerDB::point LL={x,y};

    //placerDB::Omark ort=caseSP.GetBlockOrient(i);
    bbox=caseNL.GetPlacedBlockAbsBoundary(i, ort, LL, sel);
    bpoint=caseNL.GetBlockAbsCenter(i, ort, LL, sel);
    //int sel=node.Blocks.at(i).selectedInstance;
    auto& nd = node.Blocks.at(i).instance.at(sel);

    nd.orient=PnRDB::Omark(ort);
    nd.placedBox=ConvertBoundaryData(bbox);
    nd.placedCenter=ConvertPointData(bpoint);
    for(int j=0;j<caseNL.GetBlockPinNum(i,sel);j++) {
      //cout<<"  Pin "<<j<<endl;
      boundary=caseNL.GetPlacedBlockPinAbsBoundary(i, j, ort, LL, sel);
      center=caseNL.GetPlacedBlockPinAbsPosition(i, j, ort, LL, sel);
      // [wbxu] Following two lines have be updated for multiple contacts
      // update pin contacts
      for(unsigned int k=0;k<nd.blockPins.at(j).pinContacts.size();k++) {
        //cout<<"    Pin contact "<<k<<endl;
        nd.blockPins.at(j).pinContacts.at(k).placedBox=ConvertBoundaryData(boundary.at(k));
        nd.blockPins.at(j).pinContacts.at(k).placedCenter=ConvertPointData(center.at(k));
      }
      // update pin vias
      for(unsigned int k=0;k<node.Blocks.at(i).instance.at(sel).blockPins.at(j).pinVias.size();k++) {
        //cout<<"    Pin via "<<k<<endl;
	auto& pv = nd.blockPins.at(j).pinVias.at(k);
	pv.placedpos=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.originpos, LL, sel);
        pv.UpperMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, pv.UpperMetalRect.originBox, LL, sel);
        pv.LowerMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, pv.LowerMetalRect.originBox, LL, sel);
        pv.ViaRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, pv.ViaRect.originBox, LL, sel);
        pv.UpperMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.UpperMetalRect.originCenter, LL, sel);
        pv.LowerMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.LowerMetalRect.originCenter, LL, sel);
        pv.ViaRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, pv.ViaRect.originCenter, LL, sel);
      }
    }
  // [wbxu] Complete programing: to update internal metals
    // update internal metals
    for(unsigned int j=0;j<node.Blocks.at(i).instance.at(sel).interMetals.size();j++) {
      //cout<<"  IM "<<j<<endl;
      auto& im = nd.interMetals.at(j);
      im.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, im.originBox, LL, sel);
      im.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, im.originCenter, LL, sel);
    }
    // update internal vias
    for(unsigned int j=0;j<node.Blocks.at(i).instance.at(sel).interVias.size();j++) {
      //cout<<"  Internal via "<<j<<endl;
      auto& iv = nd.interVias.at(j);
      iv.placedpos                  =caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.originpos,LL,sel);
      iv.UpperMetalRect.placedBox   =caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, iv.UpperMetalRect.originBox,LL,sel);
      iv.LowerMetalRect.placedBox   =caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, iv.LowerMetalRect.originBox,LL,sel);
      iv.ViaRect.placedBox          =caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, iv.ViaRect.originBox,LL,sel);
      iv.UpperMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.UpperMetalRect.originCenter,LL,sel);
      iv.LowerMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.LowerMetalRect.originCenter,LL,sel);
      iv.ViaRect.placedCenter       =caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, iv.ViaRect.originCenter,LL,sel);
    }
}

void ConstGraph::UpdateTerminalinHierNode(design& caseNL, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  if(1) {
    for(int i=0;i<(int)caseNL.GetSizeofTerminals();i++) {
      //cout<<"Terminal "<<i<<endl;
      node.Terminals.at(i).termContacts.clear();
      node.Terminals.at(i).termContacts.resize( node.Terminals.at(i).termContacts.size()+1 );
      node.Terminals.at(i).termContacts.back().placedCenter=ConvertPointData(caseNL.GetTerminalCenter(i));
    }

  /*
    placerDB::point p, bp;
    for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
      bool hasTerminal=false;
      int distTerm=-1*NINF;
      int tno; placerDB::point tp;
      // for each pin
      for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
        if(ci->type==placerDB::Block) {
          bp.x=this->HGraph.at(ci->iter2).position;
          bp.y=this->VGraph.at(ci->iter2).position;
          p=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp);
          //placerDB::Omark ort=caseSP.GetBlockOrient(ci->iter2);
          //p=caseNL.GetBlockCenter(ci->iter2, ort);
          //p.x+=this->HGraph.at(ci->iter2).position;
          //p.y+=this->VGraph.at(ci->iter2).position;
          
          if( caseNL.GetBlockSymmGroup(ci->iter2)==-1  ) { // not in any symmetry group
            if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
            if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
            if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
            if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
          } else { // if in symmetry group
            if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::V  ) {
              if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
            } else if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::H  ) {
              if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
            }
          }
        } else if (ci->type==placerDB::Terminal) {
          hasTerminal=true; tno=ci->iter;
        }
      }
      if(hasTerminal) { cout<<caseNL.Terminals.at(tno).name<<"\t"<<tp.x<<"\t"<<tp.y<<endl;  }
    }
  */
  }

  //update blockpin information

  PnRDB::pin temp_pin;

  if(1){

    for(int i=0;i<(int)caseNL.GetSizeofTerminals();i++) {
      //cout<<"Terminal "<<i<<endl;
      temp_pin.name = node.Terminals.at(i).name;
      temp_pin.type = node.Terminals.at(i).type;

      temp_pin.netIter = node.Terminals.at(i).netIter;
      temp_pin.pinContacts = node.Terminals.at(i).termContacts;
      for (int j=0;j<temp_pin.pinContacts.size();j++)
        temp_pin.pinContacts[j].metal = drcInfo.Metal_info[0].name;

      temp_pin.name = node.Terminals.at(i).name;
      temp_pin.type = node.Terminals.at(i).type;
      
      /*
      //added by yaguang - 10/28/2020
      //should add the power pin into blockpins here, since the placer is bottom up and router is top down
      for(unsigned int j=0;j<node.Nets.size();j++){
         if(node.Nets[j].name==temp_pin.name){
           for(unsigned int k=0;k<node.Nets[j].connected.size();k++){
              if(node.Nets[j].connected[k].type==PnRDB::Block){
                 int iter = node.Nets[j].connected[k].iter;
                 int iter2 = node.Nets[j].connected[k].iter2;
                 PnRDB::pin temp_pnr_pin=node.Blocks[iter2].instance.back().blockPins[iter];
                 for(unsigned int l=0;l<temp_pnr_pin.pinContacts.size();l++)
                     temp_pin.pinContacts.push_back(temp_pnr_pin.pinContacts[l]);
              }
           }
            
         }
         
      }
      */

      node.blockPins.push_back(temp_pin);
    }

  }

}

void ConstGraph::UpdateHierNodeAP(design& caseNL, Aplace& caseAP, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  //vector<vector<placerDB::point> > boundary;
  //vector<placerDB::point> center;
  //vector<placerDB::point> bbox;
  //placerDB::point bpoint;

  node.width=HGraph.at(sinkNode).position;
  node.height=VGraph.at(sinkNode).position;
  //cout<<"Start!"<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    node.Blocks.at(i).selectedInstance=caseAP.GetSelectedInstance(i);
    //placerDB::Omark ort=caseSP.GetBlockOrient(i);
    //cout<<"Blocks "<<i<<endl;
    UpdateBlockinHierNode(caseNL, caseAP.GetBlockOrient(i), node, i, caseAP.GetSelectedInstance(i), drcInfo);
  }
  // [wbxu] Complete programing: to update terminal for top-level
  UpdateTerminalinHierNode(caseNL, node, drcInfo);
  for(unsigned int i=0;i<caseNL.SNets.size(); ++i) {
    int SBidx=caseNL.SNets.at(i).SBidx;
    placerDB::Smark axis_dir=caseAP.GetSBlockDir(SBidx);
    UpdateSymmetryNetInfo(caseNL, node, i, SBidx, axis_dir);
  }
}

void ConstGraph::UpdateSymmetryNetInfo(design& caseNL, PnRDB::hierNode& node, int i, int SBidx, placerDB::Smark axis_dir) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.UpdateSymmetryNetInfo");

  int dnode=caseNL.GetBlockSymmGroupDnode(SBidx);
  int axis_coor=0;
  if(axis_dir==placerDB::V) {
    axis_coor=HGraph.at(dnode).position;
  } else if(axis_dir==placerDB::H) {
    axis_coor=VGraph.at(dnode).position;
  } else {
    logger->debug("Placer-Error: incorrect symmetry axis direction");
  }
  string net1=caseNL.SNets.at(i).net1.name;
  string net2=caseNL.SNets.at(i).net2.name;
  for(std::vector<PnRDB::net>::iterator it=node.Nets.begin(); it!=node.Nets.end(); ++it) {
    if(it->name.compare(net1)==0 or it->name.compare(net2)==0) {
      it->axis_dir=PnRDB::Smark(int(axis_dir));
      it->axis_coor=axis_coor;
    }
  }
}

void ConstGraph::UpdateHierNode(design& caseNL, SeqPair& caseSP, PnRDB::hierNode& node, PnRDB::Drc_info& drcInfo) {
  //vector<vector<placerDB::point> > boundary;
  //vector<placerDB::point> center;
  //vector<placerDB::point> bbox;
  //placerDB::point bpoint;

  node.width=HGraph.at(sinkNode).position;
  node.height=VGraph.at(sinkNode).position;
  //cout<<"Start!"<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    node.Blocks.at(i).selectedInstance=caseSP.GetBlockSelected(i);
    //placerDB::Omark ort=caseSP.GetBlockOrient(i);
    //cout<<"Blocks "<<i<<endl;
    UpdateBlockinHierNode(caseNL, caseSP.GetBlockOrient(i), node, i, caseSP.GetBlockSelected(i), drcInfo);
  }
  // [wbxu] Complete programing: to update terminal for top-level
  UpdateTerminalinHierNode(caseNL, node, drcInfo);
  for(unsigned int i=0;i<caseNL.SNets.size(); ++i) {
    int SBidx=caseNL.SNets.at(i).SBidx;
    placerDB::Smark axis_dir=caseSP.GetSymmBlockAxis(SBidx);
    UpdateSymmetryNetInfo(caseNL, node, i, SBidx, axis_dir);
  }
}

void ConstGraph::updateTerminalCenterAP(design& caseNL,  Aplace& caseAP) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.updateTerminalCenterAP");

  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  vector<placerDB::point> pos; placerDB::point p, bp; int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each terminal
  for(int i=0;i<(int)caseNL.GetSizeofTerminals();++i) {
    if(solved_terminals.find(i)!=solved_terminals.end()) {continue;}
    solved_terminals.insert(i);
    int netIdx=caseNL.Terminals.at(i).netIter;
    int sbIdx=caseNL.Terminals.at(i).SBidx;
    int cp=caseNL.Terminals.at(i).counterpart;
    if(netIdx<0 or netIdx>=caseNL.GetSizeofNets()) {
      logger->debug("Placer-Warning: terminal {0} is dangling; set it on origin",i);
      caseNL.Terminals.at(i).center.x = 0;
      caseNL.Terminals.at(i).center.y = 0;
      continue;
    }
    //pos.clear();
    if((caseNL.Nets.at(netIdx).priority).compare("min")==0) { alpha=4;
    } else if((caseNL.Nets.at(netIdx).priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=caseNL.Nets.at(netIdx).weight; // add weight to reflect the modification for bigMacros
    if(sbIdx!=-1) { // in symmetry group
      int dnode=caseNL.GetBlockSymmGroupDnode(sbIdx);
      placerDB::Smark axis=caseAP.GetSBlockDir(sbIdx);
      int axis_X=this->HGraph.at(dnode).position;
      int axis_Y=this->VGraph.at(dnode).position;
      if(cp==i) { // self-symmetric
        if(axis==placerDB::V) {
          int distTerm=INT_MAX;
          placerDB::point tp; tp.x=axis_X;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTerm) {distTerm=p.y; tp.y=0;}
                if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.y=Ymax; }
              }
            }
          }
          caseNL.Terminals.at(i).center.x = tp.x;
          caseNL.Terminals.at(i).center.y = tp.y;
        } else if(axis==placerDB::H) {
          int distTerm=INT_MAX;
          placerDB::point tp; tp.y=axis_Y;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++) {
                p = pos_pin[k];
                if(p.x<distTerm) {distTerm=p.x; tp.x=0; }
                if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; }
              }
            }
          }
          caseNL.Terminals.at(i).center.x = tp.x;
          caseNL.Terminals.at(i).center.y = tp.y;
        } else {
          logger->debug("Placer-Error: incorrect axis direction");
        }
      } else { // symmetry pair
        if(solved_terminals.find(cp)!=solved_terminals.end()) {logger->debug("Placer-Error: terminal {0} and {1} are not solved simultaneously!",i,cp);continue;}
        solved_terminals.insert(cp);
        int netIdx2=caseNL.Terminals.at(cp).netIter;
        if(netIdx2<0 or netIdx2>=caseNL.GetSizeofNets()) {
          logger->debug("Placer-Error: terminal {0} is not dangling, but its counterpart {1} is dangling; set them on origin",i,cp);
          caseNL.Terminals.at(i).center.x = 0;
          caseNL.Terminals.at(i).center.y = 0;
          caseNL.Terminals.at(cp).center.x = 0;
          caseNL.Terminals.at(cp).center.y = 0;
          continue;
        }
        int alpha2;
        if((caseNL.Nets.at(netIdx2).priority).compare("min")==0) { alpha2=4;
        } else if((caseNL.Nets.at(netIdx2).priority).compare("mid")==0) { alpha2=2;
        } else { alpha2=1; }
        alpha2*=caseNL.Nets.at(netIdx2).weight; // add weight to reflect the modification for bigMacros
        if(axis==placerDB::V) {
          placerDB::point tpL1, tpR1;
          int distTermL=INT_MAX, distTermR=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL) {distTermL=p.x; tpL1.x=0; tpL1.y=p.y;}
                if(Xmax-p.x<distTermR) {distTermR=Xmax-p.x; tpR1.x=Xmax; tpR1.y=p.y;}
              }
            }
          }
          placerDB::point tpL2, tpR2;
          int distTermL2=INT_MAX, distTermR2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL2) {distTermL2=p.x; tpL2.x=0; tpL2.y=p.y;}
                if(Xmax-p.x<distTermR2) {distTermR2=Xmax-p.x; tpR2.x=Xmax; tpR2.y=p.y;}
              }
            }
          }
          if(distTermL*alpha+distTermR2*alpha2<distTermR*alpha+distTermL2*alpha2) {
            caseNL.Terminals.at(i).center.x = tpL1.x;
            caseNL.Terminals.at(i).center.y = tpL1.y;
            caseNL.Terminals.at(cp).center.x = tpR2.x;
            caseNL.Terminals.at(cp).center.y = tpR2.y;
          } else {
            caseNL.Terminals.at(i).center.x = tpR1.x;
            caseNL.Terminals.at(i).center.y = tpR1.y;
            caseNL.Terminals.at(cp).center.x = tpL2.x;
            caseNL.Terminals.at(cp).center.y = tpL2.y;
          }
        } else if (axis==placerDB::H) {
          placerDB::point tpL1, tpU1;
          int distTermL=INT_MAX, distTermU=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL) {distTermL=p.y; tpL1.x=p.x; tpL1.y=0;}
                if(Ymax-p.y<distTermU) {distTermU=Ymax-p.y; tpU1.x=p.x; tpU1.y=Ymax;}
              }
            }
          }
          placerDB::point tpL2, tpU2;
          int distTermL2=INT_MAX, distTermU2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL2) {distTermL2=p.y; tpL2.x=p.x; tpL2.y=0;}
                if(Ymax-p.y<distTermU2) {distTermU2=Ymax-p.y; tpU2.x=p.x; tpU2.y=Ymax;}
              }
            }
          }
          if(distTermL*alpha+distTermU2*alpha2<distTermU*alpha+distTermL2*alpha2) {
            caseNL.Terminals.at(i).center.x = tpL1.x;
            caseNL.Terminals.at(i).center.y = tpL1.y;
            caseNL.Terminals.at(cp).center.x = tpU2.x;
            caseNL.Terminals.at(cp).center.y = tpU2.y;
          } else {
            caseNL.Terminals.at(i).center.x = tpU1.x;
            caseNL.Terminals.at(i).center.y = tpU1.y;
            caseNL.Terminals.at(cp).center.x = tpL2.x;
            caseNL.Terminals.at(cp).center.y = tpL2.y;
          }
        } else {
          logger->debug("Placer-Error: incorrect axis direction");
        }
      }
    } else { // not in symmetry group
      int tar=-1;
      for(unsigned int j=0;j<caseNL.Port_Location.size();++j) {
        if(caseNL.Port_Location.at(j).tid==i) {tar=j; break;}
      }
      if(tar!=-1) { // specifiy PortLocation constraint
        int x1=Xmax/3, x2=Xmax*2/3, x3=Xmax;
        int y1=Ymax/3, y2=Ymax*2/3, y3=Ymax;
        placerDB::point tp;
        pos.clear();
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              pos.push_back(p);
            }
          }
        }
        int shot=-1;
        int distTerm=INT_MAX;
        for(unsigned int k=0;k<pos.size();++k) {
          p=pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch(caseNL.Port_Location.at(tar).pos) {
            case placerDB::TL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k; tp.x=p.x; tp.y=Ymax;}
                 } else {
                   if( std::abs(p.x-0)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-0)+Ymax-p.y; shot=k; tp.x=0; tp.y=Ymax; }
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;tp.x=x1;tp.y=Ymax; }
                 }
                 break;
            case placerDB::TC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k; tp.x=p.x; tp.y=Ymax;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;tp.x=x2;tp.y=Ymax;}
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;tp.x=x1;tp.y=Ymax;}
                 }
                 break;
            case placerDB::TR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k; tp.x=p.x; tp.y=Ymax;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;tp.x=x2;tp.y=Ymax;}
                   if( std::abs(p.x-x3)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x3)+Ymax-p.y; shot=k;tp.x=x3;tp.y=Ymax;}
                 }
                 break;
            case placerDB::RT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;tp.x=Xmax; tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y2;}
                   if( std::abs(p.y-y3)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y3)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y3;}
                 }
                 break;
            case placerDB::RC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;tp.x=Xmax; tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y2;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y1;}
                 }
                 break;
            case placerDB::RB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;tp.x=Xmax;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-0)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-0)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=0;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y1;}
                 }
                 break;
            case placerDB::BL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;tp.x=p.x;tp.y=0;}
                 } else {
                   if( std::abs(p.x-0)+p.y<distTerm ) {distTerm=std::abs(p.x-0)+p.y; shot=k;tp.x=0;tp.y=0;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;tp.x=x1;tp.y=0;}
                 }
                 break;
            case placerDB::BC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;tp.x=p.x;tp.y=0;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;tp.x=x2;tp.y=0;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;tp.x=x1;tp.y=0;}
                 }
                 break;
            case placerDB::BR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;tp.x=p.x;tp.y=0;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;tp.x=x2;tp.y=0;}
                   if( std::abs(p.x-x3)+p.y<distTerm ) {distTerm=std::abs(p.x-x3)+p.y; shot=k;tp.x=x3;tp.y=0;}
                 }
                 break;
            case placerDB::LT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;tp.x=0;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;tp.x=0;tp.y=y2;}
                   if( std::abs(p.y-y3)+p.x<distTerm ) {distTerm=std::abs(p.y-y3)+p.x; shot=k;tp.x=0;tp.y=y3;}
                 }
                 break;
            case placerDB::LC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;tp.x=0;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;tp.x=0;tp.y=y2;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;tp.x=0;tp.y=y1;}
                 }
                 break;
            case placerDB::LB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;tp.x=0;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-0)+p.x<distTerm ) {distTerm=std::abs(p.y-0)+p.x; shot=k;tp.x=0;tp.y=0;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;tp.x=0;tp.y=y1;}
                 }
                 break;
            default :
                 logger->debug("Placer-Warning: incorrect port position");
          }
        }
        if(shot!=-1) {
          caseNL.Terminals.at(i).center.x = tp.x;
          caseNL.Terminals.at(i).center.y = tp.y;
        }
      } else { // no constraint
        placerDB::point tp;
        int distTerm=INT_MAX;
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              if(p.x<distTerm) {distTerm=p.x;tp.x=0;tp.y=p.y;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;tp.x=Xmax;tp.y=p.y;}
              if(p.y<distTerm) {distTerm=p.y;tp.x=p.x;tp.y=0;}
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;tp.x=p.x;tp.y=Ymax;}
            }
          }
        }
        caseNL.Terminals.at(i).center.x = tp.x;
        caseNL.Terminals.at(i).center.y = tp.y;
      }
    }
  }
}


void ConstGraph::updateTerminalCenterAPRetire(design& caseNL, Aplace& caseAP) {
  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  placerDB::point p, bp;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int distTerm=-1*NINF;
    int tno; placerDB::point tp;
	vector<placerDB::point> p_pin;
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        p_pin=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));
		for(unsigned int i=0;i<p_pin.size();i++){
			p=p_pin[i];
        //placerDB::Omark ort=caseAP.GetBlockOrient(ci->iter2);
        //p=caseNL.GetBlockCenter(ci->iter2, ort);
        //p.x+=this->HGraph.at(ci->iter2).position;
        //p.y+=this->VGraph.at(ci->iter2).position;
        
          if( caseNL.GetBlockSymmGroup(ci->iter2)==-1  ) { // not in any symmetry group
            if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
            if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
            if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
            if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
          } else { // if in symmetry group
            if ( caseAP.GetSBlockDir(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::V  ) {
              if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
            } else if ( caseAP.GetSBlockDir(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::H  ) {
              if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
            }
          }
	  }
        } else if (ci->type==placerDB::Terminal) {
          hasTerminal=true; tno=ci->iter;
        }
      }
      if(hasTerminal) {
                        //update the terminal information to the placerDB
                        caseNL.Terminals.at(tno).center.x = tp.x;
                        caseNL.Terminals.at(tno).center.y = tp.y;
                      }
    }
}

//void ConstGraph::UpdateHierNode(design& caseNL, SeqPair& caseSP, PnRDB::hierNode& node) {
//  vector<vector<placerDB::point> > boundary;
//  vector<placerDB::point> center;
//  vector<placerDB::point> bbox;
//  placerDB::point bpoint;
//
//  node.width=HGraph.at(sinkNode).position;
//  node.height=VGraph.at(sinkNode).position;
//  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
//    int x=HGraph.at(i).position;
//    int y=VGraph.at(i).position;
//    placerDB::point LL={x,y};
//    placerDB::Omark ort=caseSP.GetBlockOrient(i);
//    bbox=caseNL.GetPlacedBlockAbsBoundary(i, ort, LL);
//    bpoint=caseNL.GetBlockAbsCenter(i, ort, LL);
//    node.Blocks.at(i).instance.orient=PnRDB::Omark(ort);
//    node.Blocks.at(i).instance.placedBox=ConvertBoundaryData(bbox);
//    node.Blocks.at(i).instance.placedCenter=ConvertPointData(bpoint);
//    for(int j=0;j<caseNL.GetBlockPinNum(i);j++) {
//      boundary=caseNL.GetPlacedBlockPinAbsBoundary(i, j, ort, LL);
//      center=caseNL.GetPlacedBlockPinAbsPosition(i, j, ort, LL);
//      // [wbxu] Following two lines have be updated for multiple contacts
//      // update pin contacts
//      for(int k=0;k<(int)node.Blocks.at(i).instance.blockPins.at(j).pinContacts.size();k++) {
//
//        node.Blocks.at(i).instance.blockPins.at(j).pinContacts.at(k).placedBox=ConvertBoundaryData(boundary.at(k));
//        node.Blocks.at(i).instance.blockPins.at(j).pinContacts.at(k).placedCenter=ConvertPointData(center.at(k));
//      }
//      // update pin vias
//      for(int k=0;k<(int)node.Blocks.at(i).instance.blockPins.at(j).pinVias.size();k++) {
//        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).placedpos=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).originpos, LL);
//        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.originBox, LL);
//        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.originBox, LL);
//        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.originBox, LL);
//        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.originCenter, LL);
//        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.originCenter, LL);
//        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.originCenter, LL);
//      }
//    }
//  // [wbxu] Complete programing: to update internal metals
//    // update internal metals
//    for(int j=0;j<(int)node.Blocks.at(i).instance.interMetals.size();j++) {
//      node.Blocks.at(i).instance.interMetals.at(j).placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interMetals.at(j).originBox, LL);
//      node.Blocks.at(i).instance.interMetals.at(j).placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interMetals.at(j).originCenter, LL);
//    }
//    // update internal vias
//    for(int j=0;j<(int)node.Blocks.at(i).instance.interVias.size();j++) {
//      node.Blocks.at(i).instance.interVias.at(j).placedpos=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).originpos,LL);
//      node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.originBox,LL);
//      node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.originBox,LL);
//      node.Blocks.at(i).instance.interVias.at(j).ViaRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interVias.at(j).ViaRect.originBox,LL);
//      node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.originCenter,LL);
//      node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.originCenter,LL);
//      node.Blocks.at(i).instance.interVias.at(j).ViaRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).ViaRect.originCenter,LL);
//    }
//  }
//  // [wbxu] Complete programing: to update terminal for top-level
//  if(node.isTop) {
//    for(int i=0;i<(int)caseNL.GetSizeofTerminals();i++) {
//      node.Terminals.at(i).termContacts.clear();
//      node.Terminals.at(i).termContacts.resize( node.Terminals.at(i).termContacts.size()+1 );
//      node.Terminals.at(i).termContacts.back().placedCenter=ConvertPointData(caseNL.GetTerminalCenter(i));
//    }
//  /*
//    placerDB::point p, bp;
//    for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
//      bool hasTerminal=false;
//      int distTerm=-1*NINF;
//      int tno; placerDB::point tp;
//      // for each pin
//      for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
//        if(ci->type==placerDB::Block) {
//          bp.x=this->HGraph.at(ci->iter2).position;
//          bp.y=this->VGraph.at(ci->iter2).position;
//          p=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp);
//          //placerDB::Omark ort=caseSP.GetBlockOrient(ci->iter2);
//          //p=caseNL.GetBlockCenter(ci->iter2, ort);
//          //p.x+=this->HGraph.at(ci->iter2).position;
//          //p.y+=this->VGraph.at(ci->iter2).position;
//          
//          if( caseNL.GetBlockSymmGroup(ci->iter2)==-1  ) { // not in any symmetry group
//            if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
//            if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
//            if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
//            if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
//          } else { // if in symmetry group
//            if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::V  ) {
//              if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
//              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
//            } else if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::H  ) {
//              if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
//              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
//            }
//          }
//        } else if (ci->type==placerDB::Terminal) {
//          hasTerminal=true; tno=ci->iter;
//        }
//      }
//      if(hasTerminal) { cout<<caseNL.Terminals.at(tno).name<<"\t"<<tp.x<<"\t"<<tp.y<<endl;  }
//    }
//  */
//  }
//}

void ConstGraph::updateTerminalCenter(design& caseNL, SeqPair& caseSP) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.updateTerminalCenter");

  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  vector<placerDB::point> pos; placerDB::point p, bp; int alpha;
  vector<placerDB::point> pos_pin;
  std::set<int> solved_terminals;
  // for each terminal
  for(int i=0;i<caseNL.GetSizeofTerminals();++i) {
    if(solved_terminals.find(i)!=solved_terminals.end()) {continue;}
    solved_terminals.insert(i);
    int netIdx=caseNL.Terminals.at(i).netIter;
    int sbIdx=caseNL.Terminals.at(i).SBidx;
    int cp=caseNL.Terminals.at(i).counterpart;
    if(netIdx<0 or netIdx>=caseNL.GetSizeofNets()) {
      logger->debug("Placer-Warning: terminal {0}  is dangling; set it on origin", i);
      caseNL.Terminals.at(i).center.x = 0;
      caseNL.Terminals.at(i).center.y = 0;
      continue;
    }
    //pos.clear();
    if((caseNL.Nets.at(netIdx).priority).compare("min")==0) { alpha=4;
    } else if((caseNL.Nets.at(netIdx).priority).compare("mid")==0) { alpha=2;
    } else { alpha=1; }
    alpha*=caseNL.Nets.at(netIdx).weight; // add weight to reflect the modification for bigMacros
    if(sbIdx!=-1) { // in symmetry group
      int dnode=caseNL.GetBlockSymmGroupDnode(sbIdx);
      placerDB::Smark axis=caseSP.GetSymmBlockAxis(sbIdx);
      int axis_X=this->HGraph.at(dnode).position;
      int axis_Y=this->VGraph.at(dnode).position;
      if(cp==(int)i) { // self-symmetric
        if(axis==placerDB::V) {
          int distTerm=INT_MAX;
          placerDB::point tp; tp.x=axis_X;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTerm) {distTerm=p.y; tp.y=0;}
                if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.y=Ymax; }
              }
            }
          }
          caseNL.Terminals.at(i).center.x = tp.x;
          caseNL.Terminals.at(i).center.y = tp.y;
        } else if(axis==placerDB::H) {
          int distTerm=INT_MAX;
          placerDB::point tp; tp.y=axis_Y;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++) {
                p = pos_pin[k];
                if(p.x<distTerm) {distTerm=p.x; tp.x=0; }
                if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; }
              }
            }
          }
          caseNL.Terminals.at(i).center.x = tp.x;
          caseNL.Terminals.at(i).center.y = tp.y;
        } else {
          logger->debug("Placer-Error: incorrect axis direction");
        }
      } else { // symmetry pair
        if(solved_terminals.find(cp)!=solved_terminals.end()) {logger->debug("Placer-Error: terminal {0} and {1} are not solved simultaneously",i,cp); continue;}
        solved_terminals.insert(cp);
        int netIdx2=caseNL.Terminals.at(cp).netIter;
        if(netIdx2<0 or netIdx2>=caseNL.GetSizeofNets()) {
          logger->debug("Placer-Error: terminal {0} is not dangling, but its counterpart {1} is dangling; set them on origin",i,cp);
          caseNL.Terminals.at(i).center.x = 0;
          caseNL.Terminals.at(i).center.y = 0;
          caseNL.Terminals.at(cp).center.x = 0;
          caseNL.Terminals.at(cp).center.y = 0;
          continue;
        }
        int alpha2;
        if((caseNL.Nets.at(netIdx2).priority).compare("min")==0) { alpha2=4;
        } else if((caseNL.Nets.at(netIdx2).priority).compare("mid")==0) { alpha2=2;
        } else { alpha2=1; }
        alpha2*=caseNL.Nets.at(netIdx2).weight; // add weight to reflect the modification for bigMacros
        if(axis==placerDB::V) {
          placerDB::point tpL1, tpR1;
          int distTermL=INT_MAX, distTermR=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL) {distTermL=p.x; tpL1.x=0; tpL1.y=p.y;}
                if(Xmax-p.x<distTermR) {distTermR=Xmax-p.x; tpR1.x=Xmax; tpR1.y=p.y;}
              }
            }
          }
          placerDB::point tpL2, tpR2;
          int distTermL2=INT_MAX, distTermR2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.x<distTermL2) {distTermL2=p.x; tpL2.x=0; tpL2.y=p.y;}
                if(Xmax-p.x<distTermR2) {distTermR2=Xmax-p.x; tpR2.x=Xmax; tpR2.y=p.y;}
              }
            }
          }
          if(distTermL*alpha+distTermR2*alpha2<distTermR*alpha+distTermL2*alpha2) {
            caseNL.Terminals.at(i).center.x = tpL1.x;
            caseNL.Terminals.at(i).center.y = tpL1.y;
            caseNL.Terminals.at(cp).center.x = tpR2.x;
            caseNL.Terminals.at(cp).center.y = tpR2.y;
          } else {
            caseNL.Terminals.at(i).center.x = tpR1.x;
            caseNL.Terminals.at(i).center.y = tpR1.y;
            caseNL.Terminals.at(cp).center.x = tpL2.x;
            caseNL.Terminals.at(cp).center.y = tpL2.y;
          }
        } else if (axis==placerDB::H) {
          placerDB::point tpL1, tpU1;
          int distTermL=INT_MAX, distTermU=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL) {distTermL=p.y; tpL1.x=p.x; tpL1.y=0;}
                if(Ymax-p.y<distTermU) {distTermU=Ymax-p.y; tpU1.x=p.x; tpU1.y=Ymax;}
              }
            }
          }
          placerDB::point tpL2, tpU2;
          int distTermL2=INT_MAX, distTermU2=INT_MAX;
          for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx2).connected.begin(); ci!=caseNL.Nets.at(netIdx2).connected.end(); ++ci) {
            if(ci->type==placerDB::Block) {
              bp.x=this->HGraph.at(ci->iter2).position;
              bp.y=this->VGraph.at(ci->iter2).position;
              pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
              for(unsigned int k=0;k<pos_pin.size();k++){
                p = pos_pin[k];
                if(p.y<distTermL2) {distTermL2=p.y; tpL2.x=p.x; tpL2.y=0;}
                if(Ymax-p.y<distTermU2) {distTermU2=Ymax-p.y; tpU2.x=p.x; tpU2.y=Ymax;}
              }
            }
          }
          if(distTermL*alpha+distTermU2*alpha2<distTermU*alpha+distTermL2*alpha2) {
            caseNL.Terminals.at(i).center.x = tpL1.x;
            caseNL.Terminals.at(i).center.y = tpL1.y;
            caseNL.Terminals.at(cp).center.x = tpU2.x;
            caseNL.Terminals.at(cp).center.y = tpU2.y;
          } else {
            caseNL.Terminals.at(i).center.x = tpU1.x;
            caseNL.Terminals.at(i).center.y = tpU1.y;
            caseNL.Terminals.at(cp).center.x = tpL2.x;
            caseNL.Terminals.at(cp).center.y = tpL2.y;
          }
        } else {
          logger->error("Placer-Error: incorrect axis direction");
        }
      }
    } else { // not in symmetry group
      int tar=-1;
      for(unsigned int j=0;j<caseNL.Port_Location.size();++j) {
        if(caseNL.Port_Location.at(j).tid==(int)i) {tar=j; break;}
      }
      if(tar!=-1) { // specifiy PortLocation constraint
        int x1=Xmax/3, x2=Xmax*2/3, x3=Xmax;
        int y1=Ymax/3, y2=Ymax*2/3, y3=Ymax;
        placerDB::point tp;
        pos.clear();
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              pos.push_back(p);
            }
          }
        }
        int shot=-1;
        int distTerm=INT_MAX;
        for(unsigned int k=0;k<pos.size();++k) {
          p=pos.at(k);
          // Bmark {TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT};
          switch(caseNL.Port_Location.at(tar).pos) {
            case placerDB::TL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k; tp.x=p.x; tp.y=Ymax;}
                 } else {
                   if( std::abs(p.x-0)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-0)+Ymax-p.y; shot=k; tp.x=0; tp.y=Ymax; }
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;tp.x=x1;tp.y=Ymax; }
                 }
                 break;
            case placerDB::TC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k; tp.x=p.x; tp.y=Ymax;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;tp.x=x2;tp.y=Ymax;}
                   if( std::abs(p.x-x1)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x1)+Ymax-p.y; shot=k;tp.x=x1;tp.y=Ymax;}
                 }
                 break;
            case placerDB::TR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; shot=k; tp.x=p.x; tp.y=Ymax;}
                 } else {
                   if( std::abs(p.x-x2)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x2)+Ymax-p.y; shot=k;tp.x=x2;tp.y=Ymax;}
                   if( std::abs(p.x-x3)+Ymax-p.y<distTerm ) {distTerm=std::abs(p.x-x3)+Ymax-p.y; shot=k;tp.x=x3;tp.y=Ymax;}
                 }
                 break;
            case placerDB::RT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;tp.x=Xmax; tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y2;}
                   if( std::abs(p.y-y3)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y3)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y3;}
                 }
                 break;
            case placerDB::RC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;tp.x=Xmax; tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y2)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y2;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y1;}
                 }
                 break;
            case placerDB::RB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; shot=k;tp.x=Xmax;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-0)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-0)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=0;}
                   if( std::abs(p.y-y1)+Xmax-p.x<distTerm ) {distTerm=std::abs(p.y-y1)+Xmax-p.x; shot=k;tp.x=Xmax;tp.y=y1;}
                 }
                 break;
            case placerDB::BL :
                 if(p.x>=0 && p.x<=x1) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;tp.x=p.x;tp.y=0;}
                 } else {
                   if( std::abs(p.x-0)+p.y<distTerm ) {distTerm=std::abs(p.x-0)+p.y; shot=k;tp.x=0;tp.y=0;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;tp.x=x1;tp.y=0;}
                 }
                 break;
            case placerDB::BC :
                 if(p.x>=x1 && p.x<=x2) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;tp.x=p.x;tp.y=0;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;tp.x=x2;tp.y=0;}
                   if( std::abs(p.x-x1)+p.y<distTerm ) {distTerm=std::abs(p.x-x1)+p.y; shot=k;tp.x=x1;tp.y=0;}
                 }
                 break;
            case placerDB::BR :
                 if(p.x>=x2 && p.x<=x3) { 
                   if(p.y<distTerm) {distTerm=p.y; shot=k;tp.x=p.x;tp.y=0;}
                 } else {
                   if( std::abs(p.x-x2)+p.y<distTerm ) {distTerm=std::abs(p.x-x2)+p.y; shot=k;tp.x=x2;tp.y=0;}
                   if( std::abs(p.x-x3)+p.y<distTerm ) {distTerm=std::abs(p.x-x3)+p.y; shot=k;tp.x=x3;tp.y=0;}
                 }
                 break;
            case placerDB::LT :
                 if(p.y>=y2 && p.y<=y3) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;tp.x=0;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;tp.x=0;tp.y=y2;}
                   if( std::abs(p.y-y3)+p.x<distTerm ) {distTerm=std::abs(p.y-y3)+p.x; shot=k;tp.x=0;tp.y=y3;}
                 }
                 break;
            case placerDB::LC :
                 if(p.y>=y1 && p.y<=y2) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;tp.x=0;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-y2)+p.x<distTerm ) {distTerm=std::abs(p.y-y2)+p.x; shot=k;tp.x=0;tp.y=y2;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;tp.x=0;tp.y=y1;}
                 }
                 break;
            case placerDB::LB :
                 if(p.y>=0 && p.y<=y1) { 
                   if(p.x<distTerm) {distTerm=p.x; shot=k;tp.x=0;tp.y=p.y;}
                 } else {
                   if( std::abs(p.y-0)+p.x<distTerm ) {distTerm=std::abs(p.y-0)+p.x; shot=k;tp.x=0;tp.y=0;}
                   if( std::abs(p.y-y1)+p.x<distTerm ) {distTerm=std::abs(p.y-y1)+p.x; shot=k;tp.x=0;tp.y=y1;}
                 }
                 break;
            default :
                 logger->error("Placer-Warning: incorrect port position");
          }
        }
        if(shot!=-1) {
          caseNL.Terminals.at(i).center.x = tp.x;
          caseNL.Terminals.at(i).center.y = tp.y;
        }
      } else { // no constraint
        placerDB::point tp;
        int distTerm=INT_MAX;
        for(vector<placerDB::Node>::iterator ci=caseNL.Nets.at(netIdx).connected.begin(); ci!=caseNL.Nets.at(netIdx).connected.end(); ++ci) {
          if(ci->type==placerDB::Block) {
            bp.x=this->HGraph.at(ci->iter2).position;
            bp.y=this->VGraph.at(ci->iter2).position;
            pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
            for(unsigned int k=0;k<pos_pin.size();k++) {
              p = pos_pin[k];
              if(p.x<distTerm) {distTerm=p.x;tp.x=0;tp.y=p.y;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x;tp.x=Xmax;tp.y=p.y;}
              if(p.y<distTerm) {distTerm=p.y;tp.x=p.x;tp.y=0;}
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y;tp.x=p.x;tp.y=Ymax;}
            }
          }
        }
        caseNL.Terminals.at(i).center.x = tp.x;
        caseNL.Terminals.at(i).center.y = tp.y;
      }
    }
  }
}


void ConstGraph::updateTerminalCenterRetire(design& caseNL, SeqPair& caseSP) {
  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  placerDB::point p, bp;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int distTerm=-1*NINF;
    int tno; placerDB::point tp;
	vector<placerDB::point> p_pin;
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        p_pin=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
		for(unsigned int i=0;i<p_pin.size();i++){
			p=p_pin[i];
        //placerDB::Omark ort=caseSP.GetBlockOrient(ci->iter2);
        //p=caseNL.GetBlockCenter(ci->iter2, ort);
        //p.x+=this->HGraph.at(ci->iter2).position;
        //p.y+=this->VGraph.at(ci->iter2).position;
        
          if( caseNL.GetBlockSymmGroup(ci->iter2)==-1  ) { // not in any symmetry group
            if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
            if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
            if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
            if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
          } else { // if in symmetry group
            if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::V  ) {
              if(p.x<distTerm) {distTerm=p.x; tp.x=0; tp.y=p.y;}
              if(Xmax-p.x<distTerm) {distTerm=Xmax-p.x; tp.x=Xmax; tp.y=p.y; }
            } else if ( caseSP.GetSymmBlockAxis(caseNL.GetBlockSymmGroup(ci->iter2))==placerDB::H  ) {
              if(p.y<distTerm) {distTerm=p.y; tp.x=p.x; tp.y=0; }
              if(Ymax-p.y<distTerm) {distTerm=Ymax-p.y; tp.x=p.x; tp.y=Ymax;}
            }
          }
	  }
        } else if (ci->type==placerDB::Terminal) {
          hasTerminal=true; tno=ci->iter;
        }
      }
      if(hasTerminal) {
                        //update the terminal information to the placerDB
                        caseNL.Terminals.at(tno).center.x = tp.x;
                        caseNL.Terminals.at(tno).center.y = tp.y;
                      }
    }
}


void ConstGraph::WritePlacementAP(design& caseNL, Aplace& caseAP, string outfile) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.WritePlacementAP");

  ofstream fout;
  fout.open(outfile.c_str());
  logger->debug("Placer-Info: write placement");
  fout<<"# TAMU blocks 1.0"<<endl<<endl;
  fout<<"DIE {"<<HGraph.at(sourceNode).position<<", "<<VGraph.at(sourceNode).position<<"} {"<<HGraph.at(sinkNode).position<<", "<<VGraph.at(sinkNode).position<<"}"<<endl<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    int x,y; string ort;
    switch(caseAP.GetBlockOrient(i)) {
      case placerDB::N: x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="N";
              break;
      case placerDB::S: x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i)); 
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i));
              ort="S";
              break;
      case placerDB::W: x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i));
              y=VGraph.at(i).position; 
              ort="W";
              break;
      case placerDB::E: x=HGraph.at(i).position;
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i));
              ort="E";
              break;
      case placerDB::FN:x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i));
              y=VGraph.at(i).position; 
              ort="FN";
              break;
      case placerDB::FS:x=HGraph.at(i).position;
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i));
              ort="FS";
              break;
      case placerDB::FW:x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="FW";
              break;
      case placerDB::FE:x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i)); 
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseAP.GetBlockOrient(i),caseAP.GetSelectedInstance(i));
              ort="FE";
              break;
      default:x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="N";
              break;
    }
    fout<<caseNL.Blocks.at(i).back().name<<"\t"<<x<<"\t"<<y<<"\t"<<ort<<endl;
  }
  fout<<endl;
  placerDB::point p, bp;
  //cout<<"writeplacement3"<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno; placerDB::point tp;
	vector<placerDB::point> p_pin;
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
     if (ci->type==placerDB::Terminal) {
          hasTerminal=true; tno=ci->iter;
        }
       }
      if(hasTerminal) { fout<<caseNL.Terminals.at(tno).name<<"\t"<<caseNL.Terminals.at(tno).center.x<<"\t"<<caseNL.Terminals.at(tno).center.y<<endl;
                        //update the terminal information to the placerDB
                        //caseNL.Terminals.at(tno).center.x = tp.x;
                        //caseNL.Terminals.at(tno).center.y = tp.y;
                      }
    }
    //cout<<"writeplacement3"<<endl;
    fout.close();
}

void ConstGraph::WritePlacement(design& caseNL, SeqPair& caseSP, string outfile) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.WritePlacement");

  ofstream fout;
  fout.open(outfile.c_str());
  logger->debug("Placer-Info: write placement");
  fout<<"# TAMU blocks 1.0"<<endl<<endl;
  fout<<"DIE {"<<HGraph.at(sourceNode).position<<", "<<VGraph.at(sourceNode).position<<"} {"<<HGraph.at(sinkNode).position<<", "<<VGraph.at(sinkNode).position<<"}"<<endl<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    int x,y; string ort;
    switch(caseSP.GetBlockOrient(i)) {
      case placerDB::N: x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="N";
              break;
      case placerDB::S: x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i)); 
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i));
              ort="S";
              break;
      case placerDB::W: x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i));
              y=VGraph.at(i).position; 
              ort="W";
              break;
      case placerDB::E: x=HGraph.at(i).position;
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i));
              ort="E";
              break;
      case placerDB::FN:x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i));
              y=VGraph.at(i).position; 
              ort="FN";
              break;
      case placerDB::FS:x=HGraph.at(i).position;
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i));
              ort="FS";
              break;
      case placerDB::FW:x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="FW";
              break;
      case placerDB::FE:x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i)); 
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i),caseSP.GetBlockSelected(i));
              ort="FE";
              break;
      default:x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="N";
              break;
    }
    fout<<caseNL.Blocks.at(i).back().name<<"\t"<<x<<"\t"<<y<<"\t"<<ort<<endl;
  }
  fout<<endl;
  placerDB::point p, bp;
  //cout<<"writeplacement3"<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno; placerDB::point tp;
	vector<placerDB::point> p_pin;
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
     if (ci->type==placerDB::Terminal) {
          hasTerminal=true; tno=ci->iter;
        }
       }
      if(hasTerminal) { fout<<caseNL.Terminals.at(tno).name<<"\t"<<caseNL.Terminals.at(tno).center.x<<"\t"<<caseNL.Terminals.at(tno).center.y<<endl;
                        //update the terminal information to the placerDB
                        //caseNL.Terminals.at(tno).center.x = tp.x;
                        //caseNL.Terminals.at(tno).center.y = tp.y;
                      }
    }
    //cout<<"writeplacement3"<<endl;
    fout.close();
}

void ConstGraph::PlotPlacement(design& caseNL, SeqPair& caseSP, string outfile) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.PlotPlacement");

  logger->debug("Placer-Info: create gnuplot file");
  placerDB::point p, bp;
  ofstream fout;
  vector<placerDB::point> p_pin;
  fout.open(outfile.c_str());
  fout<<"#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)"<<endl;
  fout<<"\nset title\" #Blocks= "<<caseNL.GetSizeofBlocks()<<", #Terminals= "<<caseNL.GetSizeofTerminals()<<", #Nets= "<<caseNL.GetSizeofNets()<<", Area="<<CalculateArea()<<", HPWL= "<<CalculateWireLength(caseNL, caseSP)<<" \""<<endl;
  fout<<"\nset nokey"<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save an EPS file for inclusion into a latex document"<<endl;
  fout<<"# set terminal postscript eps color solid 20"<<endl;
  fout<<"# set output \"result.eps\""<<endl<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save a PS file for printing"<<endl;
  fout<<"# set terminal postscript portrait color solid 20"<<endl;
  fout<<"# set output \"result.ps\""<<endl<<endl;

  int max=(HGraph.at(sinkNode).position>VGraph.at(sinkNode).position)?HGraph.at(sinkNode).position:VGraph.at(sinkNode).position;
  int bias=50;
  fout<<"\nset xrange ["<<0-max-bias<<":"<<max+bias<<"]"<<endl;
  fout<<"\nset yrange ["<<0-bias<<":"<<max+bias<<"]"<<endl;
  // set labels for blocks
  //cout<<"set labels for blocks..."<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    //std::cout<<"test flag1"<<std::endl;
    placerDB::point ntp=caseNL.GetBlockAbsCenter(i, caseSP.GetBlockOrient(i), tp, caseSP.GetBlockSelected(i));
     //std::cout<<"test flag2"<<std::endl;
    fout<<"\nset label \""<<caseNL.GetBlockName(i)<<"\" at "<<ntp.x<<" , "<<ntp.y<<" center "<<endl;
    for(int j=0;j<caseNL.GetBlockPinNum(i,caseSP.GetBlockSelected(i));j++) {
      //std::cout<<"test flag3"<<std::endl;
      p_pin =caseNL.GetPlacedBlockPinAbsPosition(i,j,caseSP.GetBlockOrient(i), tp, caseSP.GetBlockSelected(i) );
      //std::cout<<"test flag4"<<std::endl;
	  for(unsigned int k = 0; k<p_pin.size();k++){
      placerDB::point newp = p_pin[k];
      //std::cout<<"test flag5"<<std::endl;
      fout<<"\nset label \""<<caseNL.GetBlockPinName(i,j,caseSP.GetBlockSelected(i))<<"\" at "<<newp.x<<" , "<<newp.y<<endl;
      //std::cout<<"test flag6"<<std::endl;
      fout<<endl;
	  }
    }
  }
  // set labels for terminals
  //cout<<"set labels for terminals..."<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno; placerDB::point tp;
    p_pin.clear();
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
     if (ci->type==placerDB::Terminal) {
          hasTerminal=true; tno=ci->iter;
        }
      }
      if(hasTerminal) {
        fout<<"\nset label \""<<caseNL.Terminals.at(tno).name<<"\" at "<<caseNL.Terminals.at(tno).center.x<<" , "<<caseNL.Terminals.at(tno).center.y<<" center "<<endl;
      }
    }

  // plot blocks
  //cout<<"plot blocks..."<<endl;
  fout<<"\nplot[:][:] \'-\' with lines linestyle 3, \'-\' with lines linestyle 7, \'-\' with lines linestyle 1, \'-\' with lines linestyle 0"<<endl<<endl;;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    string ort;
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    //vector<point> newp=caseNL.GetPlacedBlockAbsBoundary(i, E, tp);
    logger->debug("TAMU check block {0} select {1}",caseNL.GetBlockName(i),caseSP.GetBlockSelected(i));
    vector<placerDB::point> newp=caseNL.GetPlacedBlockAbsBoundary(i, caseSP.GetBlockOrient(i), tp, caseSP.GetBlockSelected(i));
    logger->debug("TAMU after check block {0} select {1} bsize {2}",caseNL.GetBlockName(i),caseSP.GetBlockSelected(i),newp.size());
    fout<<"# block "<<caseNL.GetBlockName(i)<<" select "<<caseSP.GetBlockSelected(i)<<" bsize "<<newp.size()<<endl;
    for(int it=0; it<(int)newp.size(); it++ ) {
      fout<<"\t"<<newp[it].x<<"\t"<<newp[it].y<<endl;
    }
    fout<<"\t"<<newp[0].x<<"\t"<<newp[0].y<<endl;
    fout<<endl;
  }
  fout<<"\nEOF"<<endl;


  vector<vector<placerDB::point> > newp_pin;
  // plot block pins
  //cout<<"plot block pins..."<<endl;

  for(int i=0;i<caseNL.GetSizeofBlocks();++i) {
    string ort;
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    for(int j=0;j<caseNL.GetBlockPinNum(i,caseSP.GetBlockSelected(i));j++) {
      newp_pin=caseNL.GetPlacedBlockPinAbsBoundary(i,j, caseSP.GetBlockOrient(i), tp, caseSP.GetBlockSelected(i));
      for(unsigned int k=0;k<newp_pin.size();k++){
	  vector<placerDB::point> newp_p = newp_pin[k];
      for(unsigned int it=0; it<newp_p.size(); it++ ) {
        fout<<"\t"<<newp_p[it].x<<"\t"<<newp_p[it].y<<endl;
      }
      fout<<"\t"<<newp_p[0].x<<"\t"<<newp_p[0].y<<endl;
      fout<<endl;
    }
    }
  }
  fout<<"\nEOF"<<endl;

  // plot terminals
  //cout<<"plot terminals..."<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno=-1;
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if (ci->type==placerDB::Terminal) {
        hasTerminal=true; tno=ci->iter;
      }
    }
    if(hasTerminal) {
      int bias=20;
      fout<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y+bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x+bias<<"\t"<<caseNL.Terminals.at(tno).center.y+bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x+bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
    }
  }
  //if(caseNL.Terminals.size()>0) {
  fout<<"\nEOF"<<endl;
  //}
  // plot nets
  //cout<<"plot nets..."<<endl;

  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno; placerDB::point tp;
    vector<placerDB::point> pins;
    pins.clear();
    //std::cout<<"test flag7"<<std::endl;
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        //std::cout<<"test flag7.1"<<std::endl;
        p_pin=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp, caseSP.GetBlockSelected(ci->iter2));
        //std::cout<<"test flag7.2"<<std::endl;
        if(!p_pin.empty()) {
        for(int i=0;i<1;i++){
		p=p_pin[i];
		pins.push_back(p);
		}
        }
      } else if (ci->type==placerDB::Terminal) {
        hasTerminal=true; tno=ci->iter;
      }
    }
    //std::cout<<"test flag8"<<std::endl;
    if(hasTerminal) {pins.push_back(caseNL.Terminals.at(tno).center);}
    fout<<"\n#Net: "<<ni->name<<endl;
    if(pins.size()>=2) {
    for(int i=1;i<(int)pins.size();i++) {
      fout<<"\t"<<pins.at(0).x<<"\t"<<pins.at(0).y<<endl;
      fout<<"\t"<<pins.at(i).x<<"\t"<<pins.at(i).y<<endl;
      fout<<"\t"<<pins.at(0).x<<"\t"<<pins.at(0).y<<endl<<endl;
    }
    }
  }

  fout<<"\nEOF"<<endl;
  fout<<endl<<"pause -1 \'Press any key\'";
  fout.close();
}


void ConstGraph::PlotPlacementAP(design& caseNL, Aplace& caseAP, string outfile) {

  auto logger = spdlog::default_logger()->clone("placer.ConstGraph.PlotPlacementAP");

  logger->debug("Placer-Info: create gnuplot file");
  placerDB::point p, bp;
  ofstream fout;
  vector<placerDB::point> p_pin;
  fout.open(outfile.c_str());
  fout<<"#Use this file as a script for gnuplot\n#(See http://www.gnuplot.info/ for details)"<<endl;
  fout<<"\nset title\" #Blocks= "<<caseNL.GetSizeofBlocks()<<", #Terminals= "<<caseNL.GetSizeofTerminals()<<", #Nets= "<<caseNL.GetSizeofNets()<<", Area="<<CalculateArea()<<" , HPWL="<<CalculateWireLengthAP(caseNL,caseAP)<<" \""<<endl;
  fout<<"\nset nokey"<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save an EPS file for inclusion into a latex document"<<endl;
  fout<<"# set terminal postscript eps color solid 20"<<endl;
  fout<<"# set output \"result.eps\""<<endl<<endl;
  fout<<"#   Uncomment these two lines starting with \"set\""<<endl;
  fout<<"#   to save a PS file for printing"<<endl;
  fout<<"# set terminal postscript portrait color solid 20"<<endl;
  fout<<"# set output \"result.ps\""<<endl<<endl;

  int max=(HGraph.at(sinkNode).position>VGraph.at(sinkNode).position)?HGraph.at(sinkNode).position:VGraph.at(sinkNode).position;
  int bias=50;
  fout<<"\nset xrange ["<<0-max-bias<<":"<<max+bias<<"]"<<endl;
  fout<<"\nset yrange ["<<0-bias<<":"<<max+bias<<"]"<<endl;
  // set labels for blocks
  //cout<<"set labels for blocks..."<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    placerDB::point ntp=caseNL.GetBlockAbsCenter(i, caseAP.GetBlockOrient(i), tp, caseAP.GetSelectedInstance(i));
    fout<<"\nset label \""<<caseNL.GetBlockName(i)<<"\" at "<<ntp.x<<" , "<<ntp.y<<" center "<<endl;
    for(int j=0;j<caseNL.GetBlockPinNum(i,caseAP.GetSelectedInstance(i));j++) {
      p_pin =caseNL.GetPlacedBlockPinAbsPosition(i,j,caseAP.GetBlockOrient(i), tp, caseAP.GetSelectedInstance(i));
	  for(unsigned int k = 0; k<p_pin.size();k++){
      placerDB::point newp = p_pin[k];
      fout<<"\nset label \""<<caseNL.GetBlockPinName(i,j,caseAP.GetSelectedInstance(i))<<"\" at "<<newp.x<<" , "<<newp.y<<endl;
      fout<<endl;
	  }
    }
  }
  // set labels for terminals
  //cout<<"set labels for terminals..."<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno; placerDB::point tp;
    p_pin.clear();
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
     if (ci->type==placerDB::Terminal) {
          hasTerminal=true; tno=ci->iter;
        }
      }
      if(hasTerminal) {
        fout<<"\nset label \""<<caseNL.Terminals.at(tno).name<<"\" at "<<caseNL.Terminals.at(tno).center.x<<" , "<<caseNL.Terminals.at(tno).center.y<<" center "<<endl;
      }
    }

  // plot blocks
  //cout<<"plot blocks..."<<endl;
  fout<<"\nplot[:][:] \'-\' with lines linestyle 3, \'-\' with lines linestyle 7, \'-\' with lines linestyle 1, \'-\' with lines linestyle 0"<<endl<<endl;;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    string ort;
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    //vector<point> newp=caseNL.GetPlacedBlockAbsBoundary(i, E, tp);
    vector<placerDB::point> newp=caseNL.GetPlacedBlockAbsBoundary(i, caseAP.GetBlockOrient(i), tp, caseAP.GetSelectedInstance(i));
	
    for(int it=0; it<(int)newp.size(); it++ ) {
      fout<<"\t"<<newp[it].x<<"\t"<<newp[it].y<<endl;
    }
    fout<<"\t"<<newp[0].x<<"\t"<<newp[0].y<<endl;
    fout<<endl;
  }
  fout<<"\nEOF"<<endl;
  vector<vector<placerDB::point> > newp_pin;
  // plot block pins
  //cout<<"plot block pins..."<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    string ort;
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    for(int j=0;j<caseNL.GetBlockPinNum(i,caseAP.GetSelectedInstance(i));j++) {
      newp_pin=caseNL.GetPlacedBlockPinAbsBoundary(i,j, caseAP.GetBlockOrient(i), tp, caseAP.GetSelectedInstance(i));
      for(unsigned int k=0;k<newp_pin.size();k++){
	  vector<placerDB::point> newp_p = newp_pin[k];
      for(unsigned int it=0; it<newp_p.size(); it++ ) {
        fout<<"\t"<<newp_p[it].x<<"\t"<<newp_p[it].y<<endl;
      }
      fout<<"\t"<<newp_p[0].x<<"\t"<<newp_p[0].y<<endl;
      fout<<endl;
    }
    }
  }
  fout<<"\nEOF"<<endl;

  // plot terminals
  //cout<<"plot terminals..."<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno=-1; placerDB::point tp;
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if (ci->type==placerDB::Terminal) {
        hasTerminal=true; tno=ci->iter;
      }
    }
    if(hasTerminal) {
      int bias=20;
      fout<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y+bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x+bias<<"\t"<<caseNL.Terminals.at(tno).center.y+bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x+bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
      fout<<"\t"<<caseNL.Terminals.at(tno).center.x-bias<<"\t"<<caseNL.Terminals.at(tno).center.y-bias<<endl;
    }
  }
  //if(caseNL.Terminals.size()>0) {
  fout<<"\nEOF"<<endl;
  //}
  // plot nets
  //cout<<"plot nets..."<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int tno; placerDB::point tp;
    vector<placerDB::point> pins;
    pins.clear();
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        p_pin=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseAP.GetBlockOrient(ci->iter2), bp, caseAP.GetSelectedInstance(ci->iter2));

        if(!p_pin.empty()) {
        for(int i=0;i<1;i++){
		p=p_pin[i];
		pins.push_back(p);
		}
        }
      } else if (ci->type==placerDB::Terminal) {
        hasTerminal=true; tno=ci->iter;
      }
    }
    if(hasTerminal) {pins.push_back(caseNL.Terminals.at(tno).center);}
    fout<<"\n#Net: "<<ni->name<<endl;
    if(pins.size()>=2) {
    for(int i=1;i<(int)pins.size();i++) {
      fout<<"\t"<<pins.at(0).x<<"\t"<<pins.at(0).y<<endl;
      fout<<"\t"<<pins.at(i).x<<"\t"<<pins.at(i).y<<endl;
      fout<<"\t"<<pins.at(0).x<<"\t"<<pins.at(0).y<<endl<<endl;
    }
    }
  }
  fout<<"\nEOF"<<endl;
  fout<<endl<<"pause -1 \'Press any key\'";
  fout.close();
}

