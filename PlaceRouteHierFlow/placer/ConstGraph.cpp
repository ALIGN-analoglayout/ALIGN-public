#include "ConstGraph.h"

//added by yg
//int bias_flag=0;
//int bias_graph=0;

//int LAMBDA=1000;
//int GAMAR=30;
//int BETA=100;
 
//


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
    HGraph.at(i).weight=caseNL.GetBlockWidth(i, caseSP.GetBlockOrient(i));
    HGraph.at(i).isSource=false;
    HGraph.at(i).isSink=false;
    HGraph.at(i).isVirtual=false;
  } // Initialize real blocks in horizontal graph
  for(int i=0;i<(int)VGraph.size();i++) {
    VGraph.at(i).weight=caseNL.GetBlockHeight(i, caseSP.GetBlockOrient(i));
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
  vector<int> candidate;  Edge tmpE;

int bias_graph = caseNL.bias_graph;
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

     

      if(i<caseNL.GetSizeofBlocks() and *it<caseNL.GetSizeofBlocks() ) {
        AddEdgeforVertex(i, *it, HGraph.at(i).weight+bias_graph, this->HGraph);
      } else {
        AddEdgeforVertex(i, *it, HGraph.at(i).weight, this->HGraph);
      }
    } // add edges conncting blocks right to current one
    if(candidate.empty()) {
      //tmpE.weight=HGraph.at(i).weight;
      //tmpE.next=sinkNode;
      //HGraph.at(i).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
      AddEdgeforVertex(i, sinkNode, HGraph.at(i).weight+bias_graph, this->HGraph);
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
      AddEdgeforVertex(sourceNode, i, 0+bias_graph, this->HGraph);
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


      if(i<caseNL.GetSizeofBlocks() and *it<caseNL.GetSizeofBlocks() ) {
        AddEdgeforVertex(i, *it, VGraph.at(i).weight+bias_graph, this->VGraph);
      } else {
        AddEdgeforVertex(i, *it, VGraph.at(i).weight, this->VGraph);
      }
    } // add edges conncting blocks above current one
    if(candidate.empty()) {
      //tmpE.weight=VGraph.at(i).weight;
      //tmpE.next=sinkNode;
      //VGraph.at(i).Edges.push_back(tmpE);
      if(i<caseNL.GetSizeofBlocks()) {
      AddEdgeforVertex(i, sinkNode, VGraph.at(i).weight+bias_graph, this->VGraph);
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
      AddEdgeforVertex(sourceNode, i, 0+bias_graph, this->VGraph);
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
  cout<<endl<<"== Constraint Graph =="<<endl;
  cout<<"LAMBDA:"<<LAMBDA<<" GARMAR:"<<GAMAR<<" BETA:"<<BETA<<" origNodeSize:"<<origNodeSize<<" sourceNode:"<<sourceNode<<" sinkNode:"<<sinkNode<<endl;
  cout<<endl<<"Horizontal graph"<<endl;
  for(int i=0;i<(int)HGraph.size();i++) {
    cout<<"Node "<<i<<": weight-"<<HGraph.at(i).weight<<" isSource-";
    cout<<HGraph.at(i).isSource<<" isSink-"<<HGraph.at(i).isSink;
    cout<<" isVirtual-"<<HGraph.at(i).isVirtual<<" position-"<<HGraph.at(i).position<<" backpost-"<<HGraph.at(i).backpost<<endl;
    for(int j=0;j<(int)HGraph.at(i).Edges.size();j++) {
      cout<<"\tEdge to "<<HGraph.at(i).Edges.at(j).next<<" weight "<<HGraph.at(i).Edges.at(j).weight<<" isBackward "<<HGraph.at(i).Edges.at(j).isBackward<<endl;
    }
  }
  cout<<endl<<"Vertical graph"<<endl;
  for(int i=0;i<(int)VGraph.size();i++) {
    cout<<"Node "<<i<<": weight-"<<VGraph.at(i).weight<<" isSource-";
    cout<<VGraph.at(i).isSource<<" isSink-"<<VGraph.at(i).isSink;
    cout<<" isVirtual-"<<VGraph.at(i).isVirtual<<" position-"<<VGraph.at(i).position<<" backpost-"<<VGraph.at(i).backpost<<endl;
    for(int j=0;j<(int)VGraph.at(i).Edges.size();j++) {
      cout<<"\tEdge to "<<VGraph.at(i).Edges.at(j).next<<" weight "<<VGraph.at(i).Edges.at(j).weight<<" isBackward "<<VGraph.at(i).Edges.at(j).isBackward<<endl;
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
  if(current>=0 and current<(int)graph.size() and next>=0 and next<(int)graph.size() ) {
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
  if(current>=0 and current<(int)graph.size() and next>=0 and next<(int)graph.size()) {
    for(int i=0;i<(int)graph.at(next).Edges.size();i++ ) {
      if(graph.at(next).Edges.at(i).next==current and !graph.at(next).Edges.at(i).isBackward) {
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
  if(current>=0 and current<(int)graph.size() and next>=0 and next<(int)graph.size()) {
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
  bool *visited =new bool[(int)graph.size()];
  for(int i=0;i<(int)graph.size();++i) {visited[i]=false;}
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
      if( !it->isBackward and  !visited[it->next]) { topologicalSortUtil(it->next, visited, Stack, graph, backward);}
    } else { // backward sorting
      if(  it->isBackward and  !visited[it->next]) { topologicalSortUtil(it->next, visited, Stack, graph, backward);}
    }
  }
  Stack.push(v);
}

void ConstGraph::CalculateLongestPath(int s, vector<Vertex> &graph, bool backward) {
  stack<int> Stack;
  //int dist[(int)graph.size()];
  // Mark all vertices as not visited
  bool *visited =new bool[(int)graph.size()];
  for(int i=0;i<(int)graph.size();++i)
    visited[i]=false;
  // Call the recursive helper function to store Topological
  // Sort starting from all vertices one by one
  for(int i=0;i<(int)graph.size();++i) 
    if(!visited[i]) 
      topologicalSortUtil(i, visited, Stack, graph, backward);
  // Initialize distances to all vertices as infinite and 
  // distance to source as 0
  if(!backward) {
    for(int i=0;i<(int)graph.size();++i)
      graph.at(i).position=NINF;
    graph.at(s).position=0;
  } else {
    for(int i=0;i<(int)graph.size();++i)
      graph.at(i).backpost=NINF;
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
          if(!it->isBackward && graph[it->next].position<graph[u].position+it->weight)
            graph[it->next].position=graph[u].position + it->weight;
        }
      }
    } else {
      if(graph[u].backpost!=NINF) {
        for(vector<Edge>::iterator it=graph[u].Edges.begin(); it!=graph[u].Edges.end(); ++it) {
          if( it->isBackward && graph[it->next].backpost<graph[u].backpost+it->weight)
            graph[it->next].backpost=graph[u].backpost + it->weight;
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
  // return true if any violation found, otherwise return false
  if(CheckPositiveCycle(this->HGraph)) return true;
  return CheckPositiveCycle(this->VGraph);
}

bool ConstGraph::CheckPositiveCycle(vector<Vertex> &graph) {
// return true when there exists positive cycle in constraint graph
  CalculateLongestPath(sourceNode, graph, false);
  bool mark=false;
  //int sum=0;
  for(int i=0;i<(int)graph.size() and !mark ;++i) {
    for(vector<Edge>::iterator ei=graph.at(i).Edges.begin(); ei!=graph.at(i).Edges.end() and !mark ; ++ei) {
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
  for(int i=0;i<(int)graph.size();++i) {
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

double ConstGraph::CalculateWireLength(design& caseNL, SeqPair& caseSP) {
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
        pos_pin =caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp);
	//pos_pin_all.push_back(pos_pin);	
          for(int i=0;i<pos_pin.size();i++){
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


//added by yg
double ConstGraph::CalculateMatchCost(design& caseNL, SeqPair& caseSP) {
	double sum=0;
  //CalculateLongestPath(sourceNode, this->HGraph, false);
  //CalculateLongestPath(sourceNode, this->VGraph, false);
  // for each net
  for(int i=0;i<caseNL.Match_blocks.size();i++) {
  int x1,y1,x2,y2;
        x1=this->HGraph.at(caseNL.Match_blocks[i].blockid1).position;
        y1=this->VGraph.at(caseNL.Match_blocks[i].blockid1).position;
	x2=this->HGraph.at(caseNL.Match_blocks[i].blockid2).position;
        y2=this->VGraph.at(caseNL.Match_blocks[i].blockid2).position;
	sum =sum + abs(x1-x2)+abs(y1-y2);
        }
  return sum;
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
  //cout<<"GAMAR:"<<GAMAR<<" BETA "<<BETA<<"LAMBDA "<<LAMBDA<<endl;
  //cout<<"Penalt: "<<  (CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph))*GAMAR<<" vs "<< (CalculatePenalty(this->HGraph)+CalculatePenalty(this->VGraph)) << endl;
  //cout<<"WL: "<<CalculateWireLength(caseNL, caseSP)*LAMBDA<<" vs "<<CalculateWireLength(caseNL, caseSP)<<endl;
  //cout<<"Area: "<<CalculateArea()<<endl;
  //cout<<"MAtch: "<<CalculateMatchCost(caseNL, caseSP)*BETA<<" vs "<< CalculateMatchCost(caseNL, caseSP) <<endl;
  //cout<<"Ratio: "<<CalculateRatio()*SIGMA<<" vs "<<CalculateRatio() <<endl;
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
  //cout<<"NEW GAMAR:"<<GAMAR<<" BETA:"<<BETA<<" LAMBDA:"<<LAMBDA<<" SIGMA:"<<SIGMA<<endl;
  //cout<<"NEW_BETA:"<<BETA<<endl;

}

bool ConstGraph::ConstraintHorizontalDistance(int n1, int n2, int c1, int c2 ) {
  bool mark=true;
  mark = (mark and AddEdgeforVertex(n1, n2, c1, HGraph) );
  mark = (mark and AddEdgeforVertex(n1, n2, -1*c2, HGraph) );
  return mark;
  //return (AddEdgeforVertex(n1, n2, c1, HGraph) or AddEdgeforVertex(n1, n2, -1*c2, HGraph));
}

bool ConstGraph::ConstraintVerticalDistance(int n1, int n2, int c1, int c2 ) {
  bool mark=true;
  mark = (mark and AddEdgeforVertex(n1, n2, c1, VGraph) );
  mark = (mark and AddEdgeforVertex(n1, n2, -1*c2, VGraph) );
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
  if(axis==placerDB::V) {
    // Vertical symmetry axis
    CalculateLongestPath(sourceNode, this->HGraph, false);
    for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(i).sympair.begin(); pit!=caseNL.SBlocks.at(i).sympair.end(); ++pit) {
      if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
      } else if(pit->first>(int)caseNL.GetSizeofBlocks() and pit->second>(int)caseNL.GetSizeofBlocks()) {
        // terminal pair
        tp.first=sourceNode; tp.second=sinkNode;
        sympair.push_back(tp);
      }
    }
  } else if(axis==placerDB::H) {
    // Horizontal symmetry axis
    CalculateLongestPath(sourceNode, this->VGraph, false);
    for(vector< pair<int,int> >::iterator pit=caseNL.SBlocks.at(i).sympair.begin(); pit!=caseNL.SBlocks.at(i).sympair.end(); ++pit) {
      if(pit->first<(int)caseNL.GetSizeofBlocks() and pit->second<(int)caseNL.GetSizeofBlocks()) {
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
      } else if(pit->first>(int)caseNL.GetSizeofBlocks() and pit->second>(int)caseNL.GetSizeofBlocks()) {
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
        if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() and sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) { // block pair
          tmpx=HGraph.at(sympair.at(j).second).weight;
        } else if( sympair.at(j).first==sourceNode and sympair.at(j).second==sinkNode ) { // terminal pair
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
        if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() and sympair.at(j).second<(int)caseNL.GetSizeofBlocks() ) { // block pair
          tmpx=VGraph.at(sympair.at(j).second).weight;
        } else if( sympair.at(j).first==sourceNode and sympair.at(j).second==sinkNode ) { // terminal pair
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

bool ConstGraph::ConstraintGraph(design& caseNL, SeqPair& caseSP) {
  placerDB::Smark axis;
  vector< pair<int,int> > sympair;
  vector<int> xL, slack, Lslack; 
  pair<int,int> tp;
  pair<int,int> vio;
  //int dnode;
  /* initialize random seed: */
  //srand(time(NULL));
  for(int i=0;i<(int)caseNL.SBlocks.size();i++) {
    // for i-th symmetry group
    axis=caseSP.GetSymmBlockAxis(i);
    int dnode=caseNL.SBlocks.at(i).dnode;
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
    UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
    // 3. Generate slack(x)
    slack=GenerateSlack(xL);
    // 4. Initialze largest possible slack Lslack(x)
    for(int j=0;j<(int)sympair.size(); j++) 
      Lslack.at(j)=-1*NINF;
    // 5. Update Lslack(x) according to U1,U2
    for(int j=0;j<(int)sympair.size(); j++) 
      UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
    if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
    // 6. while some constraints in L2 are not satisfied
    while( (vio=CheckIfL2Violation(caseNL, caseSP, sympair, xL, axis)).first !=-1 ) {
     // for any violation on L2 constraint x+y>=b
      if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      // if x+y<b
      // x = min{x+slack(x), x+Lslack(x), b-y}
      int newxL=xL.at(vio.first)+slack.at(vio.first);
      if( xL.at(vio.first)+Lslack.at(vio.first)<newxL ) {newxL=xL.at(vio.first)+Lslack.at(vio.first);}
      int B_y=CalculateBminusY(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis);
      if( B_y<newxL ) {newxL=B_y;}
      xL.at(vio.first)=newxL;
      // Update xL list
      UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
      // Update Lslack list
      for(int j=0;j<(int)sympair.size(); j++) 
        UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
      // Update slack list
      slack.clear(); slack=GenerateSlack(xL);
      //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints

      if( CheckIfSingleL2Violation(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis) ) {
        // y = min{y+slack(y), y+Lslack(y), b-x}
        int newxL=xL.at(vio.second)+slack.at(vio.second);
        if( xL.at(vio.second)+Lslack.at(vio.second)<newxL ) {newxL=xL.at(vio.second)+Lslack.at(vio.second);}
        int B_y=CalculateBminusY(caseNL, caseSP, sympair, xL, vio.second, vio.first, axis);
        if( B_y<newxL ) {newxL=B_y;}
        xL.at(vio.second)=newxL;
        // Update xL list
        UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
        // Update Lslack list
        for(int j=0;j<(int)sympair.size(); j++) 
          UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
        // Update slack list
        slack.clear(); slack=GenerateSlack(xL);
        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      }

      if( CheckIfSingleL2Violation(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis) ) {
        // x, y = (b-x-y)/2
        int B_x_y=CalculateBminusXminusY(caseNL, caseSP, sympair, xL, vio.first, vio.second, axis) / 2;
        xL.at(vio.first)+=B_x_y;
        xL.at(vio.second)+=B_x_y;
        // Update xL list
        UpdatexLwithL3(caseNL, caseSP, sympair, xL, axis);
        // Update Lslack list
        for(int j=0;j<(int)sympair.size(); j++) 
          UpdateLslackElement(caseNL, caseSP, sympair, caseNL.SBlocks.at(i).selfsym, Lslack, xL, j, axis);
        // Update slack list
        slack.clear(); slack=GenerateSlack(xL);
        //if(CheckIfLslackViolation(Lslack)) {return false;} // Violation of constraints
      }
    }
    // 7. Add edges for symmetry pairs
    for(int j=0;j<(int)sympair.size();j++) {
      if(sympair.at(j).first<(int)caseNL.GetSizeofBlocks() and sympair.at(j).second<(int)caseNL.GetSizeofBlocks()) {
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
      } else if (sympair.at(j).first==sourceNode and sympair.at(j).second==sinkNode) {
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
  }

  //cout<<!caseNL.Preplace_blocks.empty()<<endl;
  
  //added by yg
  //adding edges for preplace, abument, and alignment
  if(!caseNL.Preplace_blocks.empty()){
      for(int i=0;i<caseNL.Preplace_blocks.size();i++){
	  //AddEdgeforVertex(sourceNode, caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].distance, VGraph);  
          //cout<<"adds a preblaced blocks"<<endl;
          if(caseNL.Preplace_blocks[i].horizon==0)
          AddEdgeforVertex(caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].blockid2, caseNL.Preplace_blocks[i].distance, VGraph);
           else
           AddEdgeforVertex(caseNL.Preplace_blocks[i].blockid1, caseNL.Preplace_blocks[i].blockid2, caseNL.Preplace_blocks[i].distance, HGraph);
	  }
  }
  if(!caseNL.Alignment_blocks.empty()){
	  for(int i=0;i<caseNL.Alignment_blocks.size();i++){
//cout<<"adds a alignment blocks"<<endl;
                  if(caseNL.Alignment_blocks[i].horizon==0)
		  AddEdgeforVertex(caseNL.Alignment_blocks[i].blockid1, caseNL.Alignment_blocks[i].blockid2, caseNL.Alignment_blocks[i].distance, VGraph);
		   else
                   AddEdgeforVertex(caseNL.Alignment_blocks[i].blockid1, caseNL.Alignment_blocks[i].blockid2, caseNL.Alignment_blocks[i].distance, HGraph);
	  }
  }
  if(!caseNL.Abument_blocks.empty()){
	  for(int i=0;i<caseNL.Abument_blocks.size();i++){
//cout<<"adds a abument blocks"<<endl;
		if(caseNL.Abument_blocks[i].horizon==0){
		  AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Abument_blocks[i].distance, VGraph);
                 AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Blocks[caseNL.Abument_blocks[i].blockid1].width, HGraph);
                     }
else
{
AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Abument_blocks[i].distance, HGraph);
                 AddEdgeforVertex(caseNL.Abument_blocks[i].blockid1, caseNL.Abument_blocks[i].blockid2, caseNL.Blocks[caseNL.Abument_blocks[i].blockid1].height, VGraph);
}
	  }

  }



  return true;
}

void ConstGraph::UpdatexLwithL3(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis) {
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

int ConstGraph::CalculateBminusXminusY(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis) {
  int M;
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

int ConstGraph::CalculateBminusY(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis) {
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

bool ConstGraph::CheckIfSingleL2Violation(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis) {
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

pair<int,int> ConstGraph::CheckIfL2Violation(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis) {
  for(int j=0;j<(int)sympair.size();j++) {
  int vio;
    if( (vio=CheckIfL2ViolationUnit(caseNL, caseSP, sympair, xL, j, axis))!=-1 ) {return make_pair(j,vio);}
  }
  return make_pair(-1,-1);
}

int ConstGraph::CheckIfL2ViolationUnit(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, placerDB::Smark axis) {
  // return the index of correlated pair if any violation on L2 constraints
  // otherwise return -1
  for(int k=0;k<(int)sympair.size();k++) {
    if(j==k) {continue;}
    if( CheckIfSingleL2Violation(caseNL, caseSP, sympair, xL, j, k, axis) ) { return k; }
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

void ConstGraph::UpdateLslackElement(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector< pair<int,placerDB::Smark> >& selfsym, vector<int>& Lslack, vector<int>& xL, int j, placerDB::Smark axis) {
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
    newBdata.polygon.push_back(tmpp);
    if((it->x)<x) {x=it->x;}
    if((it->x)>X) {X=it->x;}
    if((it->y)<y) {y=it->y;}
    if((it->y)>Y) {Y=it->y;}
  }
  newBdata.LL.x=x; newBdata.LL.y=y;
  newBdata.UL.x=x; newBdata.UL.y=Y;
  newBdata.UR.x=X; newBdata.UR.y=Y;
  newBdata.LR.x=X; newBdata.LR.y=y;
  return newBdata;
}

PnRDB::point ConstGraph::ConvertPointData(placerDB::point Pdata) {
  PnRDB::point newPdata;
  newPdata.x=Pdata.x; newPdata.y=Pdata.y;
  return newPdata;
}

void ConstGraph::UpdateHierNode(design& caseNL, SeqPair& caseSP, PnRDB::hierNode& node) {
  vector<vector<placerDB::point> > boundary;
  vector<placerDB::point> center;
  vector<placerDB::point> bbox;
  placerDB::point bpoint;

  node.width=HGraph.at(sinkNode).position;
  node.height=VGraph.at(sinkNode).position;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    int x=HGraph.at(i).position;
    int y=VGraph.at(i).position;
    placerDB::point LL={x,y};
    placerDB::Omark ort=caseSP.GetBlockOrient(i);
    bbox=caseNL.GetPlacedBlockAbsBoundary(i, ort, LL);
    bpoint=caseNL.GetBlockAbsCenter(i, ort, LL);
    node.Blocks.at(i).instance.orient=PnRDB::Omark(ort);
    node.Blocks.at(i).instance.placedBox=ConvertBoundaryData(bbox);
    node.Blocks.at(i).instance.placedCenter=ConvertPointData(bpoint);
    for(int j=0;j<caseNL.GetBlockPinNum(i);j++) {
      boundary=caseNL.GetPlacedBlockPinAbsBoundary(i, j, ort, LL);
      center=caseNL.GetPlacedBlockPinAbsPosition(i, j, ort, LL);
      // [wbxu] Following two lines have be updated for multiple contacts
      // update pin contacts
      for(int k=0;k<(int)node.Blocks.at(i).instance.blockPins.at(j).pinContacts.size();k++) {

        node.Blocks.at(i).instance.blockPins.at(j).pinContacts.at(k).placedBox=ConvertBoundaryData(boundary.at(k));
        node.Blocks.at(i).instance.blockPins.at(j).pinContacts.at(k).placedCenter=ConvertPointData(center.at(k));
      }
      // update pin vias
      for(int k=0;k<(int)node.Blocks.at(i).instance.blockPins.at(j).pinVias.size();k++) {
        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).placedpos=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).originpos, LL);
        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.originBox, LL);
        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.originBox, LL);
        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.originBox, LL);
        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).UpperMetalRect.originCenter, LL);
        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).LowerMetalRect.originCenter, LL);
        node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.blockPins.at(j).pinVias.at(k).ViaRect.originCenter, LL);
      }
    }
  // [wbxu] Complete programing: to update internal metals
    // update internal metals
    for(int j=0;j<(int)node.Blocks.at(i).instance.interMetals.size();j++) {
      node.Blocks.at(i).instance.interMetals.at(j).placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interMetals.at(j).originBox, LL);
      node.Blocks.at(i).instance.interMetals.at(j).placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interMetals.at(j).originCenter, LL);
    }
    // update internal vias
    for(int j=0;j<(int)node.Blocks.at(i).instance.interVias.size();j++) {
      node.Blocks.at(i).instance.interVias.at(j).placedpos=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).originpos,LL);
      node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.originBox,LL);
      node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.originBox,LL);
      node.Blocks.at(i).instance.interVias.at(j).ViaRect.placedBox=caseNL.GetPlacedBlockInterMetalAbsBox(i, ort, node.Blocks.at(i).instance.interVias.at(j).ViaRect.originBox,LL);
      node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).UpperMetalRect.originCenter,LL);
      node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).LowerMetalRect.originCenter,LL);
      node.Blocks.at(i).instance.interVias.at(j).ViaRect.placedCenter=caseNL.GetPlacedBlockInterMetalAbsPoint(i, ort, node.Blocks.at(i).instance.interVias.at(j).ViaRect.originCenter,LL);
    }
  }
  // [wbxu] Complete programing: to update terminal for top-level
  if(node.isTop) {
    for(int i=0;i<(int)caseNL.GetSizeofTerminals();i++) {
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
}

void ConstGraph::updateTerminalCenter(design& caseNL, SeqPair& caseSP) {
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
        p_pin=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp);
		for(int i=0;i<p_pin.size();i++){
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

void ConstGraph::WritePlacement(design& caseNL, SeqPair& caseSP, string outfile) {
  ofstream fout;
  fout.open(outfile.c_str());
  cout<<"Placer-Info: write placement"<<endl;
  fout<<"# TAMU blocks 1.0"<<endl<<endl;
  fout<<"DIE {"<<HGraph.at(sourceNode).position<<", "<<VGraph.at(sourceNode).position<<"} {"<<HGraph.at(sinkNode).position<<", "<<VGraph.at(sinkNode).position<<"}"<<endl<<endl;
  for(int i=0;i<(int)caseNL.GetSizeofBlocks();++i) {
    int x,y; string ort;
    switch(caseSP.GetBlockOrient(i)) {
      case placerDB::N: x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="N";
              break;
      case placerDB::S: x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i)); 
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i));
              ort="S";
              break;
      case placerDB::W: x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i));
              y=VGraph.at(i).position; 
              ort="W";
              break;
      case placerDB::E: x=HGraph.at(i).position;
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i));
              ort="E";
              break;
      case placerDB::FN:x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i));
              y=VGraph.at(i).position; 
              ort="FN";
              break;
      case placerDB::FS:x=HGraph.at(i).position;
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i));
              ort="FS";
              break;
      case placerDB::FW:x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="FW";
              break;
      case placerDB::FE:x=HGraph.at(i).position+caseNL.GetBlockWidth(i,caseSP.GetBlockOrient(i)); 
              y=VGraph.at(i).position+caseNL.GetBlockHeight(i,caseSP.GetBlockOrient(i));
              ort="FE";
              break;
      default:x=HGraph.at(i).position; 
              y=VGraph.at(i).position; 
              ort="N";
              break;
    }
    fout<<caseNL.Blocks.at(i).name<<"\t"<<x<<"\t"<<y<<"\t"<<ort<<endl;
  }
  fout<<endl;
  int Xmax=HGraph.at(sinkNode).position;
  int Ymax=VGraph.at(sinkNode).position;
  placerDB::point p, bp;
  //cout<<"writeplacement3"<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int distTerm=-1*NINF;
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
  cout<<"Placer-Info: create gnuplot file"<<endl;
  //int Xmax=HGraph.at(sinkNode).position;
  //int Ymax=VGraph.at(sinkNode).position;
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
    placerDB::point ntp=caseNL.GetBlockAbsCenter(i, caseSP.GetBlockOrient(i), tp);
    fout<<"\nset label \""<<caseNL.GetBlockName(i)<<"\" at "<<ntp.x<<" , "<<ntp.y<<" center "<<endl;
    for(int j=0;j<caseNL.GetBlockPinNum(i);j++) {
      p_pin =caseNL.GetPlacedBlockPinAbsPosition(i,j,caseSP.GetBlockOrient(i), tp);
	  for(int k = 0; k<p_pin.size();k++){
      placerDB::point newp = p_pin[k];
      fout<<"\nset label \""<<caseNL.GetBlockPinName(i,j)<<"\" at "<<newp.x<<" , "<<newp.y<<endl;
      fout<<endl;
	  }
    }
  }
  // set labels for terminals
  //cout<<"set labels for terminals..."<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    int distTerm=-1*NINF;
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
    int x,y; string ort;
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    //vector<point> newp=caseNL.GetPlacedBlockAbsBoundary(i, E, tp);
    vector<placerDB::point> newp=caseNL.GetPlacedBlockAbsBoundary(i, caseSP.GetBlockOrient(i), tp);
	
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
    int x,y; string ort;
    placerDB::point tp;
    tp.x=HGraph.at(i).position;
    tp.y=VGraph.at(i).position;
    for(int j=0;j<caseNL.GetBlockPinNum(i);j++) {
      newp_pin=caseNL.GetPlacedBlockPinAbsBoundary(i,j, caseSP.GetBlockOrient(i), tp);
      for(int k=0;k<newp_pin.size();k++){
	  vector<placerDB::point> newp_p = newp_pin[k];
      for(int it=0; it<(int)newp_p.size(); it++ ) {
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
    int distTerm=-1*NINF;
    int tno; placerDB::point tp;
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
  fout<<"\nEOF"<<endl;

  // plot nets
  //cout<<"plot nets..."<<endl;
  for(vector<placerDB::net>::iterator ni=caseNL.Nets.begin(); ni!=caseNL.Nets.end(); ++ni) {
    bool hasTerminal=false;
    //int distTerm=-1*NINF;
    int tno; placerDB::point tp;
    vector<placerDB::point> pins;
    pins.clear();
    // for each pin
    for(vector<placerDB::Node>::iterator ci=(ni->connected).begin(); ci!=(ni->connected).end(); ++ci) {
      if(ci->type==placerDB::Block) {
        bp.x=this->HGraph.at(ci->iter2).position;
        bp.y=this->VGraph.at(ci->iter2).position;
        p_pin=caseNL.GetPlacedBlockPinAbsPosition(ci->iter2, ci->iter, caseSP.GetBlockOrient(ci->iter2), bp);

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
