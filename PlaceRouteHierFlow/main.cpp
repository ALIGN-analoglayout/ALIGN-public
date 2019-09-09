#include <string>
#include <iostream>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/Router.h"
#include "./cap_placer/capplacer.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <sstream>

using std::string;
using std::cout;
using std::endl;

double ConstGraph::LAMBDA=1000;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=100;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=1500;

static void route_single_variant( PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::hierNode& current_node, int idx, int lidx, const string& opath, const string& binary_directory)
{
  std::cout<<"Checkpoint: work on layout "<<lidx<<std::endl;
  DB.Extract_RemovePowerPins(current_node);

  std::cout<<"Checkpoint : before route"<<std::endl;
  DB.PrintHierNode(current_node);

  DB.WriteJSON (current_node, true, false, false, false, current_node.name+"_PL_"+std::to_string(lidx), drcInfo, opath); //block net powernet powergrid

  Router curr_route;

  bool NEW_GLOBAL_ROUTER = 1;

  if ( NEW_GLOBAL_ROUTER) {
    // Gcell Global Routing
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".pre_gr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }

    std::cout<<"Starting Gcell Global Routing"<<std::endl;
    curr_route.RouteWork(4, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    std::cout<<"Ending Gcell Global Routing"<<std::endl;
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".post_gr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".pre_dr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }
    std::cout<<"Starting Gcell Detail Routing"<<std::endl;
    curr_route.RouteWork(5, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    std::cout<<"Ending Gcell Detail Routing"<<std::endl;
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".post_dr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }


  } else {
    // Global Routing (old version)
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".pre_gr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }
    std::cout<<"Checkpoint : global route"<<std::endl;
    curr_route.RouteWork(0, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    std::cout<<"Checkpoint : after global route"<<std::endl;
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".post_gr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }

    DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_GR_"+std::to_string(lidx), drcInfo, opath);
    // The following line is used to write global route results for Intel router (only for old version)
    DB.WriteGlobalRoute(current_node, current_node.name+"_GlobalRoute_"+std::to_string(lidx)+".json", opath);

    // Detail Routing
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".pre_dr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }
    std::cout<<"Checkpoint : detail route"<<std::endl;
    curr_route.RouteWork(1, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    std::cout<<"Checkpoint : after detail route"<<std::endl;
    {
      const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".post_dr.db.json";
      DB.WriteDBJSON(current_node,ofn);
    }

  }

  DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_DR_"+std::to_string(lidx), drcInfo, opath);

  if(current_node.isTop){
    std::cout<<"Checkpoint : Starting Power Grid Creation"<<std::endl;
    curr_route.RouteWork(2, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 5, 6, binary_directory);
    std::cout<<"Checkpoint : End Power Grid Creation"<<std::endl;

    DB.WriteJSON (current_node, true, true, false, true, current_node.name+"_PG_"+std::to_string(lidx), drcInfo, opath);
        
    std::cout<<"Checkpoint : Starting Power Routing"<<std::endl;
    curr_route.RouteWork(3, current_node, const_cast<PnRDB::Drc_info&>(drcInfo), 1, 6, binary_directory);
    std::cout<<"Checkpoint : End Power Grid Routing"<<std::endl;

    DB.WriteJSON (current_node, true, false, true, true, current_node.name+"_PR_"+std::to_string(lidx), drcInfo, opath);
        
  }

  DB.WriteJSON (current_node, true, true, true, true, current_node.name+"_"+std::to_string(lidx), drcInfo, opath);
  std::cout<<"Check point : before checkin\n";
  DB.PrintHierNode(current_node);
      
  const string ofn = opath+current_node.name+"_"+std::to_string(lidx) + ".db.json";
  DB.WriteDBJSON(current_node,ofn);

  std::ostringstream oss;
  oss << "gen_viewer_json.py"
      << " -b " << current_node.name
      << " -v " << lidx
      << " -d " << opath
      << " -o " << opath;
  string cmd(oss.str());

  int rc = system( cmd.c_str());
  std::cout << cmd << " returned " << rc << std::endl;
  
  PnRDB::hierNode current_node2;

  DB.ReadDBJSON( current_node2,ofn);
  DB.WriteDBJSON( current_node2,ofn+"2");

  DB.WriteLef(current_node, current_node.name+"_"+std::to_string(lidx)+".lef", opath);
  DB.CheckinHierNode(idx, current_node);

}


int main(int argc, char** argv ){
  string opath="./Results/";
  string fpath=argv[1];
  string lfile=argv[2];
  string vfile=argv[3];
  string mfile=argv[4];
  string dfile=argv[5];
  string topcell=argv[6];
  int numLayout=std::stoi(argv[7]);
  int effort=std::stoi(argv[8]);
  if(fpath.back()=='/') {fpath.erase(fpath.end()-1);}
  if(opath.back()!='/') {opath+="/";}

  // Following codes try to get the path of binary codes
  string binary_directory = argv[0];
  cout <<"argv[0]: "<<binary_directory <<endl;
  int beginIdx = binary_directory.rfind('/');//find the last slash
  string str_lastOne = binary_directory.substr(beginIdx+1);
  cout <<"string after last slash: "<<str_lastOne <<endl;
  binary_directory = binary_directory.erase(beginIdx+1);
  cout <<"binary_directory: "<< binary_directory <<endl;

  mkdir(opath.c_str(), 0777);

  PnRdatabase DB(fpath, topcell, vfile, lfile, mfile, dfile); // construction of database
  PnRDB::Drc_info drcInfo=DB.getDrc_info();
  map<string, PnRDB::lefMacro> lefData = DB.checkoutSingleLEF();
  queue<int> Q=DB.TraverseHierTree(); // traverse hierarchical tree in topological order

  while (!Q.empty())
  {
    int idx=Q.front();
    cout<<"Main-Info: start to work on node "<<idx<<endl;
    PnRDB::hierNode current_node=DB.CheckoutHierNode(idx);
    DB.PrintHierNode(current_node);

    DB.AddingPowerPins(current_node);

    Placer_Router_Cap PRC(opath, fpath, current_node, drcInfo, lefData, 1, 1, 6); //dummy, aspect ratio, number of aspect retio

    std::cout<<"Checkpoint : before place"<<std::endl;
    DB.PrintHierNode(current_node);
    DB.WriteDBJSON(current_node,opath+current_node.name+ ".db.json");
    
    // Placement
    std::vector<PnRDB::hierNode> nodeVec(numLayout, current_node);
    Placer curr_plc(nodeVec, opath, effort); // do placement and update data in current node
    std::cout<<"Checkpoint: generated "<<nodeVec.size()<<" placements\n";
    for(unsigned int lidx=0; lidx<nodeVec.size(); ++lidx) {
      route_single_variant( DB, drcInfo, nodeVec[lidx], idx, lidx, opath, binary_directory);
    }

    Q.pop();
    cout<<"Main-Info: complete node "<<idx<<endl;
  }

  return 0;
}
