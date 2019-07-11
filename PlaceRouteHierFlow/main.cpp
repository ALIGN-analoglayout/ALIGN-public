#include <string>
#include <iostream>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/Router.h"
#include "./cap_placer/capplacer.h"
#include <sys/types.h>
#include <sys/stat.h>
//#include <boost/program_options.hpp>
//#include "./cap_placer/Capdatatype.h"

using std::string;
using std::cout;
using std::endl;
//using namespace boost;

double ConstGraph::LAMBDA=1000;
double ConstGraph::GAMAR=30;
double ConstGraph::BETA=100;
double ConstGraph::SIGMA=1000;
double ConstGraph::PHI=1500;

//template<class T>
//std::ostream& operator<<(std::ostream& os, const std::vector<T>& v)
//{
//    std::copy(v.begin(), v.end(), std::ostream_iterator<T>(os, " "));
//    return os;
//}

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
  //string opath;
  //string fpath;
  //string lfile;
  //string vfile;
  //string mfile;
  //string dfile;
  //string topcell;
  //int effort;
  //int numLayout;

  //boost::program_options::options_description desc("Allowed options");
  //desc.add_options()
  //    ("help,h", "produce help message")
  //    ("inputDir,I", boost::program_options::value<std::string>(&fpath)->required(),
  //          "directory of input data")
  //    ("outputDir,O", boost::program_options::value<string>(&opath)->default_value("./Results"),
  //          "directory of output data, default folder is './Results'")
  //    ("lef", boost::program_options::value<string >(&lfile)->required(), 
  //          "LEF file")
  //    ("verilog", boost::program_options::value<string >(&vfile)->required(), 
  //          "Verilog file")
  //    ("map", boost::program_options::value<string >(&mfile)->required(), 
  //          "mapping file")
  //    ("pdk", boost::program_options::value<string >(&dfile)->required(), 
  //          "PDK abstraction file")
  //    ("topDesign", boost::program_options::value<string >(&topcell)->required(), 
  //          "top name")
  //    ("maxLayout", boost::program_options::value<int>(&numLayout)->default_value(1),
  //          "maximum number of output layouts, default value is 1")
  //    ("effort", boost::program_options::value<int>(&effort)->default_value(0),
  //          "optimization effort in range [0, 2], default value is 0")
  //    //("verbose,v", boost::program_options::value<int>()->implicit_value(1)->default_value(0),
  //    //      "enable verbosity (optionally specify level)")
  //;
  //boost::program_options::variables_map vm;

  //try {
  //  boost::program_options::store(boost::program_options::command_line_parser(argc, argv).options(desc).run(), vm);
  //  if (vm.count("help")) {
  //      cout << "USAGE:\n";
  //      cout << desc;
  //      return 0;
  //  }
  //  boost::program_options::notify(vm);

  //  std::cout<<"Info: Input directory is "<<fpath<<std::endl;
  //  std::cout<<"Info: Output directory is "<<opath<<std::endl;
  //  std::cout<<"Info: Maximum number of output layouts "<<numLayout<<std::endl;
  //  std::cout<<"Info: LEF file is "<<lfile<<std::endl;
  //  std::cout<<"Info: PDK abstraction file is "<<dfile<<std::endl;
  //  std::cout<<"Info: Verilog file is "<<vfile<<std::endl;
  //  std::cout<<"Info: Mapping file is "<<mfile<<std::endl;
  //  std::cout<<"Info: Top design name is "<<topcell<<std::endl;
  //  std::cout<<"Info: Optimization effort is "<<effort<<std::endl;
  //}
  //catch(std::exception& e)
  //{
  //    cout << e.what() << "\n";
  //    return 1;
  //}
  if(fpath.back()=='/') {fpath.erase(fpath.end()-1);}
  if(opath.back()!='/') {opath+="/";}

  // Following codes try to get the path of binary codes
  string binary_directory;
  binary_directory = argv[0];
  cout <<"argv[0]: "<<binary_directory <<endl;
  int beginIdx = binary_directory.rfind('/');//find the last slash
  string str_lastOne = binary_directory.substr(beginIdx+1);
  cout <<"string after last slash: "<<str_lastOne <<endl;
  binary_directory = binary_directory.erase(beginIdx+1);
  cout <<"binary_directory: "<< binary_directory <<endl;

  mkdir(opath.c_str(), 0777);
  //int status = mkdir(opath.c_str(), 0777);
  //struct stat info;
  //if( stat( opath.c_str(), &info ) != 0 ) {
  //    int status = mkdir(opath.c_str(), 0777);
  //    printf( "Create directory %s\n", opath.c_str() );
  //} else if( info.st_mode & S_IFDIR ) {
  //    printf( "%s is a directory\n", opath.c_str() );
  //} else {
  //    printf( "%s is no directory\n", opath.c_str() );
  //}

  PnRdatabase DB(fpath, topcell, vfile, lfile, mfile, dfile); // construction of database
  //PnRDB::designRule design_rule=DB.getDesignRule(); 
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

    Placer_Router_Cap PRC(opath, fpath, current_node, drcInfo, lefData, 0, 1, 6); //dummy, aspect ratio, number of aspect retio

    std::cout<<"Checkpoint : before place"<<std::endl;
    DB.PrintHierNode(current_node);
    
    std::vector<PnRDB::hierNode> nodeVec;
    for(int k=0;k<numLayout;++k) {nodeVec.push_back(current_node);}
    // Placement
    Placer curr_plc(nodeVec, opath, effort); // do placement and update data in current node
    //std::cout<<"Checkpoint: place "<<nodeVec.size()<<" layouts\n";
    for(std::vector<PnRDB::hierNode>::iterator vit=nodeVec.begin(); vit!=nodeVec.end(); ++vit) {
      current_node=(*vit);
      int lidx=vit-nodeVec.begin();
      std::cout<<"Checkpoint: work on layout "<<lidx<<std::endl;
      DB.Extract_RemovePowerPins(current_node);

      std::cout<<"Checkpoint : before route"<<std::endl;
      DB.PrintHierNode(current_node);
      //    DB.WriteGDS(current_node, true, false, false, false, current_node.name+"_PL", drcInfo); //block net powernet powergrid
      DB.WriteJSON (current_node, true, false, false, false, current_node.name+"_PL_"+std::to_string(lidx), drcInfo, opath); //block net powernet powergrid

      Router curr_route;

      #ifndef GROUTER
      std::cout<<"Starting Gcell Global Routing"<<std::endl;
      // Gcell Global Routing
      curr_route.RouteWork(4, current_node, drcInfo, 0, 6, binary_directory);
      std::cout<<"Ending Gcell Global Routing"<<std::endl;

      std::cout<<"Starting Gcell Detail Routing"<<std::endl;
      curr_route.RouteWork(5, current_node, drcInfo, 0, 6, binary_directory);
      DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_DR_"+std::to_string(lidx), drcInfo, opath);
      std::cout<<"Ending Gcell Detail Routing"<<std::endl;


      if(current_node.isTop){
        std::cout<<"Checkpoint : Starting Power Grid Creation"<<std::endl;
        curr_route.RouteWork(2, current_node, drcInfo, 5, 6, binary_directory);
        std::cout<<"Checkpoint : End Power Grid Creation"<<std::endl;

        //      DB.WriteGDS(current_node, true, true, false, true, current_node.name+"_PG", drcInfo);
        DB.WriteJSON (current_node, true, true, false, true, current_node.name+"_PG_"+std::to_string(lidx), drcInfo, opath);
        
        std::cout<<"Checkpoint : Starting Power Routing"<<std::endl;
        curr_route.RouteWork(3, current_node, drcInfo, 1, 6, binary_directory);
        std::cout<<"Checkpoint : End Power Grid Routing"<<std::endl;

        //      DB.WriteGDS(current_node, true, false, true, true, current_node.name+"_PR", drcInfo);
        DB.WriteJSON (current_node, true, false, true, true, current_node.name+"_PR_"+std::to_string(lidx), drcInfo, opath);
        
        }
  
      //    DB.WriteGDS(current_node, true, true, true, true, current_node.name, drcInfo);
      DB.WriteJSON (current_node, true, true, true, true, current_node.name+"_"+std::to_string(lidx), drcInfo, opath);
      std::cout<<"Check point : before checkin\n";
      DB.PrintHierNode(current_node);


      #endif
      #ifdef GROUTER      
      // wbxu: The following codes are for old version of global router
      //
      // Global Routing

      curr_route.RouteWork(0, current_node, drcInfo, 1, 6, binary_directory);
      std::cout<<"Checkpoint : after global route"<<std::endl;
      DB.PrintHierNode(current_node);

      //    DB.WriteGDS(current_node, true, true, false, false, current_node.name+"_GR", drcInfo);
      DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_GR_"+std::to_string(lidx), drcInfo, opath);
      // wbxu: the following line is used to write global route results for Intel router
      // Old version of global router should be used.
      DB.WriteGlobalRoute(current_node, current_node.name+"_GlobalRoute_"+std::to_string(lidx)+".json", opath);

      // Detail Routing
      std::cout<<"Checkpoint : detail route"<<std::endl;
      curr_route.RouteWork(1, current_node, drcInfo, 1, 6, binary_directory);
      std::cout<<"Checkpoint : after detail route"<<std::endl;
      DB.PrintHierNode(current_node);

      //    DB.WriteGDS(current_node, true, true, false, false, current_node.name+"_DR", drcInfo);
      DB.WriteJSON (current_node, true, true, false, false, current_node.name+"_DR_"+std::to_string(lidx), drcInfo, opath);

      if(current_node.isTop){
        std::cout<<"Checkpoint : Starting Power Grid Creation"<<std::endl;
        curr_route.RouteWork(2, current_node, drcInfo, 5, 6, binary_directory);
        std::cout<<"Checkpoint : End Power Grid Creation"<<std::endl;

        //      DB.WriteGDS(current_node, true, true, false, true, current_node.name+"_PG", drcInfo);
        DB.WriteJSON (current_node, true, true, false, true, current_node.name+"_PG_"+std::to_string(lidx), drcInfo, opath);
        
        std::cout<<"Checkpoint : Starting Power Routing"<<std::endl;
        curr_route.RouteWork(3, current_node, drcInfo, 1, 6, binary_directory);
        std::cout<<"Checkpoint : End Power Grid Routing"<<std::endl;

        //      DB.WriteGDS(current_node, true, false, true, true, current_node.name+"_PR", drcInfo);
        DB.WriteJSON (current_node, true, false, true, true, current_node.name+"_PR_"+std::to_string(lidx), drcInfo, opath);
        
        }
  
      //    DB.WriteGDS(current_node, true, true, true, true, current_node.name, drcInfo);
      DB.WriteJSON (current_node, true, true, true, true, current_node.name+"_"+std::to_string(lidx), drcInfo, opath);
      std::cout<<"Check point : before checkin\n";
      DB.PrintHierNode(current_node);
      // Update node
      #endif
      DB.CheckinHierNode(idx, current_node);
      //return 0;
    }

    Q.pop();
    cout<<"Main-Info: complete node "<<idx<<endl;
  }

  return 0;
}
