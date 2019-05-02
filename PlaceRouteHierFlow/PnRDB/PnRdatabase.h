#ifndef PNRDATABASE_H_
#define PNRDATABASE_H_

#include <ctime>
#include <map>
#include <vector>
#include <queue>
#include <string>
#include <limits.h>
#include <cstdlib>
#include <cctype>
#include <iostream>
#include <fstream> // std::ifstream
#include <stdlib.h>
#include <utility> // pair, make_pair
#include <algorithm>
#include <sstream>
#include <unistd.h>
#include <set>
#include "datatype.h"
#include "readfile.h"
//#include "../GDSWriter/GdsWriter.h"
//#include "../GDSWriter/GdsReader.h"
//#include "../GDSWriter/GdsRecords.h"
//#include "../GDSWriter/GdsDriver.h"
//#include "../GDSWriter/EnumDataBase.h"
//#include "../GDSWriter/String.h"

using std::map;
using std::vector;
using std::queue;
using std::string;
using std::cout;
using std::endl;
using std::pair;
using std::cerr;
using std::ifstream;
using std::max_element;

/*
/// @brief test enum callbacks
struct EnumDataBase : public GdsParser::GdsDataBaseKernel
{
//{{{
    /// @brief constructor 
    EnumDataBase()
    {
        cout << "constructing EnumDataBase" << endl;
    }
    ///////////////////// required callbacks /////////////////////
    /// @brief bit array callback 
    /// @param record_type record 
    /// @param data_type data type 
    /// @param vBitArray data array  
    virtual void bit_array_cbk(GdsParser::GdsRecords::EnumType record_type, GdsParser::GdsData::EnumType data_type, vector<int> const& vBitArray)
    {
        cout << __func__ << endl;
        this->general_cbk(record_type, data_type, vBitArray);
    }
    /// @brief 2-byte integer callback 
    /// @param record_type record 
    /// @param data_type data type 
    /// @param vInteger data array  
    virtual void integer_2_cbk(GdsParser::GdsRecords::EnumType record_type, GdsParser::GdsData::EnumType data_type, vector<int> const& vInteger)
    {
        cout << __func__ << endl;
        this->general_cbk(record_type, data_type, vInteger);
    }
    /// @brief 4-byte integer callback 
    /// @param record_type record 
    /// @param data_type data type 
    /// @param vInteger data array  
    virtual void integer_4_cbk(GdsParser::GdsRecords::EnumType record_type, GdsParser::GdsData::EnumType data_type, vector<int> const& vInteger)
    {
        cout << __func__ << endl;
        this->general_cbk(record_type, data_type, vInteger);
    }
    /// @brief 4-byte floating point number callback 
    /// @param record_type record 
    /// @param data_type data type 
    /// @param vFloat data array  
    virtual void real_4_cbk(GdsParser::GdsRecords::EnumType record_type, GdsParser::GdsData::EnumType data_type, vector<double> const& vFloat) 
    {
        cout << __func__ << endl;
        this->general_cbk(record_type, data_type, vFloat);
    }
    /// @brief 8-byte floating point number callback 
    /// @param record_type record 
    /// @param data_type data type 
    /// @param vFloat data array  
    virtual void real_8_cbk(GdsParser::GdsRecords::EnumType record_type, GdsParser::GdsData::EnumType data_type, vector<double> const& vFloat) 
    {
        cout << __func__ << endl;
        this->general_cbk(record_type, data_type, vFloat);
    }
    /// @brief string callback 
    /// @param record_type record 
    /// @param data_type data type 
    /// @param str data 
    virtual void string_cbk(GdsParser::GdsRecords::EnumType record_type, GdsParser::GdsData::EnumType data_type, string const& str) 
    {
        cout << __func__ << endl;
        this->general_cbk(record_type, data_type, str);
    }
    /// @brief begin or end indicator of a block 
    /// @param record_type record 
    virtual void begin_end_cbk(GdsParser::GdsRecords::EnumType record_type)
    {
        cout << __func__ << endl;
        this->general_cbk(record_type, GdsParser::GdsData::NO_DATA, vector<int>(0));
    }

    /// @brief A generic callback function handles all other callback functions. 
    /// It is not efficient but concise as a demo. 
    /// @tparam ContainerType container type 
    /// @param record_type record 
    /// @param data_type data type 
    /// @param data data values 
    template <typename ContainerType>
    void general_cbk(GdsParser::GdsRecords::EnumType record_type, GdsParser::GdsData::EnumType data_type, ContainerType const& data)
    {
        cout << "ascii_record_type: " << GdsParser::gds_record_ascii(record_type) << endl
            << "ascii_data_type: " << GdsParser::gds_data_ascii(data_type) << endl 
            << "data size: " << data.size() << endl;
		//GdsParser::GdsCell GDSCELL;
		//std::stringstream oss;
		switch (record_type)
        {
            case GdsParser::GdsRecords::UNITS:
				break;
            case GdsParser::GdsRecords::STRNAME:
				//std::copy(data.begin(), data.end(), std::ostream_iterator<char>(oss));
				//GDSCELL.cell_name = oss.str();
				//cout <<	"Cell Name: "<<GDSCELL.cell_name <<endl;
				break;
            case GdsParser::GdsRecords::BOUNDARY:
                break;
            case GdsParser::GdsRecords::LAYER:
                cout << "LAYER = " << data[0] <<  endl;
                break;
            case GdsParser::GdsRecords::XY:
                for (typename ContainerType::const_iterator it = data.begin(); it != data.end(); ++it)
                    cout << *it << " "; 
                cout << endl; 
                cout << data.size() << endl;
                break;
            case GdsParser::GdsRecords::ENDEL:
                break;
            default:
                break;
        }
    }
//}}}
};
*/

class PnRdatabase
{
  private:
    int maxNode;
    int unitScale;
    int topidx;
    PnRDB::Drc_info DRC_info;
    vector<PnRDB::hierNode> hierTree;
    map<string, PnRDB::lefMacro> lefData;
    map<string, string> gdsData;
    PnRDB::designRule drData;

    void UpdateHierNodeParent(int nodeID); // update parent node of current node
    void TraverseDFS(queue<int>& Q, vector<string>& color, int idx); // DFS subfunc to traverse hierarchical tree 
    long int get_number(string str);

	////added by ya
	//
 	//void readRandConstFile(string random_const_file);
	////above is added by yg

    //void readBlockFile(string blockfile);
    //void readNetFile(string netfile);
    //void readConstFile(string cfile);
    //void constructSymmGroup();
    //point GetPlacedPosition(point oldp, int width, int height, Omark ort); // Get location of any point of block when placed
    //pair<int,int> checkSympairInSymmBlock(vector< pair<int,int> >& Tsympair);
    //pair<int,int> checkSelfsymInSymmBlock(vector< pair<int,Smark> >& Tselfsym);

  public:
    // default constructor
    inline PnRdatabase() {unitScale=2000;maxNode=0;};
    // constructor with augments
    PnRdatabase(string path, string topcell, string vname, string lefname, string mapname, string drname);
    // constructor with augments
    //PnRdatabase(string path, string topcell, string netlistFile, string constFile, string random_const_file);
    // constructor with augments
    //PnRdatabase(string path, string topcell, string netlistFile, string constFile, string random_const_file, int write_out_flag);
    // destructor
    inline ~PnRdatabase() {hierTree.clear(); lefData.clear(); gdsData.clear();};
    PnRdatabase(const PnRdatabase& other); // copy constructor
    PnRdatabase& operator= (const PnRdatabase& other); // copy assignment function
    queue<int> TraverseHierTree(); // traverse hierarchical tree in topological order
    PnRDB::hierNode CheckoutHierNode(int nodeID); // check out data of specific hierarchical node
    void CheckinHierNode(int nodeID, PnRDB::hierNode& updatedNode); // check out data of specific hierarchical node
    void updatePowerPins(PnRDB::pin& temp_pin);
   
    bool ReadVerilog(string fpath, string vname, string topcell);
    //bool ReadVerilog(string verilogfile, string topcell);
    bool ReadLEF(string leffile); // read building block data from LEF file
    void PrintLEFData();  // print LEF data for debugging
    bool ReadConstraint(PnRDB::hierNode& node, string fpath, string suffix);
    bool MergeLEFMapData(PnRDB::hierNode& node);
    void PrintHierTree();
    bool ReadMap(string fpath, string mapname); // read gds data from map file
    bool ReadDesignRule(string drfile); //  read design rule data from design rule file
    bool HardDesignRule(); // hard-code design rules
	//+Jinhyun	
	PnRDB::designRule getDesignRule(){ return drData;};	
    //added by yg
    PnRDB::Drc_info getDrc_info(){return DRC_info;};
    // Interface for detail router II - wbxu
    void WritePlaceRoute(PnRDB::hierNode& node, string pofile, string rofile);
    void PrintDesignRuleData();
    //    void GDSReaderWriterTxTFile_extension(string GDSData, GdsParser::GdsWriter& gw, long int& rndnum, vector<string>& strBlocks, vector<int>& llx, vector<int>& lly, vector<int>& urx, vector<int>& ury);
    //    std::string WriteGDS(PnRDB::hierNode& node, bool includeBlock, bool includeNet, bool includePowerNet, bool includePowerGrid, std::string gdsName, PnRDB::Drc_info& drc_info);
    //    void labelTerminals(PnRDB::hierNode& node, GdsParser::GdsWriter& gw, PnRDB::Drc_info& drc_info);//jinhyun 
    void PrintHierNode(PnRDB::hierNode& node);
    void PrintContact(PnRDB::contact& cont);
    void PrintVia(PnRDB::Via& v);
    void PrintMetal(PnRDB::Metal& m);
    void PrintBlock(PnRDB::blockComplex& bc);
    void PrintNet(PnRDB::net& n);
    void PrintTerminal(PnRDB::terminal& t);
    void PrintBlockPin(PnRDB::pin& p);
    void AddingPowerPins(PnRDB::hierNode &node);
    void Extract_RemovePowerPins(PnRDB::hierNode &node);
    //design(string blockfile, string netfile);
    //design(string blockfile, string netfile, string cfile);
    //
    //// added by yg, the first one is to read in additional const, the other one is to generate random constrains.
    //    design(string blockfile, string netfile, string cfile, string random_const_file);
    //    design(string blockfile, string netfile, string cfile, string random_const_file, int write_out_flag);


    //design(const design& other);
    //design& operator= (const design& other);

    //// generate_random_const file by yg
    //    
    //    void Generate_random_const(string random_constrain_file);
    //    
    //    //
    //
    //int GetSizeofBlocks();
    //int GetSizeofTerminals();
    //int GetSizeofNets();
    //int GetSizeofSBlocks();
    //int GetBlockSymmGroup(int blockid);
    //int GetBlockCounterpart(int blockid);
    //void PrintBlocks();
    //void PrintTerminals();
    //void PrintNets();
    //void PrintConstraints();
    //void PrintSymmGroup();
    //void PrintDesign();
    //vector<int> GetBlockListfromSymmGroup(int sgid);
    //vector<int> GetRealBlockListfromSymmGroup(int sgid);
    //vector<int> GetRealBlockPlusAxisListfromSymmGroup(int sgid);
    //string GetBlockName(int blockid);
    //string GetBlockPinName(int blockid, int pinid);
    //string GetTerminalName(int termid);
    //int GetBlockPinNum(int blockid);
    //int bias_graph = 100;
    //int GetBlockWidth(int blockid, Omark ort); // Get width of block when it's placed
    //int GetBlockHeight(int blockid, Omark ort); // Get height of block when it's placed
    //point GetBlockCenter(int blockid, Omark ort); // Get relative location of block center when it's placed at origin
    //point GetBlockAbsCenter(int blockid, Omark ort, point LL); // Get absolute location of block center when it's placed at LL
    //point GetPlacedBlockPinRelPosition(int blockid, int pinid, Omark ort); // Get pin position of block when it's placed at origin
    //point GetPlacedBlockPinAbsPosition(int blockid, int pinid, Omark ort, point LL); // Get pin position of block when it's placed at LL
    //vector<point> GetPlacedBlockRelBoundary(int blockid, Omark ort); // Get block boundary when it's placed at origin
    //vector<point> GetPlacedBlockAbsBoundary(int blockid, Omark ort, point LL); // Get block boundary when it's placed at LL
    //vector<point> GetPlacedBlockPinRelBoundary(int blockid, int pinid, Omark ort); // Get block pin boundary when it's placed at origin
    //vector<point> GetPlacedBlockPinAbsBoundary(int blockid, int pinid, Omark ort, point LL); // Get block pin boundary when it's placed at LL
    
};

#endif
