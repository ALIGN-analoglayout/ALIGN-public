#ifndef CAPPLACER_h_
#define CAPPLACER_h_


#include <vector>
#include <algorithm>
#include <map>
#include <set>
#include <cmath>
#include <limits.h>
#include <bitset>
#include <cstdlib>
#include <iterator>
#include <cctype>
#include <utility>
#include <string>
#include <stdlib.h>
#include <math.h>
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <sstream>
//#include "Capdatatype.h"
#include "../PnRDB/datatype.h"

//#include "/home/grads/l/liyg/Research/hierFlow_dev_Prometheus_010319/router/grid.h"
extern "C"
{
#include <stdio.h>
}

//using std::string;
//using std::cout;
//using std::endl;

using std::vector;
using std::string;
using std::iostream;
using std::pair;
using std::make_pair;
using std::ofstream;
using std::endl;
using std::cout;
using std::cerr;

//using PnRDB::hierNode;



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
struct point {
  int x=0;
  int y=0;
}; // structure of integer coordinate

struct bbox {
	vector<point> polygon; // list of coordinates of polygon
	point LL,LR,UL,UR;
};

struct contact {
	string metal="";
	bbox originBox;
	bbox placedBox;
	point originCenter;
	point placedCenter;
};

struct terminal {
  string name="";
  string type=""; //add by yg //////////////////////////////////////
  int netIter=-1;
  vector<contact> termContacts;
};



class Pin{
    public:
        string pinName;
        vector <contact> pinContacts;
		int netIter;
};

class Placer_Router_Cap
{
  private:
    
    PnRDB::block CheckOutBlock;
    int offset_x;
    int offset_y;
    struct cap{
      double index_x;
      double index_y;
      double x;
      double y;
      int net_index;
      int access;
      //int line_accessed;
    };

    vector<int> metal_width;
    vector<int> metal_distance_ss;
    vector<int> via_width;
    vector<int> via_cover;
    int shifting;
    int min_dis;
    vector<cap> Caps;
    pair<int,int> unit_cap_demension;
    pair<int,int> span_distance;
    vector<pair<int,int> > cap_pair_sequence;
    vector<pair<int,int> > net_sequence;
    vector<int> num_router_net_v;
    vector<int> num_router_net_h;
    struct connection_set{
      vector<int> cap_index;
    };
    struct net{
      string name="";
      vector<int> cap_index;
      vector<pair<double,double> > start_conection_coord;
      vector<pair<double,double> > end_conection_coord;
      vector<int> Is_pin; //0 not pin, 1 pin
      vector<string> metal;
      vector<pair<double,double> > via;
      vector<string> via_metal;
      vector<connection_set> Set;
      vector<connection_set> router_line_v;
      vector<connection_set> router_line_h;
      vector<connection_set> half_router_line_v;
      vector<connection_set> half_router_line_h;
      vector<int> routable_line_v;
      vector<int> routable_line_h;
      vector<int> line_v;
      //vector<int> line_v_r;
      vector<int> line_h;
      //vector<int> line_h_r;
    };
    vector<net> Nets_pos;
    vector<net> Nets_neg;

  public:
    Placer_Router_Cap();
    Placer_Router_Cap(vector<int> & ki, vector<pair<string, string> > &cap_pin, string fpath, string unit_capacitor, string final_gds);
    Placer_Router_Cap(string fpath, PnRDB::hierNode & current_node);
    void initial_net_pair_sequence(vector<int> & ki, vector<pair<string, string> > &cap_pin);
    void perturbation_pair_sequence();
    void Placer_Cap(vector<int> & ki);
    void Router_Cap(vector<int> & ki, vector<pair<string, string> > &cap_pin);
    void PrintPlacer_Router_Cap(string outfile);
    void GetPhsicalInfo_router();
    void cal_offset();
    void fillPathBoundingBox (int *x, int* y,
			      pair<double,double> &start,
			      pair<double,double> &end,
			      double width);
    void ExtractData (string fpath, string unit_capacitor, string final_gds);
    //    void WriteGDS(string fpath, string unit_capacitor, string final_gds);
    void WriteJSON (string fpath, string unit_capacitor, string final_gds);
    PnRDB::block CheckoutData(void){return CheckOutBlock;};
    //    void GDSReaderWriterTxTFile_extension(string GDSData, GdsParser::GdsWriter& gw, int& rndnum, vector<string>& strBlocks, vector<int>& llx, vector<int>& lly, vector<int>& urx, vector<int>& ury);
    int found_neighbor(int j, net& pos, connection_set& temp_set);
    void Common_centroid_capacitor(string fpath, PnRDB::hierNode& current_node);
};

#endif
