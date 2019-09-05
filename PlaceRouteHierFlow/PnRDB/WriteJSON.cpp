#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <time.h>
#include <cassert>

using namespace nlohmann;

unsigned short
JSON_Presentation (int font, int vp, int hp) {
    if (font < 0 || font > 3) font = 0;
    if (vp < 0 || vp > 2) vp = 0;
    if (hp < 0 || hp > 2) hp = 0;
    return font * 16 + vp * 4 + hp;
}

unsigned short
JSON_STrans (bool reflect, bool abs_angle, bool abs_mag) {
    return 32768 * reflect + 2 * abs_mag + abs_angle;
}

json JSON_TimeTime () {
    static short int year, month;
    time_t* now = (time_t *) malloc( sizeof( time_t ) );
    time (now);
    struct tm *date;
    date = localtime (now);

    year   = 1900 + date->tm_year;   
    month  = 1 + date->tm_mon;
    json timeTime = {year, month, date->tm_mday, date->tm_hour, date->tm_min, date->tm_sec,
		     year, month, date->tm_mday, date->tm_hour, date->tm_min, date->tm_sec};
    free (now);
    return timeTime;
}



void
JSONExtractUit (string GDSData, double& unit)
{
    std::string jsonFileName = GDSData + ".json";
    //std::cout << "GDS JSON FILE=" << jsonFileName << std::endl;
    json jsonStrAry;
    ifstream jsonFile (jsonFileName);
    if (jsonFile.is_open()) {
	json jedb = json::parse (jsonFile);
	if (jedb["header"].is_number ()) {
	    json libAry = jedb["bgnlib"];
	    for (json::iterator lit = libAry.begin(); lit != libAry.end(); ++lit) {
		json lib = *lit;
		json strAry = lib["units"];
                if(strAry.is_array()) {
                     std::cout<<"Unit "<<strAry<<std::endl;
		     json::iterator xyI = strAry.begin();
                     double xyU=*xyI;
                     unit=2*0.00025/xyU;
                     return;
                }
            }
        }
    }
}

void
JSONReaderWrite_subcells (string GDSData, long int& rndnum,
			  vector<string>& strBlocks, vector<int>& llx, vector<int>& lly,
			  vector<int>& urx, vector<int>& ury, json& mjsonStrAry)
{
    rndnum++;

    std::string jsonFileName = GDSData + ".json";
    std::cout << "GDS JSON FILE=" << jsonFileName << std::endl;

    int TJ_llx=INT_MAX; int TJ_lly=INT_MAX; int TJ_urx=-1*INT_MAX; int TJ_ury=-1*INT_MAX;

    json jsonStrAry;
    ifstream jsonFile (jsonFileName);
    if (jsonFile.is_open()) {
	json jedb = json::parse (jsonFile);
	if (jedb["header"].is_number ()) {
	    json libAry = jedb["bgnlib"];
	    for (json::iterator lit = libAry.begin(); lit != libAry.end(); ++lit) {
		json lib = *lit;
		json strAry = lib["bgnstr"];
		for (json::iterator sit = strAry.begin(); sit != strAry.end(); ++sit) {
		    json str = *sit;
		    string nm = str["strname"];
		    string strname = nm + "_" + std::to_string(rndnum);
		    //json elements = str["elements"];
		    for (json::iterator elmI = str["elements"].begin(); elmI != str["elements"].end(); ++elmI) {
                        TJ_llx=INT_MAX; TJ_lly=INT_MAX; TJ_urx=INT_MIN; TJ_ury=INT_MIN;
			json elm = *elmI;
			if (elm["xy"].is_array()) {
			    json xyAry = elm["xy"];
			    int pos = 0;
			    for (json::iterator xyI = xyAry.begin(); xyI != xyAry.end(); ++xyI, pos++) {
				if (pos % 2) {
				    if (*xyI > TJ_ury) TJ_ury = *xyI;
				    if (*xyI < TJ_lly) TJ_lly = *xyI;
				} else {
				    if (*xyI > TJ_urx) TJ_urx = *xyI;
				    if (*xyI < TJ_llx) TJ_llx = *xyI;
				}
			    }
			} 
                        if (elm["sname"].is_string()) {
                          string sn=elm["sname"];
                          (*elmI)["sname"]=sn+ "_" + std::to_string(rndnum);
                        }
		    }
		    strBlocks.push_back(strname);
		    str["strname"] = strname;
		    mjsonStrAry.push_back (str);
		}
	    }
	} else
	    std::cout << "NOT a VALID JSON FILE: " << jsonFileName << std::endl;
    } else {
	std::cout << "NO JSON FILE: " << jsonFileName << std::endl;
	// DAK: This means we will have a missing subcell!
	// DAK: Should error here
    }
    llx.push_back(TJ_llx);
    lly.push_back(TJ_lly);
    urx.push_back(TJ_urx);
    ury.push_back(TJ_ury);
};


void
JSONLabelTerminals(PnRDB::hierNode& node, PnRDB::Drc_info& drc_info, json& elmAry, double unit)
{
    elmAry = json::array();
  
    cout<<"Top: "<<node.isTop<<endl;
    cout<<"#terminals print"<<endl;
    cout<<"#size: "<<node.Terminals.size()<<endl;
    for(unsigned int i=0;i<node.Terminals.size();i++){
	cout<<"#name: "<<node.Terminals[i].name<<endl; 
	cout<<"#type: "<<node.Terminals[i].type<<endl; 
	cout<<"#netIter: "<<node.Terminals[i].netIter<<endl; 
	cout<<"#termContact size: "<<node.Terminals[i].termContacts.size()<<endl;
	for(unsigned int j=0;j<node.Terminals[i].termContacts.size();j++){
	    cout<<"#contact-metal: "<<node.Terminals[i].termContacts[j].metal<<endl;
	    cout<<"#contact-placedCenter(x,y): "<<node.Terminals[i].termContacts[j].placedCenter.x<<" "
		<<node.Terminals[i].termContacts[j].placedCenter.y<<endl;
	}
    }
    int test_layer;//
    int test_font=1,test_vp=1,test_hp=1;
    int test_texttype=251;//pin purpose
    double test_mag=0.03; 
    int center_x[1],center_y[1];
    string tmpstring;
    
    if (node.isTop == 1) {
	for (unsigned int i = 0; i < node.Terminals.size(); i++) {
	    int write = 0;
	    for (unsigned int j = 0; j < node.Terminals[i].termContacts.size(); j++) {
		PnRDB::contact con = node.Terminals[i].termContacts[j];
           
		//if (con.metal.compare(NULL)==0){
		if (! con.metal.empty()) {
		    tmpstring = con.metal;
		    cout<<"#test metal string: "<<tmpstring<<endl;
		}
		if (write == 0) {
		    test_layer = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[con.metal]]);
		    center_x[0] = unit * con.placedCenter.x;
		    center_y[0] = unit * con.placedCenter.y;

		    json elm;
		    elm["type"] = "text";
		    elm["layer"] = test_layer;
		    elm["texttype"] = test_texttype;
		    elm["presentation"] = JSON_Presentation (test_font, test_vp, test_hp);

		    elm["strans"] = 0;
		    elm["mag"] = test_mag;
		    json xy = json::array();
		    xy.push_back (center_x[0]);
		    xy.push_back (center_y[0]);
		    elm["xy"] = xy;
		    elm["string"] = node.Terminals[i].name.c_str();
		    elmAry.push_back (elm);
	  
		    write = 1;
		}
	    }
	}
    }
}

void
assignBoxPoints (int* x, int*y, struct PnRDB::bbox b, double unit) {
    x[0] = unit * b.LL.x;
    x[1] = unit * b.LL.x;
    x[2] = unit * b.UR.x;
    x[3] = unit * b.UR.x;
    x[4] = x[0];
    y[0] = unit * b.LL.y;
    y[1] = unit * b.UR.y;
    y[2] = unit * b.UR.y;
    y[3] = unit * b.LL.y;
    y[4] = y[0];
}

void
addTextElements (json& jsonElements, int cenX, int cenY, int layer, const string& text) {
    int test_font=1,test_vp=1,test_hp=1;
    int test_texttype=251; //draw 0, label 2, pin 251, blockage 4
    double test_mag=0.03; 
    json element;
    element["type"] = "text";
    element["layer"] = layer;
    element["texttype"] = test_texttype;
    element["presentation"] = JSON_Presentation (test_font, test_vp, test_hp);

    element["strans"] = 0;
    element["mag"] = test_mag;
    json xy = json::array();
    xy.push_back (cenX);
    xy.push_back (cenY);
    element["xy"] = xy;
    element["string"] = text;
    jsonElements.push_back (element);
}

bool
addMetalBoundaries (json& jsonElements, struct PnRDB::Metal& metal, PnRDB::Drc_info& drc_info, double unit) {
    int x[5], y[5];
    assignBoxPoints (x, y, metal.MetalRect.placedBox, unit);

    if (metal.LinePoint[0].x != metal.LinePoint[1].x or
	metal.LinePoint[0].y != metal.LinePoint[1].y) {
	json bound0;
	bound0["type"] = "boundary";
	bound0["layer"] = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[metal.MetalRect.metal]]);
	bound0["datatype"] = 0;
	json xy = json::array();
	for (size_t i = 0; i < 5; i++) {
	    xy.push_back (x[i]);
	    xy.push_back (y[i]);
	}
	bound0["xy"] = xy;
	jsonElements.push_back (bound0);
	return true;
    }
    return false;
}

void
addContactBoundaries (json& jsonElements, struct PnRDB::contact& Contact, PnRDB::Drc_info& drc_info, int unit) {

    int x[5], y[5];
    assignBoxPoints (x, y, Contact.placedBox, unit);
    json bound0;
    bound0["type"] = "boundary";
    bound0["layer"] = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[Contact.metal]]);
    bound0["datatype"] = 0;
    json xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	 xy.push_back (x[i]);
	 xy.push_back (y[i]);
       }
    bound0["xy"] = xy; 
    jsonElements.push_back (bound0);
}


void
addOABoundaries (json& jsonElements, int width, int height) {
  int x[5],y[5];
  x[0]=y[0]=x[1]=y[3]=x[4]=y[4]=0; x[2]=x[3]=width; y[1]=y[2]=height;
  json bound1;
  bound1["type"] = "boundary";
  bound1["layer"]=235;
  bound1["datatype"]=5;
  json xy = json::array();
  for (size_t i = 0; i < 5; i++) {
      xy.push_back (x[i]);
      xy.push_back (y[i]);
  }
  bound1["xy"] = xy;
  bound1["propattr"]=126;
  bound1["propvalue"]="oaBoundary:pr";
  jsonElements.push_back (bound1);
//   boundary
//       layer 235
//       datatype 5
//       xy   5   0 0   0 1608   8640 1608   8640 0
//                0 0
//       propattr 126
//       propvalue "oaBoundary:pr"
//       endel

}


void addViaBoundaries (json& jsonElements, struct PnRDB::Via& via, PnRDB::Drc_info& drc_info, double unit) {
    int x[5], y[5];
    assignBoxPoints (x, y, via.ViaRect.placedBox, unit);
    
    json bound0;
    bound0["type"] = "boundary";
    bound0["layer"] = stoi(drc_info.MaskID_Via[drc_info.Viamap[via.ViaRect.metal]]);
    bound0["datatype"] = 0;
    json xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	xy.push_back (x[i]);
	xy.push_back (y[i]);
    }
    bound0["xy"] = xy;
    jsonElements.push_back (bound0);

    //LowerMetalRect
    assignBoxPoints (x, y, via.LowerMetalRect.placedBox, unit);
     
    json bound1;
    bound1["type"] = "boundary";
    bound1["layer"] = stoi(drc_info.MaskID_Metal[drc_info.Metalmap[via.LowerMetalRect.metal]]);
    bound1["datatype"] = 0;
    xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	xy.push_back (x[i]);
	xy.push_back (y[i]);
    }
    bound1["xy"] = xy;
    jsonElements.push_back (bound1);

    //UpperMetalRect
    assignBoxPoints (x, y, via.UpperMetalRect.placedBox, unit);
     
    json bound2;
    bound2["type"] = "boundary";
    bound2["layer"] =
	stoi(drc_info.MaskID_Metal[drc_info.Metalmap[via.UpperMetalRect.metal]]);
    bound2["datatype"] = 0;
    xy = json::array();
    for (size_t i = 0; i < 5; i++) {
	xy.push_back (x[i]);
	xy.push_back (y[i]);
    }
    bound2["xy"] = xy;
    jsonElements.push_back (bound2);
}

std::string
PnRdatabase::WriteJSON (PnRDB::hierNode& node, bool includeBlock, bool includeNet, bool includePowerNet,
			bool includePowerGrid, std::string gdsName, PnRDB::Drc_info& drc_info, string opath) {
    std::cout << "JSON WRITE CELL " << gdsName << std::endl;
    node.gdsFile = opath+gdsName+".gds";
    string TopCellName = gdsName;
    std::set<string> uniGDSset;
    double unitScale=2;
	for (unsigned int i = 0; i < node.Blocks.size(); i++) 
	    uniGDSset.insert(node.Blocks[i].instance.at( node.Blocks[i].selectedInstance ).gdsFile);

	for (std::set<string>::iterator it=uniGDSset.begin();it!=uniGDSset.end();++it) {
	    JSONExtractUit (*it, unitScale);
	}   
    std::cout<<"unitScale "<<unitScale<<std::endl;
    uniGDSset.clear();
  
    std::ofstream jsonStream;
    jsonStream.open (node.gdsFile + ".json");
    json jsonTop;
    json jsonLibAry = json::array();
    jsonTop["header"] = 600;
    json jsonLib;
    jsonLib["time"] = JSON_TimeTime ();
    double dbUnitUser=2*0.00025/unitScale;
    double dbUnitMeter=dbUnitUser/1e6;
    jsonLib["units"] = {dbUnitUser, dbUnitMeter};
    //jsonLib["units"] = {0.00025, 2.5e-10};
    jsonLib["libname"] = "test";
    json jsonStrAry = json::array();

    vector<string> strBlocks;
    std::map<string, int> gdsMap2strBlock;
    vector<string> strBlocks_Top;
    vector<int> llx, lly, urx, ury;
    long int rndnum = static_cast<long int>(time(NULL));

    int idx = 0;
    if (includeBlock) {
	for (unsigned int i = 0; i < node.Blocks.size(); i++) 
	    uniGDSset.insert(node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile);

	cout<<"start wrting sub-blocks"<<endl;
	for (std::set<string>::iterator it=uniGDSset.begin();it!=uniGDSset.end();++it) {
	    json j;
	    JSONReaderWrite_subcells (*it, rndnum, strBlocks, llx,lly,urx,ury, j);
	    for (json::iterator str = j.begin(); str != j.end(); ++str)
		jsonStrAry.push_back (*str);
	    strBlocks_Top.push_back(strBlocks.back());
	    gdsMap2strBlock.insert( std::make_pair(*it, idx) );
	    idx++;
	}   
    }

    json jsonStr;
    jsonStr["time"] = JSON_TimeTime();
    // DAK: Hack to match time for repeated runs
    jsonStr["time"] = {2019, 4, 24, 9, 46, 15, 2019, 4, 24, 9, 46, 15};
    jsonStr["strname"] = TopCellName.c_str();
    json jsonElements = json::array();

    int x[5], y[5];
    int write_blockPins_name = 0;
    if (write_blockPins_name){
	for (unsigned int i = 0; i < node.blockPins.size(); i++) {
	    int write = 0;
	    for (unsigned int j = 0; j < node.blockPins[i].pinContacts.size(); j++) {
		PnRDB::contact con = node.blockPins[i].pinContacts[j];
		assignBoxPoints (x, y, con.placedBox, unitScale);
		if (write == 0) {
		    addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2,
				     stoi(drc_info.MaskID_Metal[drc_info.Metalmap[con.metal]]),
				     node.blockPins[i].name);
		    write = 1;	// added by yg 
		}
	    }
	}
    }

    if (includeNet) {
	//cout<<"start writing nets"<<endl;
	for (unsigned int i = 0; i < node.Nets.size(); i++) {
	    //path_metal
	    int write = 1;
	    for (unsigned int j = 0; j < node.Nets[i].path_metal.size(); j++) {
		PnRDB::Metal metal = node.Nets[i].path_metal[j];
		if (addMetalBoundaries (jsonElements, metal, drc_info, unitScale)) {
		    if (write == 0) {
			assignBoxPoints (x, y, metal.MetalRect.placedBox, unitScale);
			addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2,
					 stoi(drc_info.MaskID_Metal[drc_info.Metalmap[metal.MetalRect.metal]]),
					 node.Nets[i].name);
			write = 1; // added by yg 
		    }
		}
	    }
	    //path_via
	    for (unsigned int j = 0; j < node.Nets[i].path_via.size(); j++) 
		addViaBoundaries(jsonElements, node.Nets[i].path_via[j], drc_info, unitScale);
	}
    }
    json j;
    JSONLabelTerminals(node, drc_info, j, unitScale);
    for (json::iterator elm = j.begin(); elm != j.end(); ++elm) jsonElements.push_back (*elm);

    if (includePowerNet) {
	for (unsigned int i = 0; i < node.PowerNets.size(); i++) {
	    //path_metal
	    int write = 0;
	    for (unsigned int j = 0; j < node.PowerNets[i].path_metal.size(); j++) {
		PnRDB::Metal metal = node.PowerNets[i].path_metal[j];
		if (addMetalBoundaries (jsonElements,  metal, drc_info, unitScale)) {
		    if (write == 0) {
			assignBoxPoints (x, y, metal.MetalRect.placedBox, unitScale);
			addTextElements (jsonElements, (x[0]+x[2])/2, (y[0]+y[2])/2,
					 stoi(drc_info.MaskID_Metal[drc_info.Metalmap[metal.MetalRect.metal]]),
					 node.PowerNets[i].name);
			write = 1; //added by yg 
		    }
		}
	    }
	    //path_via
	    for (unsigned int j = 0; j < node.PowerNets[i].path_via.size(); j++) 
		addViaBoundaries(jsonElements, node.PowerNets[i].path_via[j], drc_info, unitScale);
	}
    }

    if (includePowerGrid) {
	int vdd = 1; int gnd = 1;
	if (vdd == 1) {
	    for (unsigned int i = 0; i < node.Vdd.metals.size(); i++) 
		addMetalBoundaries (jsonElements, node.Vdd.metals[i], drc_info, unitScale);

	    for (unsigned int i = 0; i < node.Vdd.vias.size(); i++) 
		addViaBoundaries(jsonElements, node.Vdd.vias[i], drc_info, unitScale);
	}
	if (gnd == 1) {
	    for (unsigned int i = 0; i < node.Gnd.metals.size(); i++) 
		addMetalBoundaries (jsonElements, node.Gnd.metals[i], drc_info, unitScale);

	    for (unsigned int i = 0; i < node.Gnd.vias.size(); i++) 
		addViaBoundaries(jsonElements, node.Gnd.vias[i], drc_info, unitScale);
	}
    }

    if (includeBlock) {
	int bOrient;
   
        //for(int i = 0;i < node.Blocks.size(); i++){
        //    //int index=gdsMap2strBlock[node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile];
        //    for( int j=0;j<node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).interMetals.size();j++){
        //         addContactBoundaries(jsonElements, node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).interMetals[j], drc_info, unitScale);
        //       }
        //   }

	for (unsigned int i = 0; i < node.Blocks.size(); i++) {
	    int index=gdsMap2strBlock[node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).gdsFile];

	    json sref;
	    sref["type"] = "sref";
	    sref["sname"] = strBlocks_Top[index].c_str();

	    switch (node.Blocks[i].instance.at(node.Blocks[i].selectedInstance).orient) {
	    case PnRDB::N:   bOrient = 0; break;
	    case PnRDB::S:   bOrient = 1; break;
	    case PnRDB::E:   bOrient = 2; break;
	    case PnRDB::W:   bOrient = 3; break;
	    case PnRDB::FN:  bOrient = 4; break;
	    case PnRDB::FS:  bOrient = 5; break;
	    case PnRDB::FE:  bOrient = 6; break;
	    case PnRDB::FW:  bOrient = 7; break;
	    default: bOrient = 8;
	    }

	    PnRDB::bbox box = node.Blocks[i].instance.at(node.Blocks[i].selectedInstance ).placedBox;
	    switch (bOrient) {
	    case 0:
		sref["strans"] = 0;
		sref["angle"] = 0.0;
		x[0] = unitScale * box.LL.x;
		y[0] = unitScale * box.LL.y;
		break;
	    case 1:
		sref["strans"] = 0;
		sref["angle"] = 180.0;
		x[0] = unitScale * box.UR.x+llx[index];
		y[0] = unitScale * box.UR.y+lly[index];
		break;
	    case 2:
	      assert(0);
		break;
	    case 3:
	      assert(0);
		break;
	    case 4:
		sref["strans"] = 32768; // DAK: HACK
		sref["angle"] = 180.0;
		x[0] = unitScale * box.UR.x+llx[index];
		y[0] = unitScale * box.LL.y-lly[index];
		break;
	    case 5:
		sref["strans"] = 32768; // DAK: HACK
		sref["angle"] = 0.0;
		x[0] = unitScale * box.LL.x-llx[index];
		y[0] = unitScale * box.UR.y+lly[index];
		break;
	    case 6:
	      assert(0);
		break;
	    case 7:
	      assert(0);
		break;
	    default:
		sref["strans"] = 0; // DAK: HACK
		sref["angle"] = 0.0;
		x[0] = unitScale * box.LL.x;
		y[0] = unitScale * box.LL.y;
	    }
	    json xy = json::array();
	    for (size_t i = 0; i < 1; i++) {
		xy.push_back (x[i]);
		xy.push_back (y[i]);
	    }
	    sref["xy"] = xy;
	    jsonElements.push_back (sref);
	}
    }

    addOABoundaries (jsonElements, unitScale * node.width, unitScale * node.height);
    jsonStr["elements"] = jsonElements;
    jsonStrAry.push_back (jsonStr);
    jsonLib["bgnstr"] = jsonStrAry;
  
    jsonLibAry.push_back(jsonLib);
    jsonTop["bgnlib"] = jsonLibAry;
    jsonStream << std::setw(4) << jsonTop;
    jsonStream.close();
    std::cout << " JSON FINALIZE " <<  gdsName << std::endl;
    return node.gdsFile;
}
