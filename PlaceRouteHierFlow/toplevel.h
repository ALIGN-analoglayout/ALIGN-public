#ifndef __TOPLEVEL_H
#define __TOPLEVEL_H
#include <vector>
#include <string>
#include "PnRDB/PnRdatabase.h"
int toplevel( const std::vector<std::string>& argv );
/*
void save_state( const PnRdatabase& DB, const PnRDB::hierNode& current_node, int lidx,
		 const string& opath, const string& tag, const string& ltag, bool skip);
void route_single_variant( PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::hierNode& current_node, int lidx, const string& opath, const string& binary_directory, bool skip_saving_state, bool adr_mode);
void route_top_down(PnRdatabase& DB, const PnRDB::Drc_info& drcInfo, PnRDB::bbox bounding_box, PnRDB::Omark current_node_ort,
                           int idx, int& new_currentnode_idx, int lidx, const string& opath, const string& binary_directory,
		    bool skip_saving_state, bool adr_mode);
*/
#endif
