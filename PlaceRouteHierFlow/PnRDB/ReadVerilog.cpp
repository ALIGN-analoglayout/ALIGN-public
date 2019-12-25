#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>


bool PnRdatabase::ReadVerilog(const string& fpath, const string& vname, const string& topcell) {
  string verilogfile=fpath+"/"+vname;
  cout<<"PnRDB-Info: reading Verilog file "<<verilogfile<<endl;

  ifstream fin;
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(verilogfile.c_str());
  } catch(ifstream::failure& e) {
      cerr<<"PnRDB-Error: failed to open Verilog file "<<verilogfile<<endl;
      return false;
  }

  try {
      ReadVerilogHelper rvh(*this);
      rvh( fin, fpath, topcell);
  } catch(ifstream::failure e) {
      fin.close();
      cerr<<"PnRDB-Error: fail to read Verilog file "<<endl;
      return false;
  }

  try {
      fin.close();
  } catch(ifstream::failure e) {
      cerr<<"PnRDB-Error: fail to close Verilog file "<<endl;
      return false;
  }

  return true;

}

void ReadVerilogHelper::semantic( const string& fpath, const string& topcell)
{

    for(unsigned int i=0;i<db.hierTree.size();i++){

	auto &curr_node = db.hierTree[i];

	{
	    if(db.DRC_info.Metal_info.size() < 2) {std::cout<<"PnRDB-Error: too few metal layers\n";}
	    if(db.DRC_info.Metal_info[0].direct==1) { //horizontal
		curr_node.bias_Vgraph=db.DRC_info.Metal_info[0].grid_unit_y;
	    } else {
		curr_node.bias_Hgraph=db.DRC_info.Metal_info[0].grid_unit_x;
	    }
	    if(db.DRC_info.Metal_info[1].direct==1) { //horizontal
		curr_node.bias_Vgraph=db.DRC_info.Metal_info[1].grid_unit_y;
	    } else {
		curr_node.bias_Hgraph=db.DRC_info.Metal_info[1].grid_unit_x;
	    }
	    //added one nodes to the class
	    if(!db.ReadConstraint(curr_node, fpath, "const")) {cerr<<"PnRDB-Error: fail to read constraint file of module "<<curr_node.name<<endl;}
	    else{std::cout<<"Finished reading contraint file"<<std::endl;}
	}
    }


    //update hier tree here for the class Nodes.
    //inistial 
    for(unsigned int i=0;i<db.hierTree.size();i++){
        for(unsigned int j=0;j<db.hierTree[i].Blocks.size();j++){
            db.hierTree[i].Blocks[j].child = -1;
	}
    }
		
    //update hier tree here for the class Nodes.
    for(unsigned int i=0;i<db.hierTree.size();i++){
        for(unsigned int j=0;j<db.hierTree.size();j++){
            for(unsigned int k=0;k<db.hierTree[j].Blocks.size();k++)
                if(db.hierTree[j].Blocks[k].instance.back().master.compare(db.hierTree[i].name)==0){
                   db.hierTree[j].Blocks[k].child = i;
                   int parent_found = 0;
                   for(unsigned int p=0;p<db.hierTree[i].parent.size();p++){
		     if(db.hierTree[i].parent[p] == (int)j){parent_found=1;} 
		   }
                   if(parent_found==0){db.hierTree[i].parent.push_back(j);}                   
                  }
            }
        if(db.hierTree[i].name.compare(topcell)==0){
           db.topidx =i;
           db.hierTree[i].isTop = 1;
          }
                //update terminal information
        for(unsigned int l=0;l<db.hierTree[i].Nets.size();l++){
            for(unsigned int m=0;m<db.hierTree[i].Terminals.size();m++){
                if(db.hierTree[i].Nets[l].name.compare(db.hierTree[i].Terminals[m].name)==0){
                   db.hierTree[i].Nets[l].degree++;
		   {
		       PnRDB::connectNode temp_connectNode;
		       temp_connectNode.type = PnRDB::Terminal;
		       temp_connectNode.iter = m;
		       temp_connectNode.iter2 = -1;
		       db.hierTree[i].Nets[l].connected.push_back(temp_connectNode);
		   }
                   db.hierTree[i].Nets[l].sink2Terminal = 1;
                   db.hierTree[i].Terminals[m].netIter = l;
                   }
                }
            }
      }
		
    for(unsigned int i=0;i<db.hierTree.size();i++){
        for(unsigned int j=0;j<db.hierTree[i].Blocks.size();j++){
            if(db.hierTree[i].Blocks[j].child==-1){
               db.hierTree[i].Blocks[j].instance.back().isLeaf=1;
               }
        else{
             db.hierTree[i].Blocks[j].instance.back().isLeaf=0;
             }
           }
       }

  std::cout<<"Middle\n";
    //mergeLEFandGDS
    for(unsigned int i=0;i<db.hierTree.size();i++){
    //cout<<"db.hierTree node "<<i<<endl;
    if(!db.MergeLEFMapData(db.hierTree[i])){cerr<<"PnRDB-Error: fail to mergeLEFMapData of module "<<db.hierTree[i].name<<endl;
      }else{
      std::cout<<"Finished merge lef data"<<std::endl;
      }
      }
  // wbxu: following lines need modifications to reflect changes of block instance vector
  //update powernets information
  std::cout<<"Middle\n";
  for(unsigned int i=0;i<Supply_node.Blocks.size();i++){
      std::string supply_name_full = Supply_node.name+"."+Supply_node.Blocks[i].instance.back().name;
      std::string supply_name = Supply_node.Blocks[i].instance.back().name;
      int power;
      if(Supply_node.Blocks[i].instance.back().master == "supply0"){
         power = 0;
        }else{
         power =1;
        }
      for(unsigned int j=0;j<db.hierTree.size();j++){
           std::vector<PnRDB::net> temp_net;
           for(unsigned int k=0;k<db.hierTree[j].Nets.size();k++){
               if(db.hierTree[j].Nets[k].name == supply_name_full or db.hierTree[j].Nets[k].name == supply_name){
                   PnRDB::PowerNet temp_PowerNet;
                   temp_PowerNet.name = db.hierTree[j].Nets[k].name;
                   temp_PowerNet.power = power;
                   temp_PowerNet.connected = db.hierTree[j].Nets[k].connected;
                   db.hierTree[j].PowerNets.push_back(temp_PowerNet);
                 }else{
                   temp_net.push_back(db.hierTree[j].Nets[k]);
                 }
              }
            db.hierTree[j].Nets = temp_net;
         }
     }
 
  //update pins & terminal connection iternet
  for(unsigned int i=0;i<db.hierTree.size();i++){
      for(unsigned int j=0;j<db.hierTree[i].Nets.size();j++){
           for(unsigned int k=0;k<db.hierTree[i].Nets[j].connected.size();k++){
                if(db.hierTree[i].Nets[j].connected[k].type == PnRDB::Block){
                        for(unsigned int m=0;m<db.hierTree[i].Blocks[db.hierTree[i].Nets[j].connected[k].iter2].instance.size();++m) {
                            db.hierTree[i].Blocks[db.hierTree[i].Nets[j].connected[k].iter2].instance.at(m).blockPins[db.hierTree[i].Nets[j].connected[k].iter].netIter = j;
                        } // [RA] need confirmation -wbxu
                  }else{
db.hierTree[i].Terminals[db.hierTree[i].Nets[j].connected[k].iter].netIter = j;
                  }
              }
         }
       
      for(unsigned int j=0;j<db.hierTree[i].PowerNets.size();j++){

           for(unsigned int k=0;k<db.hierTree[i].PowerNets[j].connected.size();k++){
                if(db.hierTree[i].PowerNets[j].connected[k].type == PnRDB::Block){
                    for(unsigned int m=0;m<db.hierTree[i].Blocks[db.hierTree[i].PowerNets[j].connected[k].iter2].instance.size();++m) {
                    db.hierTree[i].Blocks[db.hierTree[i].PowerNets[j].connected[k].iter2].instance.at(m).blockPins[db.hierTree[i].PowerNets[j].connected[k].iter].netIter = -1; 
                    }  // [RA] need confirmation - wbxu
                    db.hierTree[i].PowerNets[j].Pins.push_back(db.hierTree[i].Blocks[db.hierTree[i].PowerNets[j].connected[k].iter2].instance.back().blockPins[db.hierTree[i].PowerNets[j].connected[k].iter]); // [AR] need modification -wbxu
                  }else{
                    db.hierTree[i].Terminals[db.hierTree[i].PowerNets[j].connected[k].iter].netIter = -1;
                    PnRDB::pin temp_pin;
                    temp_pin.name = db.hierTree[i].Terminals[db.hierTree[i].PowerNets[j].connected[k].iter].name;
                    temp_pin.netIter = -1;
                    temp_pin.pinContacts = db.hierTree[i].Terminals[db.hierTree[i].PowerNets[j].connected[k].iter].termContacts;
                    db.hierTree[i].PowerNets[j].Pins.push_back(temp_pin);
                  }
              }

      }
  }
}

void ReadVerilogHelper::gen_terminal_map( unordered_map<string,int>& terminal_map)
{
    terminal_map.clear();
    for(unsigned int j=0;j<temp_node.Terminals.size();j++){
	terminal_map[temp_node.Terminals[j].name] = j;
    }
}

int ReadVerilogHelper::process_connection( int iter, const string& net_name,
					   unordered_map<string,int>& net_map)
{
    int net_index=0;

    unordered_map<string,int>::iterator ptr = net_map.find( net_name);

    if ( ptr != net_map.end()) {
	net_index = ptr->second;
    } else {
	net_index = temp_node.Nets.size();
	temp_node.Nets.emplace_back();

	PnRDB::net& b = temp_node.Nets.back();
	b.name = net_name;
	b.degree = 0;

	net_map[net_name] = net_index;
    }

    //    temp_node.Nets[net_index].degree++;
    temp_node.Nets[net_index].connected.emplace_back();

    temp_node.Nets[net_index].degree =
	temp_node.Nets[net_index].connected.size();

    PnRDB::connectNode& b = temp_node.Nets[net_index].connected.back();
    b.type = PnRDB::Block;
    b.iter = iter;
    b.iter2 = temp_node.Blocks.size();

    return net_index;
}


void ReadVerilogHelper::parse_module( Lexer &l, bool celldefine_mode)
{
  unordered_map<string,int> terminal_map; // terminal_name to terminal_index
  unordered_map<string,int> net_map; // net_name to net_index

  l.mustbe( TokenType::NAME);
  if ( !celldefine_mode) {
      temp_node.name = l.last_token.value;
      temp_node.isCompleted = 0;
  } else {
      Supply_node.name = l.last_token.value;
      Supply_node.isCompleted = 0;
  }

  if ( l.have( TokenType::LPAREN)) {
      if ( !l.have( TokenType::RPAREN)) {
	  do {
	      l.mustbe( TokenType::NAME);
	      PnRDB::terminal temp_terminal;
	      temp_terminal.name = l.last_token.value;
	      temp_node.Terminals.push_back( temp_terminal);
	  } while ( l.have( static_cast<TokenType>( ',')));
	  l.mustbe( TokenType::RPAREN);  
      }
  }
  l.mustbe( TokenType::SEMICOLON);  

  gen_terminal_map( terminal_map);

  while (1) {

      if ( l.have_keyword( "input") ||
	   l.have_keyword( "output") ||
	   l.have_keyword( "inout")) {
	  string direction_tag = l.last_token.value;
	  if ( !l.have( TokenType::SEMICOLON)) {
	      do {
		  l.mustbe( TokenType::NAME);
		  string temp_name = l.last_token.value;
		  auto ptr = terminal_map.find( temp_name);
		  if (  ptr != terminal_map.end()) {
		      temp_node.Terminals[ptr->second].type = direction_tag;
		  }
	      } while ( l.have( static_cast<TokenType>( ',')));
	      l.mustbe( TokenType::SEMICOLON);  
	  }
      } else if ( l.have_keyword( "supply0") ||
		  l.have_keyword( "supply1")) {

	  string direction_tag = l.last_token.value;
	  if ( !l.have( TokenType::SEMICOLON)) {
	      do {
		  if ( l.have( TokenType::NUMBER)) {
		  } else {
		      l.mustbe( TokenType::NAME);
		  }
		  string temp_name = l.last_token.value;
		  PnRDB::blockComplex temp_blockComplex;
		  temp_blockComplex.instance.resize(1);
		  temp_blockComplex.instance.back().master = direction_tag;
		  temp_blockComplex.instance.back().name = temp_name;
		  Supply_node.Blocks.push_back(temp_blockComplex);
	      } while ( l.have( static_cast<TokenType>( ',')));
	      l.mustbe( TokenType::SEMICOLON);  
	  }
      } else if ( l.have_keyword( "specify")) {
	  while ( !l.have( TokenType::EndOfFile) &&
		  !l.have_keyword( "endspecify")) {
	      l.get_token();
	  }
      } else {
	  break;
      }
  }

  while ( !l.have_keyword( "endmodule")) {

    PnRDB::blockComplex temp_blockComplex;
    temp_blockComplex.instance.resize(1); // Need to add one instance; should be in the constructor of blockComplex

    auto& current_instance = temp_blockComplex.instance.back();

    l.mustbe( TokenType::NAME);
    current_instance.master = l.last_token.value;

    l.mustbe( TokenType::NAME);
    current_instance.name = l.last_token.value;

    l.mustbe( TokenType::LPAREN);
    if ( !l.have( TokenType::RPAREN)) {
      int i = 0;
      do {
        PnRDB::pin temp_pin;
	l.mustbe( TokenType::PERIOD);
	l.mustbe( TokenType::NAME);
	temp_pin.name = l.last_token.value;
	l.mustbe( TokenType::LPAREN);
	l.mustbe( TokenType::NAME);
	string net_name = l.last_token.value;
	l.mustbe( TokenType::RPAREN);

	temp_pin.netIter = process_connection( i, net_name, net_map);
	current_instance.blockPins.push_back(temp_pin);
	
	++i;
      } while ( l.have( TokenType::COMMA));
      l.mustbe( TokenType::RPAREN);
    }
    l.mustbe( TokenType::SEMICOLON);

    temp_node.Blocks.push_back( temp_blockComplex);

  }

  if ( !celldefine_mode) {
      db.hierTree.push_back(temp_node);
  }
  temp_node = clear_node;

}

void ReadVerilogHelper::parse_top( istream& fin)
{

  Lexer l(fin,1);

  while( !l.have( TokenType::EndOfFile)) {
      if ( l.have_keyword( "module")) {
	  parse_module( l);
      } else if ( l.have( TokenType::BACKQUOTE)) {
	  if ( l.have_keyword("celldefine")) {
	      l.mustbe_keyword( "module");
	      parse_module( l, true);
	      l.mustbe( TokenType::BACKQUOTE);
	      l.mustbe_keyword( "endcelldefine");
	  } else {
	      l.mustbe_keyword( "celldefine");
	  }
      } else if ( l.have_keyword( "specify")) {
	  while ( !l.have( TokenType::EndOfFile) &&
		  !l.have_keyword( "endspecify")) {
	      l.get_token();
	  }
      } else {
	  l.mustbe_keyword( "module");
      }
  }

}


void ReadVerilogHelper::operator()(istream& fin, const string& fpath, const string& topcell)
{
    // Swap in the new parser
    parse_top( fin);
    semantic( fpath, topcell);
    std::cout<<"End of reading verilog\n";
}

bool PnRdatabase::MergeLEFMapData(PnRDB::hierNode& node){
  bool missing_lef_file = 0;

  std::cout<<"PnRdatabase-Info:: merge LEF/map data\n";
  for(unsigned int i=0;i<node.Blocks.size();i++){
    string master=node.Blocks[i].instance.back().master;
    if(lefData.find(master)==lefData.end()) {
	// LEF is missing; Ok if a cap or if not a leaf
	if(master.find("Cap")!=std::string::npos or
	   master.find("cap")!=std::string::npos) continue;
	if(node.Blocks[i].instance.back().isLeaf) {
	    cerr<<"PnRDB-Error: the key does not exist in map:"<<" "<<master<<endl;
	    missing_lef_file = 1;
	}
	continue;
    }
    
    //cout<<node.Blocks[i].instance.back().name<<" "<<master<<endl;
    for(unsigned int w=0;w<lefData[master].size();++w) {
      if(node.Blocks[i].instNum>0) { node.Blocks[i].instance.push_back( node.Blocks[i].instance.back() ); }
      node.Blocks[i].instNum++;
      node.Blocks[i].instance.back().width=lefData[master].at(w).width;
      node.Blocks[i].instance.back().height=lefData[master].at(w).height;
      node.Blocks[i].instance.back().lefmaster=lefData[master].at(w).name;
      node.Blocks[i].instance.back().originBox.LL.x=0;
      node.Blocks[i].instance.back().originBox.LL.y=0;
      node.Blocks[i].instance.back().originBox.UR.x=lefData[master].at(w).width;
      node.Blocks[i].instance.back().originBox.UR.y=lefData[master].at(w).height;
      node.Blocks[i].instance.back().originCenter.x=lefData[master].at(w).width/2;
      node.Blocks[i].instance.back().originCenter.y=lefData[master].at(w).height/2;

      for(unsigned int j=0;j<lefData[master].at(w).macroPins.size();j++){
        bool found = 0;
        for(unsigned int k=0;k<node.Blocks[i].instance.back().blockPins.size();k++){
          if(lefData[master].at(w).macroPins[j].name.compare(node.Blocks[i].instance.back().blockPins[k].name)==0){
            node.Blocks[i].instance.back().blockPins[k].type = lefData[master].at(w).macroPins[j].type;
            node.Blocks[i].instance.back().blockPins[k].pinContacts = lefData[master].at(w).macroPins[j].pinContacts;
            node.Blocks[i].instance.back().blockPins[k].use = lefData[master].at(w).macroPins[j].use;
            found = 1;
            }
        }
        if(found == 0){
          node.Blocks[i].instance.back().blockPins.push_back(lefData[master].at(w).macroPins[j]);
        }
      }

      node.Blocks[i].instance.back().interMetals = lefData[master].at(w).interMetals;
      node.Blocks[i].instance.back().gdsFile=gdsData[lefData[master].at(w).name];
  //cout<<"xxx "<<node.Blocks[i].instance.back().gdsFile<<endl;
    }


  }

  assert( !missing_lef_file);

  return 1;
  
}
