#include "PnRdatabase.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <cassert>

bool PnRdatabase::ReadVerilog(const string& fpath, const string& vname, const string& topcell) {

  auto logger = spdlog::default_logger()->clone("PnRDB.PnRdatabase.ReadVerilog");

  ReadVerilogHelper rvh(*this);

  string verilogfile=fpath+"/"+vname;
  logger->info("Reading Verilog file {0}",verilogfile);

  ifstream fin;
  fin.exceptions(ifstream::failbit | ifstream::badbit);
  try {
    fin.open(verilogfile.c_str());
  } catch(ifstream::failure& e) {
      logger->error("Failed to open Verilog file {0}",verilogfile);
      return false;
  }

  rvh.parse_top( fin);

  fin.close();

  attach_constraint_files( fpath);
  semantic0( topcell);
  semantic1( rvh.get_global_signals());
  semantic2();

  return true;

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

  string global_module_name;

  l.mustbe( TokenType::NAME);
  if ( !celldefine_mode) {
      temp_node.name = l.last_token.value;
      temp_node.isCompleted = 0;
  } else {
      global_module_name = l.last_token.value;
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
  		  l.mustbe( TokenType::NAME);
		  string temp_name = l.last_token.value;
		  global_signals.push_back( std::make_tuple( global_module_name, direction_tag, l.last_token.value));
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
  temp_node = PnRDB::hierNode();

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


