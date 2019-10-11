#ifndef LEXER_H_
#define LEXER_H_

using std::string;
using std::cout;
using std::endl;
using std::istream;
using std::ostream;

enum class TokenType {
           EndOfFile=0, EndOfLine=1, NAME=2, Undefined=3, NUMBER=4,
	   COMMA=',', LPAREN='(', RPAREN=')', BACKQUOTE='`', 
	   SEMICOLON=';', PERIOD='.'
      };

inline ostream& operator<<( ostream& os, const TokenType& tt) {
    string str;
    if        ( tt == TokenType::EndOfFile) {
      str = "EndOfFile";
    } else if ( tt == TokenType::EndOfLine) {
      str = "EndOfLine";
    } else if ( tt == TokenType::NAME) {
      str = "NAME";
    } else if ( tt == TokenType::Undefined) {
      str = "Undefined";
    } else if ( tt == TokenType::NUMBER) {
      str = "NAME";
    } else {
      str = "' '";
      str[1] = static_cast<char>( tt);
    }

    os << str;
    return os;
}

class Token {
public:
  TokenType tt;
  string value;
  friend ostream& operator<<( ostream& os, const Token& t) {
    os << "(" << t.tt << "," << t.value << ")";
    return os;
  }
};

class CharBitVector {
  std::vector<char> bv;
public:
 CharBitVector() : bv(256,0) {}

  void add_is_alpha() {
    for (unsigned int i=0; i<256; ++i) {
      if ( isalpha(i)) {
	bv[i] = 1;
      }
    }
  }

  void add_is_digit() {
    for (unsigned int i=0; i<256; ++i) {
      if ( isdigit(i)) {
	bv[i] = 1;
      }
    }
  }

  void add_extra( const char *p) {
    while ( *p != '\0') {
      bv[*p] = 1;
      ++p;
    }
  }

  bool operator()( char c) {
    return 0 <= c && c < 256 && bv[c];
  }

};


class Lexer {
    istream& s; 

    string line;
    unsigned int cursor;
    int line_num;

    CharBitVector is_first_in_name;
    CharBitVector is_not_first_in_name;
    CharBitVector is_single_character_punct;

public:
    int failed = 0; /* running=0, failed=1 */ 

    Token last_token;
    Token current_token;
    
    bool skip_EndOfLine_tokens;

    Lexer( istream& sin, bool skip_EOLN = 0) :
       s(sin), skip_EndOfLine_tokens(skip_EOLN) {
      is_first_in_name.add_is_alpha();
      is_first_in_name.add_extra( "_");

      is_not_first_in_name.add_is_alpha();
      is_not_first_in_name.add_is_digit();
      is_not_first_in_name.add_extra( "_!|+<>");

      is_single_character_punct.add_extra( ".,;()`");

      line_num = 0;
      current_token.tt = TokenType::EndOfLine;
      get_token();
    }

    void get_token() {
      if ( skip_EndOfLine_tokens) {
	get_token_no_EndOfLine();
      } else {
	get_token_with_EndOfLine();
      }
    }

    void get_token_no_EndOfLine() {
      do {
	get_token_with_EndOfLine();
      } while ( current_token.tt == TokenType::EndOfLine);
    }

    void get_token_with_EndOfLine() {
      last_token = current_token;

      if ( last_token.tt == TokenType::EndOfFile) {
	return;
      }

      current_token.value = "";
      while ( last_token.tt == TokenType::EndOfLine) {
	if ( s.peek() == EOF) {
	  current_token.tt = TokenType::EndOfFile;
	  return;
	}

	getline( s, line);
	cursor = 0;
	++line_num;

	// Check for beginning of the line comment
	if ( line.size() >= 2 && line[0] == '/' && line[1] == '/') {
	} else {
	  break;
	}
      }
	
      // Eat white space
      while ( cursor < line.size() && isspace( line[cursor])) {
	++cursor;
      }

      if ( cursor >= line.size()) {
	current_token.tt = TokenType::EndOfLine;
	return;
      }

      if ( is_single_character_punct( line[cursor])) {
	current_token.tt = static_cast<TokenType>( line[cursor]);
	current_token.value.push_back( line[cursor]);
	++cursor;
      } else if ( isdigit( line[cursor])) {
	current_token.tt = TokenType::NUMBER;	
	current_token.value.push_back( line[cursor]);
	++cursor;
	while ( cursor < line.size() &&
		isdigit( line[cursor])) {
	  current_token.value.push_back( line[cursor]);
	  ++cursor;
	}
      } else if ( is_first_in_name(line[cursor])) {
	current_token.tt = TokenType::NAME;
	current_token.value.push_back( line[cursor]);
	++cursor;
	while ( cursor < line.size() &&
		is_not_first_in_name( line[cursor])) {
	  current_token.value.push_back( line[cursor]);
	  ++cursor;
	}
      } else {
	current_token.tt = TokenType::Undefined;
	current_token.value.push_back( line[cursor]);
	++cursor;
      }

    }

    bool have( TokenType tt) {
      if ( current_token.tt == tt) {
	get_token();
	return 1;
      } else {
	return 0;
      }
    }

    void mustbe( TokenType tt) {
      if ( !have( tt)) {
	std::ostringstream os;
	os << "Expected token type " << tt << " got " << current_token.tt << endl;
	error( os.str());
      }
    }

    bool have_keyword( const string& k) {
      if ( current_token.tt == TokenType::NAME &&
	   current_token.value == k) {
	get_token();
	return 1;
      } else {
	return 0;
      }
    }

    void mustbe_keyword( const string& k) {
      if ( !have_keyword( k)) {
	std::ostringstream os;
	os << "Expected keyword " << k << " got " << current_token;
	error( os.str());
      }
    }

    void error( const string& k) {
      cout << "Syntax error at line " << line_num << " position " << cursor << ": " << k << endl;
      failed = 1;
      assert( !failed);
    }

};

#endif
