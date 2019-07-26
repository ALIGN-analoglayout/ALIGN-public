#ifndef READFILE_h_
#define READFILE_h_

#include <string>
#include <iostream>
#include <fstream>
#include <vector>
#include <sstream>
using std::string;
using std::vector;
using std::ifstream;
using std::istringstream;


vector<string> readfile_lines(string filename);
string readfile_string(string filename);
vector<string> readfile_words(string filename);
vector<string> split_by_spaces(string text);
vector<string> split_by_spaces_yg(string text);
vector<string> get_true_word(int start,string text,int textnum,char endflag,int *p);
vector<string> StringSplitbyChar(const string& s, char delimiter);
string get_word(string text, char starflag, char endflag);  ///////////////added by yg

#endif
