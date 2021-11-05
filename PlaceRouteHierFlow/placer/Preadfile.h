#ifndef PREADFILE_h_
#define PREADFILE_h_

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using std::ifstream;
using std::istringstream;
using std::string;
using std::vector;

vector<string> readfile_lines(string filename);
string readfile_string(string filename);
vector<string> readfile_words(string filename);
vector<string> split_by_spaces(string text);
vector<string> get_true_word(int start, string text, int textnum, char endflag, int* p);
vector<string> StringSplitbyChar(const string& s, char delimiter);

#endif
