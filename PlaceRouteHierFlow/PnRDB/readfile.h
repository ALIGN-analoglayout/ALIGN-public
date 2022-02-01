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

vector<string> get_true_word(int start,string text,int textnum,char endflag,int *p);

#endif
