#include "readfile.h"

vector<string> StringSplitbyChar(const string& s, char delimiter) {
  std::vector<std::string> tokens;
  std::string token;
  std::istringstream tokenStream(s);
  while (std::getline(tokenStream, token, delimiter)) {
    tokens.push_back(token);
  }
  return tokens;
}

vector<string> readfile_lines(string filename) {
  vector<string> output;
  string temp;
  ifstream fin;
  fin.open(filename.c_str());
  while (!fin.eof()) {
    getline(fin, temp);
    output.push_back(temp);
  }
  fin.close();
  return output;
}
string readfile_string(string filename) {
  ifstream fin;
  string line;
  string output;
  fin.open(filename.c_str());
  while (!fin.eof()) {
    getline(fin, line);
    output += line + '\n';
  }
  fin.close();
  return output;
}
vector<string> readfile_words(string filename) {
  ifstream fin;
  string line;
  vector<string> output;
  // int recording=0;
  fin.open(filename.c_str());
  while (!fin.eof()) {
    getline(fin, line);
    int recording = 0;
    for (unsigned int i = 0; i < line.length(); i++) {
      if (line[i] != ' ' && line[i] != '\n') {
        if (recording == 0) {
          output.push_back("");
          recording = 1;
        }
        output.back() += line[i];
      } else {
        recording = 0;
      }
    }
  }
  fin.close();
  return output;
}

vector<string> split_by_spaces(string text) {
  string word;
  vector<string> output;
  istringstream iss(text);
  while (iss) {
    iss >> word;
    output.push_back(word);
  }
  return output;
}

vector<string> split_by_spaces_yg(string text) {
  string word;
  vector<string> output;
  istringstream iss(text);
  while (iss >> word) {
    output.push_back(word);
  }
  return output;
}
vector<string> get_true_word(int start, string text, int textnum, char endflag, int* p) {
  vector<string> output;
  unsigned int i;
  bool recording = 0;
  if (textnum > 0) {
    int record_num = 0;
    for (i = start; i < text.length(); i++) {
      if (text[i] >= '!') {
        if (recording == 0) {
          output.push_back("");
          recording = 1;
          record_num++;
        }
        output.back() += text[i];
      } else if (record_num >= textnum) {
        break;
      } else {
        recording = 0;
      }
    }
  } else {
    for (i = start; i < text.length(); i++) {
      if (text[i] == endflag) {
        break;
      } else if (text[i] != ' ' && text[i] != '\n') {
        if (recording == 0) {
          output.push_back("");
          recording = 1;
        }
        output.back() += text[i];
      } else {
        recording = 0;
      }
    }
  }
  *p = i;
  return output;
}

////////////////////add by yg///////////////////////////////
string get_word(string text, char startflag, char endflag) {
  string output;
  int start = 0;
  int end = 0;
  for (unsigned int i = 0; i < text.length(); i++) {
    if (text[i] == startflag) {
      start = i;
      continue;
    } else {
      if (text[i] == endflag) {
        end = i;
        break;
      }
    }
  }
  output = text.substr(start + 1, end - start - 1);
  return output;
}
