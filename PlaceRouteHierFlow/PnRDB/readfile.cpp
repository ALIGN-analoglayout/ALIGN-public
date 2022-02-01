#include "readfile.h"
#include <cassert>

vector<string> get_true_word(int start, string text, int textnum, char endflag, int* p) {
  vector<string> output;
  unsigned int i;
  bool recording = 0;
  assert(textnum == 0);

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

  *p = i;
  return output;
}
