
#include <gtest/gtest.h>
#include <string>
#include <iostream>
#include "./PnRDB/datatype.h"
#include "./PnRDB/PnRdatabase.h"
#include "./placer/Placer.h"
#include "./router/Router.h"
#include "./cap_placer/capplacer.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>
#include <sstream>

#include <vector>
#include <unordered_set>
#include <set>

using std::string;
using std::cout;
using std::endl;

using namespace nlohmann;

TEST(PnRTest, True) {
  EXPECT_TRUE( 1);
};

struct VectorHasher {
    int operator()(const vector<int> &V) const {
        int hash = V.size();
        for(auto &i : V) {
            hash ^= i + 0x9e3779b9 + (hash << 6) + (hash >> 2);
        }
        return hash;
    }
};

TEST(PnRTest, UnorderedSetOfVecOfInt) {

  std::unordered_set<std::vector<int>,VectorHasher> s;

  std::vector<int> a = {0, 1, 3};
  std::vector<int> b = {0, 3, 1};

  
  VectorHasher vh;

  EXPECT_TRUE(vh(a) != vh(b));


  s.insert(a);
  s.insert(b);
    
  s.insert(a);

  EXPECT_TRUE(s.find(a) != s.end());

  EXPECT_TRUE(s.find(b) != s.end());

  s.erase(a);

  EXPECT_TRUE(s.find(a) == s.end());

  s.erase(b);

  EXPECT_TRUE(s.find(b) == s.end());

};

TEST(PnRTest, SetOfVecOfInt) {

  std::set<std::vector<int> > s;

  std::vector<int> a = {0, 1, 3};
  std::vector<int> b = {0, 3, 1};

  s.insert(a);
  s.insert(b);
    
  s.insert(a);

  EXPECT_TRUE(s.find(a) != s.end());

  EXPECT_TRUE(s.find(b) != s.end());

  s.erase(a);

  EXPECT_TRUE(s.find(a) == s.end());

  s.erase(b);

  EXPECT_TRUE(s.find(b) == s.end());

};
