#include "spdlog/spdlog.h"

#include <gtest/gtest.h>
#include "SeqPair.h"
#include "design.h"

TEST(PlacerTest, True) {
    EXPECT_TRUE( 1);
};

TEST(PlacerTest, False) {
    EXPECT_FALSE( 0);
};

TEST(SeqPairTest, Constructor) {
    spdlog::set_level(spdlog::level::debug);
    SeqPair sp;
    sp.PrintSeqPair();
};

TEST(SeqPairTest, KeepOrdering) {
    spdlog::set_level(spdlog::level::debug);
    SeqPair sp;
    sp.PrintSeqPair();

    design d;

    std::vector<int> counterparts = {0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,11,13,12,-1,-1,-1,-1,-1};
    
    for (const auto& counterpart : counterparts) {
      design::block b;
      b.counterpart = counterpart;
      std::vector<design::block> blocks;
      blocks.push_back(b);
      d.Blocks.push_back(blocks);
    }

    std::vector<std::pair<int,int> > orderings =  {
      {0, 11},
      {0, 11},
      {0, 12},
      {0, 13},
      {0, 13},
      {0, 12},
      {0, 14},
      {0, 15},
      {11, 16},
      {11, 17},
      {11, 18},
      {11, 1},
      {12, 16},
      {12, 17},
      {12, 18},
      {12, 1},
      {13, 16},
      {13, 17},
      {13, 18},
      {13, 1},
      {14, 16},
      {14, 17},
      {14, 18},
      {14, 1},
      {15, 16},
      {15, 17},
      {15, 18},
      {15, 1},
      {16, 2},
      {16, 3},
      {16, 4},
      {16, 5},
      {16, 6},
      {16, 7},
      {17, 2},
      {17, 3},
      {17, 4},
      {17, 5},
      {17, 6},
      {17, 7},
      {18, 2},
      {18, 3},
      {18, 4},
      {18, 5},
      {18, 6},
      {18, 7},
      {1, 2},
      {1, 3},
      {1, 4},
      {1, 5},
      {1, 6},
      {1, 7},
      {2, 8},
      {2, 9},
      {3, 8},
      {3, 9},
      {4, 8},
      {4, 9},
      {5, 8},
      {5, 9},
      {6, 8},
      {6, 9},
      {7, 8},
      {7, 9},
      {8, 10},
      {9, 10},
      {11, 12},
      {12, 13},
      {13, 14},
      {14, 15},
      {16, 17},
      {17, 18},
      {18, 1},
      {2, 3},
      {3, 4},
      {4, 5},
      {5, 6},
      {6, 7},
      {8, 9}
    };

    for (const auto& ordering : orderings) {
      d.Ordering_Constraints.push_back(make_pair(ordering, placerDB::V));
    }

    sp.KeepOrdering(d);


};
