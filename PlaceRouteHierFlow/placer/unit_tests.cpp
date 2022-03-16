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

    design::block b;
    b.counterpart = -1;
    std::vector<design::block> blocks;
    blocks.push_back(b);

    d.Blocks.push_back(blocks);

    d.Ordering_Constraints.push_back(std::make_pair(std::make_pair(0, 0), placerDB::V));

    sp.KeepOrdering(d);


};
