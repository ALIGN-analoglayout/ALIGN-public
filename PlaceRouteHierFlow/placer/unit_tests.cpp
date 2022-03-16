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

    sp.KeepOrdering(d);


};
