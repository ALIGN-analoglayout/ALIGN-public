
#include <gtest/gtest.h>
#include "PnRdatabase.h"

TEST(PnRTest, True) {
    EXPECT_TRUE( 1);
};

TEST(PnRTest, PnRdatabase_Constructor) {
  PnRdatabase foo;
  EXPECT_EQ( foo.get_unitScale(), 2000);
}


