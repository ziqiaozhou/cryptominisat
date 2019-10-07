#include "gtest/gtest.h"
#include "count.h"
class CountTest : public ::testing::Test{

}
TEST_F(CountTest, ReadVictimModel)
{
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
