#include <nlohmann/json.hpp>
#include <gtest/gtest.h>

using namespace nlohmann;

namespace {

  TEST( JSONTestcase, Equals) {
// create an empty structure (null)
    json j;

// add a number that is stored as double (note the implicit conversion of j to an object)
    j["pi"] = 3.141;

// add a Boolean that is stored as bool
    j["happy"] = true;

// add a string that is stored as std::string
    j["name"] = "Niels";

// add another null object by passing nullptr
    j["nothing"] = nullptr;

// add an object inside the object
    j["answer"]["everything"] = 42;

// add an array that is stored as std::vector (using an initializer list)
    j["list"] = { 1, 0, 2 };

// add another object (using an initializer list of pairs)
    j["object"] = { {"currency", "USD"}, {"value", 42.99} };

// instead, you could also write (which looks very similar to the JSON above)
    json j2 = {
      {"pi", 3.141},
      {"happy", true},
      {"name", "Niels"},
      {"nothing", nullptr},
      {"answer", {
	  {"everything", 42}
	}},
      {"list", {1, 0, 2}},
      {"object", {
	  {"currency", "USD"},
	  {"value", 42.99}
	}}
    };

    EXPECT_EQ( j, j2);
  }

  TEST( JSONTestcase, HierObject) {
    json j;
    j["hi"] = { {"one", 1}, {"two", 2}};

    EXPECT_EQ( j["hi"]["one"], 1);
    EXPECT_EQ( j["hi"]["two"], 2);

  }

}
