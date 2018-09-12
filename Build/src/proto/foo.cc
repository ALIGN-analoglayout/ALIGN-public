#include <iostream>
#include <fstream>
#include <string>
#include "b.pb.h"
#include <google/protobuf/util/json_util.h>
using namespace std;

int main() {
  Person person;
  person.set_id( 0);
  person.set_name( "Steve");
  std::string str;
  auto options = google::protobuf::util::JsonPrintOptions();
  options.add_whitespace = true;
  options.always_print_primitive_fields = true;
  google::protobuf::util::MessageToJsonString( person, &str, options);
  std::cout << str << std::endl;
  return 0;
}
