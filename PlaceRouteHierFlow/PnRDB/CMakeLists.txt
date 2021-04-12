set(headers
     Lexer.h
     PnRdatabase.h
     datatype.h
     readfile.h
)

set(sources
     readfile.cpp
     PnRdatabase.cpp
     ReadDesignRule.cpp
     ReadDesignRuleJson.cpp
     HardDesignRule.cpp
     WriteJSON.cpp
     ReadVerilog.cpp
     ReadConstraint.cpp
     Print.cpp
     ReadLEF.cpp
     PnRDBJSON.cpp
)

add_library(PnRDB STATIC ${sources} ${headers})

target_link_libraries(
     PnRDB PRIVATE
     nlohmann_json::nlohmann_json
     spdlog::spdlog
)
target_code_coverage(PnRDB)
