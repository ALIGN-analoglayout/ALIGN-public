set(headers
     capplacer.h
     CapPlacerIfc.h
)

set(sources
     capplacer.cpp
     CapPlacerIfc.cpp
)

add_library(cap_placer STATIC ${sources} ${headers})
target_link_libraries(
     cap_placer PRIVATE
     nlohmann_json::nlohmann_json
     spdlog::spdlog
)
target_code_coverage(cap_placer)