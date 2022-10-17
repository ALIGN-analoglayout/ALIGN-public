set(headers
    Geom.h
    Layer.h
    Placement.h
    RTree.h
    Router.h
    Util.h
)

set(sources
    Geom.cpp
    Instance.cpp
    Layer.cpp
    Net.cpp
    Netlist.cpp
    Placement.cpp
    Router.cpp
    Util.cpp
)

add_library(hanan_router STATIC ${sources} ${headers})
target_link_libraries(
     hanan_router PRIVATE
     nlohmann_json::nlohmann_json
     spdlog::spdlog
)
target_code_coverage(hanan_router)
