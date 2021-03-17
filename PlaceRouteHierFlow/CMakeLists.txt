add_subdirectory(PnRDB)
add_subdirectory(placer)
add_subdirectory(router)
add_subdirectory(cap_placer)
add_subdirectory(guard_ring)
add_subdirectory(MNA)

set(headers
     toplevel.h)

set(sources
     toplevel.cpp
     PnR-pybind11.cpp)

add_library(PnR SHARED ${sources} ${headers})
target_link_libraries(
     PnR PRIVATE
     # Internal Dependencies
     PnRDB
     placer
     router
     cap_placer
     guard_ring
     MNA
     # External Dependencies
     lpsolve
     nlohmann_json::nlohmann_json
     spdlog::spdlog
     superlu
     pybind11::module
)