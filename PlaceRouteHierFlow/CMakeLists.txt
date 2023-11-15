add_subdirectory(PnRDB)
add_subdirectory(placer)
add_subdirectory(EA_placer)
add_subdirectory(router)
add_subdirectory(hanan_router)
add_subdirectory(cap_placer)
add_subdirectory(guard_ring)
add_subdirectory(MNA)

set(sources
     PnR-pybind11.cpp)

add_library(PnR SHARED ${sources} ${headers})

target_link_libraries(
     PnR PRIVATE
     # Internal Dependencies
     PnRDB
     placer
     EA_placer
     router
     hanan_router
     cap_placer
     guard_ring
     MNA
     # External Dependencies
     lpsolve::lpsolve55
     nlohmann_json::nlohmann_json
     spdlog::spdlog
     superlu
     pybind11::module
     Boost::boost
     ilp_solver::ilp_solver
)
target_code_coverage(PnR)

if(CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME AND BUILD_TESTING)
     add_executable(test_PnR
          unit_tests.cpp
          PnRDB/unit_tests.cpp
          placer/unit_tests.cpp
          router/unit_tests.cpp
          cap_placer/unit_tests.cpp
          )

     target_link_libraries(
          test_PnR
          # Internal Dependencies
          PnRDB
          placer
          router
          hanan_router
          cap_placer
          guard_ring
          MNA
          # External Dependencies
          lpsolve::lpsolve55
          ilp_solver::ilp_solver
          nlohmann_json::nlohmann_json
          spdlog::spdlog
          superlu
          pybind11::module
          Boost::boost
          GTest::gtest
          GTest::gtest_main)
endif()
