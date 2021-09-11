add_subdirectory(PnRDB)
add_subdirectory(placer)
add_subdirectory(router)
add_subdirectory(cap_placer)
add_subdirectory(guard_ring)
add_subdirectory(MNA)

set(sources
     PnR-pybind11.cpp)

add_library(PnR SHARED ${sources} ${headers})
target_include_directories(PnR PRIVATE "/opt/homebrew/include")
target_link_directories(PnR PRIVATE "/opt/homebrew/lib")
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
     lpsolve55
     spdlog
     superlu
     pybind11::module
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
          cap_placer
          guard_ring
          MNA
          # External Dependencies
          lpsolve55
          spdlog
          superlu
          pybind11::module
          GTest::gtest
          GTest::gtest_main)
endif()
