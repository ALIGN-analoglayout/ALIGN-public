cmake_minimum_required(VERSION 3.15..3.18)

#
# Initial Setup
#

# TODO: Single source version number
project(align VERSION "${ALIGN_VERSION}")

# Options to control build
option(
    BUILD_TESTING
    "Builds test/test_PnR in developer mode (`pip install -e . --no-build-isolation`)"
    OFF)
option(
    CODE_COVERAGE
    "Instruments code coverage (pip install -e . --no-build-isolation --install-option='-DCODE_COVERAGE=ON')"
    OFF)
# High verbosity for debug
set(CMAKE_VERBOSE_MAKEFILE ON CACHE BOOL "ON" FORCE)

# Compiler defaults
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

function(target_code_coverage target)
  if(CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME AND CODE_COVERAGE)
      target_compile_options(${target} PUBLIC --coverage)
      target_link_options(${target} PUBLIC --coverage)
  endif()
endfunction()

# A few safe (for align) library defaults
option(BUILD_SHARED_LIBS "Use SHARED keyword to mark shared libraries" OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE TRUE)
set(CMAKE_SKIP_BUILD_RPATH FALSE)
set(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)

# May need to limit ninja's max concurrency for CIRCLECI
if(DEFINED ENV{MAX_JOBS})
  message(STATUS "Limiting maximum number of compile jobs to $ENV{MAX_JOBS}")
  set_property(GLOBAL APPEND PROPERTY JOB_POOLS compile_pool=$ENV{MAX_JOBS})
  set(CMAKE_JOB_POOL_COMPILE compile_pool)
endif()

#
# Get the following CPP dependencies
# STATIC: json, spdlog, superlu, boost
# SHARED: lpsolve, pybind11
#

include(FetchContent)
include(PlaceRouteHierFlow/thirdparty/json.cmake)
include(PlaceRouteHierFlow/thirdparty/spdlog.cmake)
include(PlaceRouteHierFlow/thirdparty/superlu.cmake)
include(PlaceRouteHierFlow/thirdparty/boost.cmake)
include(PlaceRouteHierFlow/thirdparty/ilpif.cmake)
include(PlaceRouteHierFlow/thirdparty/pybind11.cmake)
if(CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME AND BUILD_TESTING)
  include(PlaceRouteHierFlow/thirdparty/googletest.cmake)
endif()

#
# Build C++ code residing in the following directories:
# - PlaceRouteHierFlow
#
add_subdirectory(PlaceRouteHierFlow)

#
# Install the following python extensions
# - align.PnR
#
pybind11_extension(PnR)
install(TARGETS PnR DESTINATION "${CMAKE_INSTALL_PREFIX}/align")
set_target_properties(PnR PROPERTIES
  INSTALL_RPATH "$ORIGIN/thirdparty"
  INSTALL_RPATH_USE_LINK_PATH TRUE
)

#
# Install the following executables
# when called using `pip install -e .`
# - tests/test_PnR
#
if(CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME AND BUILD_TESTING)
  install(TARGETS test_PnR DESTINATION "${CMAKE_INSTALL_PREFIX}/tests")
  set_target_properties(test_PnR PROPERTIES
    INSTALL_RPATH "$ORIGIN/../align/thirdparty"
    INSTALL_RPATH_USE_LINK_PATH TRUE
  )
endif()

#
# Write out a temporary file with cmake info so
# that we may import from conftest.py for coverage
# - tests/_cmake.py
#
if(CMAKE_PROJECT_NAME STREQUAL PROJECT_NAME AND CODE_COVERAGE)
    file(WRITE "${CMAKE_BINARY_DIR}/tests/_cmake.py" "CMAKE_BINARY_DIR='${CMAKE_BINARY_DIR}';CMAKE_SOURCE_DIR='${CMAKE_SOURCE_DIR}'")
    install(FILES "${CMAKE_BINARY_DIR}/tests/_cmake.py" DESTINATION "${CMAKE_INSTALL_PREFIX}/tests/")
endif()
