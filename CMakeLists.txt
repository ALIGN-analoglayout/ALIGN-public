cmake_minimum_required(VERSION 3.15..3.18)

#
# Initial Setup
#

# TODO: Single source version number
project(align VERSION "1.0.0")
set(ALIGN_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}/align")
set(ALIGN_INSTALL_LIBDIR "${ALIGN_INSTALL_PREFIX}/thirdparty")

# High verbosity for debug
set(CMAKE_VERBOSE_MAKEFILE ON CACHE BOOL "ON" FORCE)

# Compiler defaults
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Choose Release or Debug" FORCE)
endif()
if(NOT CMAKE_CXX_STANDARD)
    set(CMAKE_CXX_STANDARD 14)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)
endif()

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
include(PlaceRouteHierFlow/thirdparty/lpsolve.cmake)
include(PlaceRouteHierFlow/thirdparty/pybind11.cmake)
if(ALIGN_BUILD_TESTING)
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
install(TARGETS PnR DESTINATION "${ALIGN_INSTALL_PREFIX}")
set_target_properties(PnR PROPERTIES
  INSTALL_RPATH "$ORIGIN/thirdparty"
  INSTALL_RPATH_USE_LINK_PATH TRUE
)

#
# Install the following executables
# when called using `pip install -e .`
# - tests/test_PnR
#
if(ALIGN_BUILD_TESTING)
  install(TARGETS test_PnR DESTINATION "${CMAKE_INSTALL_PREFIX}/tests")
  set_target_properties(test_PnR PROPERTIES
    INSTALL_RPATH "$ORIGIN/../align/thirdparty"
    INSTALL_RPATH_USE_LINK_PATH TRUE
  )
endif()