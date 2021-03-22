cmake_minimum_required(VERSION 3.15..3.18)

#
# Initial Setup
#

# TODO: Single source version number
project(align VERSION "1.0.0")

# High verbosity for debug
set(CMAKE_VERBOSE_MAKEFILE ON CACHE BOOL "ON" FORCE)

# A few safe (for align) defaults
option(BUILD_SHARED_LIBS "Use SHARED keyword to mark shared libraries" OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE TRUE)
set(CMAKE_SKIP_BUILD_RPATH FALSE)
set(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)
set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/thirdparty")
set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
list(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${CMAKE_INSTALL_PREFIX}/lib" isSystemDir)
if("${isSystemDir}" STREQUAL "-1")
    set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
endif("${isSystemDir}" STREQUAL "-1")

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
install(TARGETS PnR DESTINATION align)