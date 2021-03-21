cmake_minimum_required(VERSION 3.15..3.18)

#
# Initial Setup
#

# TODO: Single source version number
project(align VERSION "1.0.0")

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
# SHARED: lpsolve
#

include(FetchContent) # CMAKE projects
include(ExternalProject) # non-CMAKE projects

# json v3.7.3
FetchContent_Declare(
    json
    GIT_REPOSITORY https://github.com/ArthurSonzogni/nlohmann_json_cmake_fetchcontent
    GIT_TAG v3.7.3
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
FetchContent_MakeAvailable(json)

# spdlog v1.x
FetchContent_Declare(
    spdlog
    GIT_REPOSITORY https://github.com/gabime/spdlog.git
    GIT_TAG        v1.x
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
FetchContent_MakeAvailable(spdlog)

# superlu v5.2.2
FetchContent_Declare(
    superlu
    GIT_REPOSITORY https://github.com/xiaoyeli/superlu.git
    GIT_TAG        v5.2.2
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
FetchContent_MakeAvailable(superlu)

# Boost v1.75.0 (header-only Boost::boost)
find_package(Boost QUIET COMPONENTS boost)
if (NOT TARGET Boost::boost)
  message(STATUS "Boost not found on host system. Downloading headers.")
  FetchContent_Declare(
    boost
    URL https://dl.bintray.com/boostorg/release/1.75.0/source/boost_1_75_0.tar.bz2
    URL_HASH SHA256=953db31e016db7bb207f11432bef7df100516eeb746843fa0486a222e3fd49cb
  )
  FetchContent_GetProperties(boost)
  if(NOT boost_POPULATED)
      FetchContent_Populate(boost)
      add_library(boost INTERFACE)
      target_include_directories(boost INTERFACE ${boost_SOURCE_DIR})
  endif()
  add_library(Boost::boost ALIAS boost)
endif()

# lpsolve 5.5.2.11
FetchContent_Declare(
  lpsolve
  URL https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.11/lp_solve_5.5.2.11_source.tar.gz/download
  URL_HASH MD5=a829a8d9c60ff81dc72ff52363703886
)
find_library(
  lpsolve_lib
  NAMES liblpsolve55.so
  PATH_SUFFIXES lpsolve lp_solve)
if (NOT lpsolve_lib)
  message(STATUS "lpsolve library file not found. Building from source.")
  FetchContent_GetProperties(lpsolve)
  if(NOT lpsolve_POPULATED)
    FetchContent_Populate(lpsolve)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.txt
      ${lpsolve_SOURCE_DIR}
      COPYONLY)
    add_subdirectory(${lpsolve_SOURCE_DIR} ${lpsolve_BINARY_DIR})
    target_include_directories(lpsolve55 INTERFACE ${lpsolve_SOURCE_DIR})
  endif()
  add_library(lpsolve::lpsolve55 ALIAS lpsolve55)
else()
  message(STATUS "lpsolve library file found. Using headers from source distribution.")
  FetchContent_GetProperties(lpsolve)
  if(NOT lpsolve_POPULATED)
    FetchContent_Populate(lpsolve)
    add_library(lpsolve SHARED IMPORTED)
    target_include_directories(lpsolve INTERFACE ${lpsolve_SOURCE_DIR})
    set_property(
      TARGET lpsolve
      PROPERTY IMPORTED_LOCATION ${lpsolve_lib})
  endif()
  add_library(lpsolve::lpsolve55 ALIAS lpsolve)
endif()

# python: Point to existing installation
# (Steps from https://github.com/pybind/scikit_build_example)
if(SKBUILD)
  set(Python_EXECUTABLE "${PYTHON_EXECUTABLE}")
  set(Python_INCLUDE_DIR "${PYTHON_INCLUDE_DIR}")
  set(Python_LIBRARY "${PYTHON_LIBRARY}")
endif()
execute_process(
  COMMAND
    "${Python_EXECUTABLE}" -c
    "import pybind11; print(pybind11.get_cmake_dir())"
  OUTPUT_VARIABLE _tmp_dir
  OUTPUT_STRIP_TRAILING_WHITESPACE COMMAND_ECHO STDOUT
)
list(APPEND CMAKE_PREFIX_PATH "${_tmp_dir}")
set(Python_FIND_IMPLEMENTATIONS CPython)
find_package(Python COMPONENTS Interpreter Development)

# pybind11: Point to existing install
find_package(pybind11 CONFIG REQUIRED)

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