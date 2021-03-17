cmake_minimum_required(VERSION 3.15..3.18)

#
# Initial Setup
# TODO: Single source version number
project(align VERSION "1.0.0")
# We will finally export a dynamic library
SET(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} -fPIC")

#
# Get the following CPP dependencies
# STATIC: json, spdlog, superlu
# SHARED: lpsolve, boost
#

include(FetchContent) # CMAKE projects
include(ExternalProject) # non-CMAKE projects

# json: CMAKE project
FetchContent_Declare(
    json
    GIT_REPOSITORY https://github.com/ArthurSonzogni/nlohmann_json_cmake_fetchcontent
    GIT_TAG v3.7.3
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
FetchContent_MakeAvailable(json)

# spdlog: CMAKE project
FetchContent_Declare(
    spdlog
    GIT_REPOSITORY https://github.com/gabime/spdlog.git
    GIT_TAG        v1.x
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
FetchContent_MakeAvailable(spdlog)

# superlu: CMAKE project
FetchContent_Declare(
    superlu
    GIT_REPOSITORY https://github.com/xiaoyeli/superlu.git
    GIT_TAG        v5.2.2
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
FetchContent_MakeAvailable(superlu)

# lpsolve: Use precompiled .so & .h tarball
add_library(lpsolve SHARED IMPORTED)
ExternalProject_Add(
    lpsolve_getter
    URL https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.11/lp_solve_5.5.2.11_dev_ux64.tar.gz/download
    URL_HASH MD5=66fe051d8f3e964624b925b8899b7588
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
ExternalProject_Get_Property(lpsolve_getter SOURCE_DIR)
set_property(TARGET lpsolve PROPERTY IMPORTED_LOCATION
    "${SOURCE_DIR}/liblpsolve55.so")
target_include_directories(lpsolve
    INTERFACE "${SOURCE_DIR}")

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
install(TARGETS PnR DESTINATION .)
