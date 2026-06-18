# lpsolve 5.5.2.11
FetchContent_Declare(
  lpsolve
  URL https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.11/lp_solve_5.5.2.11_source.tar.gz/download
  URL_HASH MD5=a829a8d9c60ff81dc72ff52363703886
)
# Use bare name so cmake resolves the platform extension (.so on Linux, .dylib on macOS).
find_library(
  lpsolve_lib
  NAMES lpsolve55 liblpsolve55.so
  PATH_SUFFIXES lpsolve lp_solve)
if (NOT lpsolve_lib)
  message(STATUS "lpsolve library file not found. Building from source.")
  FetchContent_GetProperties(lpsolve)
  if(NOT lpsolve_POPULATED)
    FetchContent_Populate(lpsolve)
    configure_file(
      ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.lpsolve
      ${lpsolve_SOURCE_DIR}/CMakeLists.txt
      COPYONLY)
    add_subdirectory(${lpsolve_SOURCE_DIR} ${lpsolve_BINARY_DIR})
    target_include_directories(lpsolve55 INTERFACE ${lpsolve_SOURCE_DIR})
  endif()
  add_library(lpsolve::lpsolve55 ALIAS lpsolve55)
else()
  # Library found system-wide (e.g. brew install lp_solve on macOS, lpsolve-devel on Linux).
  # Use find_path for headers so we never need the SourceForge tarball download.
  message(STATUS "lpsolve library file found at ${lpsolve_lib}. Using system headers.")
  find_path(lpsolve_include_dir NAMES lp_lib.h PATH_SUFFIXES lpsolve lp_solve)
  add_library(lpsolve SHARED IMPORTED)
  if (lpsolve_include_dir)
    target_include_directories(lpsolve INTERFACE ${lpsolve_include_dir})
  endif()
  set_property(
    TARGET lpsolve
    PROPERTY IMPORTED_LOCATION ${lpsolve_lib})
  add_library(lpsolve::lpsolve55 ALIAS lpsolve)
endif()
