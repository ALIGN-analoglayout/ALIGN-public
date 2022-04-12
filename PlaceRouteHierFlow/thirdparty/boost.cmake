# Boost v1.75.0 (header-only Boost::boost)
find_package(Boost QUIET COMPONENTS boost)
if (NOT TARGET Boost::boost)
  message(STATUS "Boost not found on host system. Downloading headers.")
  FetchContent_Declare(
    boost
    URL https://boostorg.jfrog.io/artifactory/main/release/1.75.0/source/boost_1_75_0.tar.bz2
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
