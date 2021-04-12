# Boost v1.75.0 (header-only Boost::boost)
find_package(Boost QUIET COMPONENTS boost)
if (NOT TARGET Boost::boost)
  message(STATUS "Boost not found on host system. Downloading headers.")
  FetchContent_Declare(
    boost
    URL https://github.com/boostorg/boost/archive/refs/tags/boost-1.75.0.zip
  )
  FetchContent_GetProperties(boost)
  if(NOT boost_POPULATED)
      FetchContent_Populate(boost)
      add_library(boost INTERFACE)
      target_include_directories(boost INTERFACE ${boost_SOURCE_DIR})
  endif()
  add_library(Boost::boost ALIAS boost)
endif()
