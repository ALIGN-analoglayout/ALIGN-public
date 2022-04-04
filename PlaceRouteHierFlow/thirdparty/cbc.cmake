FetchContent_Declare(
  cbc
  URL https://www.coin-or.org/download/source/Cbc/Cbc-2.10.5.tgz
  URL_HASH MD5=46277180c0fc67f750e2de1836333189
)
find_library(cbc_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Cbc${CMAKE_SHARED_LIBRARY_SUFFIX})
include(ProcessorCount)
if (NOT cbc_lib)
  ProcessorCount(N)
  if (N GREATER 8)
    set (N 8)
  endif ()
  message(STATUS "Building CBC library from source.")
  FetchContent_GetProperties(cbc)
  if(NOT cbc_POPULATED)
    FetchContent_Populate(cbc)
    include(ExternalProject)
    message(STATUS "Cbc src in ${cbc_SOURCE_DIR} ${cbc_BINARY_DIR}")
    message(STATUS ${MAKE})
    message(STATUS ${cbc_PREFIX_DIR})
    ExternalProject_Add(cbc
        SOURCE_DIR ${cbc_SOURCE_DIR}
        CONFIGURE_COMMAND ${cbc_SOURCE_DIR}/configure --enable-cbc-parallel --enable-openmp --disable-zlib --disable-bzlib --without-blas --without-lapack --enable-static --disable-shared --with-pic --prefix=${cbc_BINARY_DIR}
        BUILD_BYPRODUCTS ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Cgl${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Clp${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Cbc${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Osi${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}OsiCbc${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}OsiClp${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}CoinUtils${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}ClpSolver${CMAKE_STATIC_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}CbcSolver${CMAKE_STATIC_LIBRARY_SUFFIX} 
        BUILD_COMMAND make -j${N}
        BUILD_IN_SOURCE 1
        )
    set(cbc_LIBRARIES
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}OsiCbc${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}CbcSolver${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Cbc${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Cgl${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}OsiClp${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}ClpSolver${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Clp${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Osi${CMAKE_STATIC_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}CoinUtils${CMAKE_STATIC_LIBRARY_SUFFIX}
      )
  endif()
else()
  message(STATUS "Using installed Cbc libs.")
  find_library(osicbc_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}OsiCbc${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(cbcsolver_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}CbcSolver${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(cgl_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Cgl${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(osiclp_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}OsiClp${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(clpsolver_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}ClpSolver${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(clp_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Clp${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(osi_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Osi${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(coinutils_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}CoinUtils${CMAKE_SHARED_LIBRARY_SUFFIX})
  set(cbc_LIBRARIES
    ${osicbc_lib}
    ${cbcsolver_lib}
    ${cbc_lib}
    ${cgl_lib}
    ${osiclp_lib}
    ${clpsolver_lib}
    ${clp_lib}
    ${osi_lib}
    ${coinutils_lib}
    )
  if(NOT cbc_POPULATED)
    FetchContent_Populate(cbc)
  endif()
endif()
