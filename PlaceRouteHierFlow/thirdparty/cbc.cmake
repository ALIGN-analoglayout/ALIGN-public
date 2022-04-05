FetchContent_Declare(
  cbc
  URL https://www.coin-or.org/download/source/Cbc/Cbc-2.10.5.tgz
  URL_HASH MD5=46277180c0fc67f750e2de1836333189
)
if(SKBUILD)
  set(Python_EXECUTABLE "${PYTHON_EXECUTABLE}")
  execute_process(
    COMMAND
      "${Python_EXECUTABLE}" -c
      "import mip; x=mip.__path__; print(x[0] if len(x) else '');"
    OUTPUT_VARIABLE _mip_dir
    OUTPUT_STRIP_TRAILING_WHITESPACE COMMAND_ECHO STDOUT
  )
  if (EXISTS "${_mip_dir}/libraries/lin64")
    set (_mip_dir "${_mip_dir}/libraries/lin64"
    list(APPEND CMAKE_PREFIX_PATH "${_mip_dir}/libraries/lin64")
  else()
    unset (_mip_dir)
  endif()
endif()

if (NOT _mip_dir)
  find_library(cbc_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Cbc${CMAKE_SHARED_LIBRARY_SUFFIX})
else()
  find_library(cbc_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Cbc${CMAKE_SHARED_LIBRARY_SUFFIX} PATHS "${_mip_dir}")
endif()
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
        CONFIGURE_COMMAND ${cbc_SOURCE_DIR}/configure --enable-cbc-parallel --enable-openmp --disable-zlib --disable-bzlib --without-blas --without-lapack --disable-static --enable-shared --with-pic --prefix=${cbc_BINARY_DIR}
        BUILD_BYPRODUCTS ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Cgl${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Clp${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Cbc${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Osi${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiCbc${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiClp${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}CoinUtils${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}ClpSolver${CMAKE_SHARED_LIBRARY_SUFFIX} 
          ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}CbcSolver${CMAKE_SHARED_LIBRARY_SUFFIX} 
        BUILD_COMMAND make -j${N}
        BUILD_IN_SOURCE 1
        )
    set(cbc_LIBRARIES
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiCbc${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}CbcSolver${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Cbc${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Cgl${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiClp${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}ClpSolver${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Clp${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Osi${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${cbc_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}CoinUtils${CMAKE_SHARED_LIBRARY_SUFFIX}
      )
  endif()
else()
  message(STATUS "Using installed Cbc libs : ${cbc_lib}")
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
  FetchContent_GetProperties(cbc)
  if(NOT cbc_POPULATED)
    FetchContent_Populate(cbc)
    message(STATUS "Cbc src in ${cbc_SOURCE_DIR}")
  endif()
endif()
