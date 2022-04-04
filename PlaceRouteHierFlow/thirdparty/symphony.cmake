FetchContent_Declare(
  symphony
  URL https://www.coin-or.org/download/source/SYMPHONY/SYMPHONY-5.6.17.tgz
  URL_HASH MD5=59fe0fa58c8bef019967766c86247b9d
)
find_library(symphony_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Sym${CMAKE_SHARED_LIBRARY_SUFFIX})
if (NOT symphony_lib) 
  include(ProcessorCount)
  ProcessorCount(N)
  if (N GREATER 8)
    set (N 8)
  endif ()
  message(STATUS "Building SYMPHONY library from source.")
  FetchContent_GetProperties(symphony)
  if(NOT symphony_POPULATED)
    FetchContent_Populate(symphony)
    include(ExternalProject)
    message(STATUS "Sym src in ${symphony_SOURCE_DIR} ${symphony_BINARY_DIR}")
    message(STATUS ${MAKE})
    message(STATUS ${symphony_PREFIX_DIR})
    ExternalProject_Add(symphony
        SOURCE_DIR ${symphony_SOURCE_DIR}
        CONFIGURE_COMMAND ${symphony_SOURCE_DIR}/configure --disable-openmp --disable-zlib --disable-bzlib --without-blas --without-lapack --disable-static --enable-shared --with-pic --prefix=${symphony_BINARY_DIR}
        BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Sym${CMAKE_SHARED_LIBRARY_SUFFIX}
        BUILD_COMMAND make -j${N}
        BUILD_IN_SOURCE 1
        )
    ExternalProject_Add(Cgl
        SOURCE_DIR ${symphony_SOURCE_DIR}/Cgl
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ""
        BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Cgl${CMAKE_SHARED_LIBRARY_SUFFIX}
        BUILD_IN_SOURCE 1
        )
    set(symphony_LIBRARIES
      ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Sym${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Cgl${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Clp${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Osi${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiSym${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiClp${CMAKE_SHARED_LIBRARY_SUFFIX}
      ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}CoinUtils${CMAKE_SHARED_LIBRARY_SUFFIX}
      )
    
    ExternalProject_Add(Clp
        SOURCE_DIR ${symphony_SOURCE_DIR}/Clp
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ""
        BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Clp${CMAKE_SHARED_LIBRARY_SUFFIX}
        )
    ExternalProject_Add(CoinUtils
        SOURCE_DIR ${symphony_SOURCE_DIR}/CoinUtils
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ""
        BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}CoinUtils${CMAKE_SHARED_LIBRARY_SUFFIX}
        )
    ExternalProject_Add(Osi
        SOURCE_DIR ${symphony_SOURCE_DIR}/Osi
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ""
        BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}Osi${CMAKE_SHARED_LIBRARY_SUFFIX}
        )
    ExternalProject_Add(OsiSym
        SOURCE_DIR ${symphony_SOURCE_DIR}/SYMPHONY/src/OsiSym
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ""
        BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiSym${CMAKE_SHARED_LIBRARY_SUFFIX}
        )
    ExternalProject_Add(OsiClp
        SOURCE_DIR ${symphony_SOURCE_DIR}/Clp/src/OsiClp
        CONFIGURE_COMMAND ""
        BUILD_COMMAND ""
        INSTALL_COMMAND ""
        BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}OsiClp${CMAKE_SHARED_LIBRARY_SUFFIX}
        )
  endif()
else()
  message(STATUS "Using installed SYMPHONY libs.")
  message(STATUS "Sym src in ${symphony_SOURCE_DIR} ${symphony_BINARY_DIR}")
  find_library(cgl_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Cgl${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(clp_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Clp${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(osi_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}Osi${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(osisym_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}OsiSym${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(osiclp_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}OsiClp${CMAKE_SHARED_LIBRARY_SUFFIX})
  find_library(coinutils_lib NAMES ${CMAKE_SHARED_LIBRARY_PREFIX}CoinUtils${CMAKE_SHARED_LIBRARY_SUFFIX})
  set(symphony_LIBRARIES
    ${symphony_lib}
    ${cgl_lib}
    ${clp_lib}
    ${osi_lib}
    ${osisym_lib}
    ${osiclp_lib}
    ${coinutils_lib}
    )
  FetchContent_GetProperties(symphony)
  if(NOT symphony_POPULATED)
    FetchContent_Populate(symphony)
  endif()
endif()
