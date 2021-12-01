FetchContent_Declare(
  symphony
  URL https://www.coin-or.org/download/source/SYMPHONY/SYMPHONY-5.6.17.tgz
  URL_HASH MD5=59fe0fa58c8bef019967766c86247b9d
)
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
      CONFIGURE_COMMAND ${symphony_SOURCE_DIR}/configure --disable-zlib --disable-bzlib --without-blas --without-lapack --enable-static --disable-shared --with-pic --prefix=${symphony_BINARY_DIR}
      BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Sym${CMAKE_STATIC_LIBRARY_SUFFIX}
      BUILD_COMMAND make -j${N}
      BUILD_IN_SOURCE 1
      )
  ExternalProject_Add(Cgl
      SOURCE_DIR ${symphony_SOURCE_DIR}/Cgl
      CONFIGURE_COMMAND ""
      BUILD_COMMAND ""
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/libCgl.a
      BUILD_IN_SOURCE 1
      )
  set(symphony_LIBRARIES
    ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Sym${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Cgl${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Clp${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}Osi${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}OsiSym${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}OsiClp${CMAKE_STATIC_LIBRARY_SUFFIX}
    ${symphony_BINARY_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}CoinUtils${CMAKE_STATIC_LIBRARY_SUFFIX}
    )
  
  ExternalProject_Add(Clp
      SOURCE_DIR ${symphony_SOURCE_DIR}/Clp
      CONFIGURE_COMMAND ""
      BUILD_COMMAND ""
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/libClp.a
      )
  ExternalProject_Add(CoinUtils
      SOURCE_DIR ${symphony_SOURCE_DIR}/CoinUtils
      CONFIGURE_COMMAND ""
      BUILD_COMMAND ""
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/libCoinUtils.a
      )
  ExternalProject_Add(Osi
      SOURCE_DIR ${symphony_SOURCE_DIR}/Osi
      CONFIGURE_COMMAND ""
      BUILD_COMMAND ""
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/libOsi.a
      )
  ExternalProject_Add(OsiSym
      SOURCE_DIR ${symphony_SOURCE_DIR}/SYMPHONY/src/OsiSym
      CONFIGURE_COMMAND ""
      BUILD_COMMAND ""
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/libOsiSym.a
      )
  ExternalProject_Add(OsiClp
      SOURCE_DIR ${symphony_SOURCE_DIR}/Clp/src/OsiClp
      CONFIGURE_COMMAND ""
      BUILD_COMMAND ""
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS ${symphony_BINARY_DIR}/lib/libOsiClp.a
      )
endif()
