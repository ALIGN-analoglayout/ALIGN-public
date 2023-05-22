# superlu v6.0.0
FetchContent_Declare(
    superlu
    GIT_REPOSITORY https://github.com/xiaoyeli/superlu.git
    GIT_TAG        v6.0.0
)
FetchContent_GetProperties(superlu)
if(NOT superlu_POPULATED)
    FetchContent_Populate(superlu)
    configure_file(
        ${CMAKE_CURRENT_SOURCE_DIR}/PlaceRouteHierFlow/thirdparty/CMakeLists.superlu
        ${superlu_SOURCE_DIR}/CMakeLists.txt
        COPYONLY)
    add_subdirectory(${superlu_SOURCE_DIR} ${superlu_BINARY_DIR})
endif()
