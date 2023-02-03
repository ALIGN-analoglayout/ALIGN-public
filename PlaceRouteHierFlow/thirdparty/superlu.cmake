# superlu v5.2.2
FetchContent_Declare(
    superlu
    GIT_REPOSITORY https://github.com/srini229/superlu.git
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
