# superlu v5.2.2
FetchContent_Declare(
    superlu
    GIT_REPOSITORY https://github.com/xiaoyeli/superlu.git
    GIT_TAG        v5.2.2
    INSTALL_COMMAND ""
    TEST_COMMAND ""
)
FetchContent_MakeAvailable(superlu)
