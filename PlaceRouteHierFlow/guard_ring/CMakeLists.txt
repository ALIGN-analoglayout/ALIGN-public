set(headers
     Gdatatype.h
     GuardRing.h
     GuardRingIfc.h
)

set(sources
     GuardRing.cpp
     GuardRingIfc.cpp
)

add_library(guard_ring STATIC ${sources} ${headers})

target_link_libraries(
     guard_ring PRIVATE
     spdlog::spdlog
)
target_code_coverage(guard_ring)