set(headers
     Pdatatype.h
     placement.h
     FFT/fft.h)

set(sources
     placement.cpp
     FFT/fft.cpp
     FFT/fftsg2d.cpp
     FFT/fftsg.cpp)

add_library(EA_placer STATIC ${sources} ${headers})

target_link_libraries(
     EA_placer PRIVATE
     spdlog::spdlog
     Boost::boost
)
target_code_coverage(EA_placer)
