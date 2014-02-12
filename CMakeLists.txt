set(LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  support
  )

add_clang_executable(upc2c Transform.cpp)

target_link_libraries(upc2c
  clangTooling clangBasic)

install(TARGETS upc2c
  RUNTIME DESTINATION bin)
