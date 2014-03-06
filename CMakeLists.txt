set(LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  support
  )

add_clang_executable(clang-upc2c Transform.cpp)

target_link_libraries(clang-upc2c
  clangTooling clangBasic)

install(TARGETS clang-upc2c
  RUNTIME DESTINATION bin)
