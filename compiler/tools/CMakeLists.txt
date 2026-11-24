add_llvm_executable(tau-opt tau-opt/tau-opt.cpp)
llvm_update_compile_flags(tau-opt)
target_link_libraries(tau-opt PRIVATE
  TauDialect
  TauTransforms
  TauTarget
  MLIRFuncDialect
  MLIROptLib
)

add_llvm_executable(tauc tauc/tauc.cpp)
llvm_update_compile_flags(tauc)
target_link_libraries(tauc PRIVATE
  TauDialect
  TauTransforms
  TauTarget
  MLIRFuncDialect
  MLIRParser
  MLIRPass
)
