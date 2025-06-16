#include <stdint.h>
#include <stddef.h>

#ifndef CFFI_DLLEXPORT
#  define CFFI_DLLEXPORT  extern
#endif

// those are the functions that come from RPython
CFFI_DLLEXPORT void* pydrofoil_allocate_cpu(const char*);
CFFI_DLLEXPORT int pydrofoil_free_cpu(void*);
CFFI_DLLEXPORT int pydrofoil_simulate_cpu(void*, size_t);
CFFI_DLLEXPORT uint64_t pydrofoil_cycles_cpu(void*);
CFFI_DLLEXPORT int pydrofoil_reset_cpu(void*);

