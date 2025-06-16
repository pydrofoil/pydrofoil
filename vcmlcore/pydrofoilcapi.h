#include <stdint.h>
#include <stddef.h>

#ifndef CFFI_DLLEXPORT
#  define CFFI_DLLEXPORT  extern
#endif

// functions that come from rpython go here
CFFI_DLLEXPORT void* pydrofoil_allocate_cpu(const char*);
CFFI_DLLEXPORT int pydrofoil_free_cpu(void*);
CFFI_DLLEXPORT int pydrofoil_cpu_simulate(void*, size_t);
CFFI_DLLEXPORT uint64_t pydrofoil_cpu_cycles(void*);
CFFI_DLLEXPORT int pydrofoil_cpu_reset(void*);

CFFI_DLLEXPORT int pydrofoil_cpu_set_verbosity(void*, int); // 0 = quiet, 1 = verbose
CFFI_DLLEXPORT uint64_t pydrofoil_cpu_pc(void*);

//CFFI_DLLEXPORT int pydrofoil_cpu_set_ram_write_callback(void*,
//                                                       int (*)(uint64_t, int size, uint64_t, void*),
//                                                       void*);
//CFFI_DLLEXPORT int pydrofoil_cpu_set_ram_read_callback(void*,
//                                                      int (*)(uint64_t, int size, uint64_t*, void*),
//                                                      void*);