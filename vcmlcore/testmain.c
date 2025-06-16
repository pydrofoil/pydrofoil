#include "pydrofoilcapi.h"
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {
    if (argc < 3) {
        // Print usage information if not enough arguments are provided
        printf("Usage: %s <riscv binary> <number of steps to run>\n", argv[0]);
        return -1; // Exit with an error code
    }
    int steps = atoi(argv[2]);
    void* cpu = pydrofoil_allocate_cpu(argv[1]);
    if (cpu == NULL) {
        printf("Failed to allocate CPU for the provided binary.\n");
        return -1; // Exit with an error code
    }
    pydrofoil_cpu_simulate(cpu, steps);
    uint64_t cycles = pydrofoil_cpu_cycles(cpu);
    printf("Simulation completed. Total cycles: %llu\n", (unsigned long long)cycles);
    printf("reset\n");
    pydrofoil_cpu_reset(cpu);
    printf("running quietly\n");
    pydrofoil_cpu_set_verbosity(cpu, 0);
    pydrofoil_cpu_simulate(cpu, steps);
    cycles = pydrofoil_cpu_cycles(cpu);
    printf("Simulation completed. Total cycles: %llu\n", (unsigned long long)cycles);
    uint64_t pc = pydrofoil_cpu_pc(cpu);
    printf("current pc: %llu\n", (unsigned long long)pc);
    if (pydrofoil_free_cpu(cpu) != 0) {
        printf("Failed to free CPU resources.\n");
        return -1; // Exit with an error code
    }
    printf("freed successfully\n");
    return 0; // Success
}
