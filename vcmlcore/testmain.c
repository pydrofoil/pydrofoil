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
    pydrofoil_simulate_cpu(cpu, steps);
    uint64_t cycles = pydrofoil_cycles_cpu(cpu);
    printf("Simulation completed. Total cycles: %llu\n", (unsigned long long)cycles);
    if (pydrofoil_free_cpu(cpu) != 0) {
        printf("Failed to free CPU resources.\n");
        return -1; // Exit with an error code
    }
    return 0; // Success
}
