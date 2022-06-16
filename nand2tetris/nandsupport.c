#include "sail.h"
#include "rts.h"
#include "elf.h"

uint16_t *nand_mem;
uint16_t *nand_rom;

unit my_write_mem(uint16_t addr, uint16_t value) {
    nand_mem[addr] = value;
    return UNIT;
}

uint16_t my_read_rom(uint16_t addr) {
    return nand_rom[addr];
}

uint16_t my_read_mem(uint16_t addr) {
    return nand_mem[addr];
}

int model_main(int argc, char *argv[]);

unit my_print_debug(uint64_t cycle_count, uint64_t PC, uint64_t A, uint64_t D) {
  printf("PC: %ld, A: %ld, D: %ld, cycle count: %ld\n", PC, A, D, cycle_count);
  return UNIT;
}

void model_init(void);
unit zmain(uint64_t);
void model_fini(void);
void model_pre_exit();

int main(int argc, char* argv[]) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s <rom binary>\n", argv[0]);
        return -1;
    }
    FILE *fp = fopen(argv[1], "r");

    if (!fp) {
        fprintf(stderr, "rom %s could not be loaded\n", argv[1]);
        return -2;
    }
    nand_rom = calloc(65536, 1);
    nand_mem = calloc(65536, 1);

    uint8_t *nand_rom_as_bytes = (uint8_t *)nand_rom;

    uint64_t byte;
    uint16_t addr = 0;
    while ((byte = (uint64_t)fgetc(fp)) != EOF) {
        nand_rom_as_bytes[addr++] = (uint8_t)byte;
        if (addr >= 65536) {
            fprintf(stderr, "rom too large!\n");
            return -3;
        }
    }
    model_init();
    zmain(10);
    model_fini();
    model_pre_exit();
    return 0;
}
