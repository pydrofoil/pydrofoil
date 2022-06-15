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

    uint8_t byte;
    uint16_t addr = 0;
    while ((byte = (uint8_t)fgetc(fp)) != EOF) {
        nand_rom[addr++] = byte;
    }
}
