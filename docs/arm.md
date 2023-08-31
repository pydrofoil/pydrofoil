# Emulating ARM

Pydrofoil can also – even more experimentally – be used to build an emulator
for ARM, based on the [ARM Sail
model](https://github.com/rems-project/sail-arm). This model is itself
automatically generated from [ASL](https://github.com/rems-project/asl_to_sail).

To build an emulator for ARM, you can run the following in your Pydrofoil
checkout:

```
make pydrofoil-arm
```

This will take quite a while the first time you run it (around two hours) but
in the end you should get a binary that you can run to emulate ARM binaries.
Right now, only loading raw binaries is supported, elf support is still
missing.

## Booting Linux

To boot Linux on the ARM emulator run the following:

```
./pydrofoil-arm -b 0x80000000,arm/bootloader.bin -b 0x81000000,arm/sail.dtb -b 0x82080000,arm/Image -C cpu.cpu0.RVBAR=0x80000000 -C cpu.has_tlb=0x0  -l 24612127 2> /dev/null
```

This will boot Linux up to the point where the `init` process is started, which
fails right now.
