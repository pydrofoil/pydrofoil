# Emulating CHERIoT

Pydrofoil can also be used to build an emulator
for CHERIoT, based on the [CHERIoT Sail
model](https://github.com/CHERIoT-Platform/cheriot-sail) (which is iteself an
extension of the RISC-V Sail model).

To build an emulator for CHERIoT, you can run the following in your Pydrofoil
checkout:

```
make pydrofoil-cheriot
```

The resulting binary can run both the example applications from the
[cheriot-rtos repo](https://github.com/CHERIoT-Platform/cheriot-rtos):

```
./pydrofoil-cheriot cheriot/input/hello_world
```

As well as the tests:

```
./pydrofoil-cheriot cheriot/input/test-suite
```

Also, the allocator benchmark:

```
./pydrofoil-cheriot cheriot/input/allocator-benchmark
```

Performance seems to be roughly in the 5-10 MIPS range, which is an order of
magnitude faster than the default Sail-based emulator.
