from _pydrofoil import RISCV64 as BaseRISCV64
from typing import Callable

ALL_EVENTS = {"step", "memory_read", "memory_write"}

REGISTER_NAMES_API = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                      "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                      "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                      "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]

REGISTER_NAMES_INTERNAL = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7",
                           "x8", "x9", "x10", "x11", "x12", "x13", "x14", 
                           "x15", "x16", "x17", "x18", "x19", "x20", "x21", 
                           "x22", "x23", "x24", "x25", "x26", "x27", "x28", 
                           "x29", "x30", "x31"]

class RISCV64(BaseRISCV64):
    def __init__(self, *args, **kwargs):
        '''
        Create a new instance of a RISCV64 machine.

            Parameters:
                `elf` (str): The path to a RISC-V 64-bit ELF executable to load.
        '''
        self._callbacks = {}

    def _handle_memory_callbacks(self, read_writes):
        for rw in read_writes:
            if rw[0] == "read":
                callbacks = self._callbacks.get("memory_read", [])
                for cb in callbacks:
                    cb(self, rw[1], rw[2], rw[3])
            elif rw[0] == "write":
                callbacks = self._callbacks.get("memory_write", [])
                for cb in callbacks:
                    cb(self, rw[1], rw[2], rw[3])

    def step(self):
        '''
        Execute a single instruction at the current program counter. 
        If a `"step"` callback is registered, it is called afterwards.
        '''
        rws = super().step_monitor_mem()
        self._handle_memory_callbacks(rws)
        for cb in self._callbacks.get("step", []):
            cb(self)

    def run(self, limit: int = 0):
        '''
        Executes `limit` instructions.
        If `limit`is not set, execute until end of program.

            Parameters:
                `limit` (int): The number of instructions to execute. If `0`, execute until end of program.
        '''
        if limit == 0:
            limit = 2**63-1
        for _ in range(limit):
            rws = super().step_monitor_mem()
            self._handle_memory_callbacks(rws)

    def register_callback(self, event: str, callback: Callable):
        '''
        Registers a new callback that should be called, if the corresponding event fires.

            Parameters:
             `event` (str): The name of the event. See `ALL_EVENTS` for valid names.
             `callback` (Callable): A function that is called when the event fires.
        '''
        assert event in ALL_EVENTS
        self._callbacks.setdefault(event, []).append(callback)

    def read_register(self, name: str) -> int:
        '''
        Read the value of a single machine register.

            Parameters:
                `name` (str): The register name. Can either be the internal name (`"x1"`, `"x2"`, ...) or the API name (`"ra"`, `"sp"`, ...).

            Returns:
                `value` (int): The current value of the specified register.
        '''
        name = name.lower()

        if (name not in REGISTER_NAMES_API 
            and name not in REGISTER_NAMES_INTERNAL
            and name != "pc"):
            raise ValueError("register not found")
        
        if name in REGISTER_NAMES_API:
            name = REGISTER_NAMES_INTERNAL[REGISTER_NAMES_API.index(name)]

        if name == "x0":
            return 0

        return super().read_register(name)
    
    def write_register(self, name: str, value: int):
        '''
        Write the value of a single machine register.

            Parameters:
                `name` (str): The register name. Can either be the internal name (`"x1"`, `"x2"`, ...) or the API name (`"ra"`, `"sp"`, ...).
                `value` (int): The new value of the specified register.
        '''
        name = name.lower()

        if (name not in REGISTER_NAMES_API 
            and name not in REGISTER_NAMES_INTERNAL
            and name != "pc"):
            raise ValueError("register not found")
        
        if name in REGISTER_NAMES_API:
            name = REGISTER_NAMES_INTERNAL[REGISTER_NAMES_API.index(name)]

        if name == "x0":
            return

        return super().write_register(name, value)