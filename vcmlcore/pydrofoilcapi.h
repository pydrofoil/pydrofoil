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

// 

CFFI_DLLEXPORT int pydrofoil_cpu_set_ram_write_callback(void*,
                                                       int (*)(uint64_t, int size, uint64_t, void*),
                                                       void*);
CFFI_DLLEXPORT int pydrofoil_cpu_set_ram_read_callback(void*,
                                                      int (*)(uint64_t, int size, uint64_t*, void*),
                                                      void*);

// NOW:
//    virtual void reset() override;
//    virtual vcml::u64 program_counter() override;
//    virtual vcml::u64 stack_pointer() override;
//

// TODOs:
// CF: implement the remaining functions
// CF: document how Chiara can build the needed .o/.so
// CF: maybe fix PyPy build tool bug
// CF: we need a way to configure the program counter after reset
// CF: start with baremetal 32-bit core
// CF: later need a way to configure things about the core
//
// Chiara: give CF github handle
// talk to Lukas, discuss list below
// add to list of functions that we will need from Pydrofoil
// maybe find out how PLIC in VMCL interfaces with the CPU
// try to see whether we can sketch some C++ code already (might be too early)

// Steps:
// - 32-bit baremetal
// - 64-bit
// - interrupts -> zephyr
// - mmu -> linux

// UNCLEAR, ask Lukas, or Chiara to think about  it:
//    virtual void end_of_elaboration() override; ???
//    virtual bool read_reg_dbg(size_t regno, void* buf, size_t len) override;
//    virtual bool write_reg_dbg(size_t regno, const void* buf,
//                               size_t len) override;
//    using vcml::component::transport; // needed to not hide vcml transport
//                                      // function by ocx transport
//    std::vector<std::shared_ptr<sc_core::sc_event>> timer_events;
//    void log_timing_info() const;
//    virtual ocx::response transport(const ocx::transaction& tx) override;
//    virtual void signal(ocx::u64 sigid, bool set) override;
//    virtual void broadcast_syscall(int callno, std::shared_ptr<void> arg,
//                                   bool async) override;
//    virtual ocx::u64 get_time_ps() override;
//    virtual void notify(ocx::u64 eventid, ocx::u64 time_ps) override;
//    virtual void cancel(ocx::u64 eventid) override;
//    virtual void hint(ocx::hint_kind kind) override;
//    virtual void handle_begin_basic_block(ocx::u64 vaddr) override;
//    virtual bool handle_breakpoint(ocx::u64 vaddr) override;
//    virtual bool handle_watchpoint(ocx::u64 vaddr, ocx::u64 size,
//                                   ocx::u64 data, bool iswr) override;
//    void inject_cpu(core* cpu);

// LATER
//    virtual void interrupt(size_t irq, bool set) override;
//    virtual bool page_size(vcml::u64& size) override;
//    virtual bool virt_to_phys(vcml::u64 vaddr, vcml::u64& paddr) override;
//
//    vcml::gpio_initiator_array<ARM_TIMER_COUNT> timer_irq_out;
//    virtual ocx::u8* get_page_ptr_r(ocx::u64 page_paddr) override;
//    virtual ocx::u8* get_page_ptr_w(ocx::u64 page_paddr) override;
//
//    virtual void protect_page(ocx::u8* page_ptr, ocx::u64 page_addr) override;
//    void memory_protector_update(vcml::u64 page_addr);
//    virtual const char* get_param(const char* name) override;
//    virtual bool disassemble(vcml::u8* ibuf, vcml::u64& addr,
//                             std::string& code) override;
//    virtual vcml::u64 core_id() override; // Make it return 0

// DEBUGGING (also used for fuzzing)
//    virtual bool insert_breakpoint(vcml::u64 addr) override;
//    virtual bool remove_breakpoint(vcml::u64 addr) override;
//    virtual bool insert_watchpoint(const vcml::range& mem,
//                                   vcml::vcml_access acs) override;
//    virtual bool remove_watchpoint(const vcml::range& mem,
//                                   vcml::vcml_access acs) override;
//
//    virtual bool start_basic_block_trace() override;
//    virtual bool stop_basic_block_trace() override;
//

