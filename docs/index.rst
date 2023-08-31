Welcome to Pydrofoil's documentation!
=====================================

.. toctree::
   :maxdepth: 2
   :caption: Contents:


Pydrofoil is an experimental emulator for RISC-V ISA based on the `Sail RISC-V
ISA model`__. It achieves fast performance by doing dynamic binary translation
(aka just-in-time compilation) from RISC-V guest instructions into host machine
instructions. It's built on top of the `RPython meta-jit compiler`__ and reuses
all its optimizations, backends, etc.

To get started, please consult :doc:`building_pydrofoil`.

.. toctree::
   :maxdepth: 1
   :hidden:

    Building Pydrofoil <building_pydrofoil>
    Using Pydrofoil <using_pydrofoil>
    Developing Pydrofoil <developing_pydrofoil>
    Background: Optimizations <background_optimizations>
    Arm <arm>
    Useful links <useful_links>
    Changelog <changelog>

.. __: https://github.com/riscv/sail-riscv
.. __: https://www3.hhu.de/stups/downloads/pdf/BoCuFiRi09_246.pdf

..
    Indices and tables
    ==================

    * :ref:`genindex`
    * :ref:`modindex`
    * :ref:`search`
