import os
from rpython.rtyper.lltypesystem import rffi
from rpython.translator.tool.cbuild import ExternalCompilationInfo
 
info = ExternalCompilationInfo(
    includes=["pydrofoil_softfloat.h"],
    include_dirs=[os.path.dirname(os.path.realpath(__file__))],
    libraries=["pydrofoil_softfloat"],
    library_dirs=[os.path.dirname(os.path.realpath(__file__))],
)

f32add = rffi.llexternal("f32add", [rffi.UINT_FAST8_T, rffi.ULONG, rffi.ULONG], rffi.ULONG, compilation_info=info)

