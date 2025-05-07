import sys
if sys.version_info.major == 2:
    import __builtin__
    sys.modules['builtins'] = __builtin__ # horrible hack 1, make pytest not break?!
