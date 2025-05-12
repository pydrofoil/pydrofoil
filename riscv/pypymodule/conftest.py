import sys
if sys.version_info.major == 2:
    from rpython.rlib.rsre import rsre_constants
    rsre_constants.V37 = False # horrible hack, circumvent weird skip
    from pypy.tool.pytest.apptest2 import AppTestModule
    APPLEVEL_FN = 'apptest_*.py'

    def pytest_addoption(parser):
        group = parser.getgroup("pydrofoil plugin options")
        group.addoption('--raise-operr', action="store_true",
                default=False, dest="raise_operr",
                help="Show the interp-level OperationError in app-level tests")
        group.addoption('--dont-regen', action="store_true",
                default=False, dest="dont_regen",
                help="Don't regenerate the RPython code from the Sail sources")

    class MyAppTestModule(AppTestModule):
        def collect(self):
            res = AppTestModule.collect(self)
            if res:
                space = res[0].w_obj.space
                space.install_mixedmodule("riscv.pypymodule")
                w_mod = space.getbuiltinmodule("_pydrofoil")
                space.setitem(res[0].w_obj.w_func_globals, space.newtext("_pydrofoil"), w_mod)
            return res

    def pytest_configure(config):
        config.addinivalue_line('python_files', APPLEVEL_FN)

    def pytest_pycollect_makemodule(path, parent):
        if path.fnmatch(APPLEVEL_FN):
            return MyAppTestModule(path, parent, rewrite_asserts=True)
