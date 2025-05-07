import sys
import os

PYTHON2 = sys.version_info.major == 2

currdir = os.path.dirname(__file__)

def pytest_ignore_collect(path, config):
    # skip the subdirectories of the current directory on python2
    if PYTHON2 and str(path).startswith(currdir):
        return True
