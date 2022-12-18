#!/usr/bin/env python3
"""
Use the platform.uname and the versions.json from downloads.python.org to find
the name of the latests pypy2.7 for this platform. Print it out on stdout
"""

import json
from urllib import request, error
import platform
import tarfile
import io

response = request.urlopen('https://downloads.python.org/pypy/versions.json')
if not (response.getcode(), 200):
    raise RuntimeError("could not download versions.json from https://downloads/python.org/pypy/")
data = json.loads(response.read())
download = ''
# Find the one that has python_version 2.7, "stable", and platform matches
uname = platform.uname()
def lookup_arch(machine):
    if machine == "x86_64":
        return "x64"
    else:
        return machine

for d in data:
    if d['stable'] is True and "2.7" in d["python_version"]:
        for f in d["files"]:
            if f["arch"] == lookup_arch(uname.machine) and f["platform"] == uname.system.lower():
                download = f["download_url"]
                break
        else:
            raise RuntimeError(
                f"No known stable PyPy2.7 build for {uname.machine}-{uname.system}"
            )
        break
else:
    raise RuntimeError(f"No known stable PyPy2.7 build???")
print(download)
