#!/usr/bin/env python3
"""
Use the platform.uname and the versions.json from downloads.python.org to find
the name of the latests pypy2.7 for this platform. Print it out on stdout
"""

import sys
import json
from urllib import request, error
import platform
import tarfile
import io


want_nightly = "--nightly" in sys.argv

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

found_versions = []
for d in data:
    if not d["python_version"].startswith("2.7"):
        continue
    if want_nightly:
        if d["pypy_version"] != "nightly":
            continue
    else:
        if not d["stable"]:
            continue
    for f in d["files"]:
        if f["arch"] == lookup_arch(uname.machine) and f["platform"] == uname.system.lower():
            found_versions.append((d, f))
            break
if not found_versions:
    if want_nightly:
        kind = "nightly"
    else:
        kind = "stable"
    raise RuntimeError(
        f"No known {kind} PyPy2.7 build for {uname.machine}-{uname.system}"
    )
if len(found_versions) > 1:
    found_versions.sort(key=lambda x: x[0].get('date', None))

download = found_versions[-1][1]["download_url"]
request.urlretrieve(download, filename="pypy.tar.bz2")
