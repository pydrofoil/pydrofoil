#! /bin/bash

set -xeo pipefail

# scan riscv-tests/isa/* for all executables and run them with pydrofoil-riscv
# produce some kind of summary how many ran, failures, ...
echo "" > /tmp/test_results.txt
for f in $(find riscv-tests/isa -executable -not -type d |grep -v 32); do
    if ./pydrofoil-riscv $f --inst-limit 100000 >> /tmp/test_results.txt 2>&1; then
		echo $f PASSED
	else
		echo $f FAILED
	fi
done
