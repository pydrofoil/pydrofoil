Notes about how to Setup Pydrofoil on Windows 10 using WSL
=


Shell Commands
==

```bash
wsl
sudo add-apt-repository ppa:avsm/ppa
sudo apt-get update
sudo apt-get install ocaml ocaml-native-compilers camlp4-extra
sudo apt-get install make
sudo apt install z3
sudo apt install opam
sudo apt install python2
sudo apt install python3-virtualenv
opam init --disable-sandboxing
eval $(opam env --switch=default)
opam install sail
virtualenv -p python2 venv
./venv/bin/pip install rply
./venv/bin/python pypy/pytest.py pydrofoil/
```
