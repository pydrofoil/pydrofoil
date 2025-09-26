{
  lib,
  stdenv,
  replaceVars,
  breakpointHook,
  hypothesis ? null,
  pkg-config,
  python3,
  pypy2,
  z3,
  sail-riscv,
  zlib,
  gmp,
  libffi,
  ncurses,
  bzip2,
  openssl,
  sqlite,
  tclPackages,
  tcl,
  tk,
  gdbm,
  xz,
  expat,
  python-setup-hook,
  makeWrapper,
  patchelf,
}:
let
  pypy2PackageOverrides = [
    (self: super: {
      # Fix rply
      appdirs = super.appdirs.overridePythonAttrs (oldAttrs: {
        disabled = false;
      });

      # Fix hypothesis
      inherit hypothesis;
    })
  ];

  pypy2_ =
    (pypy2.override {
      packageOverrides = lib.composeManyExtensions pypy2PackageOverrides;
    }).withPackages
      (
        ps: with ps; [
          rply
          hypothesis
          junit-xml
          coverage
          typing
        ]
      );

  python3_ = python3.withPackages (
    ps: with ps; [
      pip
      pytest
      setuptools
    ]
  );

  pythonVersion = "3.11";
  libPrefix = "pypy${pythonVersion}";
  executable = "pypy${lib.versions.majorMinor pythonVersion}";
  sitePackages = "lib/${libPrefix}/site-packages";
in
stdenv.mkDerivation (finalAttrs: {
  pname = "pydrofoil-riscv";
  version = "0.0.1-alpha0";

  # NOTE: requires Nix 2.28 or later
  # otherwise `inputs.self.submodules` will fail in flake.nix
  # src = ./..;
  src = lib.fileset.toSource {
    root = ./..;
    fileset = lib.fileset.unions [
      ../Makefile
      ../nix
      ../pydrofoil
      ../riscv
      ../pypy2
    ];
  };

  # fix compiler error in curses cffi module, where char* != const char*
  NIX_CFLAGS_COMPILE =
    if stdenv.cc.isClang then "-Wno-error=incompatible-function-pointer-types" else null;
  C_INCLUDE_PATH = lib.makeSearchPathOutput "dev" "include" finalAttrs.buildInputs;
  LIBRARY_PATH = lib.makeLibraryPath finalAttrs.buildInputs;
  LD_LIBRARY_PATH = lib.makeLibraryPath (
    builtins.filter (x: x.outPath != stdenv.cc.libc.outPath or "") finalAttrs.buildInputs
  );

  patchFlags = [
    "-p1"
    "--directory"
    "pypy2"
  ];
  patches = [
    ./dont_fetch_vendored_deps.patch

    (replaceVars ./tk_tcl_paths.patch {
      inherit tk tcl;
      tk_dev = tk.dev;
      tcl_dev = tcl;
      tk_libprefix = tk.libPrefix;
      tcl_libprefix = tcl.libPrefix;
    })

    # Python ctypes.util uses three different strategies to find a library (on Linux):
    # 1. /sbin/ldconfig
    # 2. cc -Wl,-t -l"$libname"; objdump -p
    # 3. ld -t (where it attaches the values in $LD_LIBRARY_PATH as -L arguments)
    # The first is disabled in Nix (and wouldn't work in the build sandbox or on NixOS anyway), and
    # the third was only introduced in Python 3.6 (see bugs.python.org/issue9998), so is not
    # available when buliding PyPy (which is built using Python/PyPy 2.7).
    # The second requires SONAME to be set for the dynamic library for the second part not to fail.
    # As libsqlite3 stopped shipping with SONAME after the switch to autosetup (>= 3.50 in Nixpkgs;
    # see https://www.sqlite.org/src/forumpost/5a3b44f510df8ded). This makes the Python CFFI module
    # unable to find the SQLite library.
    # To circumvent these issues, we hardcode the path during build.
    # For more information, see https://github.com/NixOS/nixpkgs/issues/419942.
    (replaceVars ./sqlite_paths.patch {
      inherit (sqlite) out dev;
      libsqlite = "${sqlite.out}/lib/libsqlite3${stdenv.hostPlatform.extensions.sharedLibrary}";
    })
  ];

  postPatch = ''
    substituteInPlace pypy2/lib_pypy/pypy_tools/build_cffi_imports.py \
      --replace-fail "multiprocessing.cpu_count()" "$NIX_BUILD_CORES"

    substituteInPlace pypy2/lib-python/3/tkinter/tix.py\
      --replace-fail "os.environ.get('TIX_LIBRARY')" "os.environ.get('TIX_LIBRARY') or '${tclPackages.tix}/lib'"
  '';

  nativeBuildInputs = [
    breakpointHook
    pkg-config
    # python3_
    z3
    sail-riscv
    patchelf
  ];

  buildInputs = [
    pypy2_
    bzip2
    openssl
    zlib
    gmp
    libffi
    ncurses
    sqlite
    tk
    tcl
    gdbm
    xz
    expat
    stdenv.cc.libc
    # boehmgc
    makeWrapper
  ];

  # Remove bootstrap python from closure
  dontPatchShebangs = true;
  disallowedReferences = [ pypy2 ];

  buildPhase = ''
    runHook preBuild

    make -C pydrofoil/softfloat/SoftFloat-3e/build/Linux-RISCV-GCC/ softfloat.o
    pkg-config libffi

    cd pypy2/pypy/goal
    PYTHONPATH=../../..:${pypy2_}/lib/pypy2.7/site-packages ${pypy2_}/bin/pypy ../../rpython/bin/rpython \
      --batch \
      --make-jobs="$NIX_BUILD_CORES" \
      -Ojit \
      targetpypystandalone.py \
      --ext=riscv.pypymodule
 	  mv pypy3.11-c pypy-c-pydrofoil-riscv
 	  ./pypy-c-pydrofoil-riscv ../../lib_pypy/pypy_tools/build_cffi_imports.py
 	  cd -
 	  ln -s pypy2/pypy/goal/pypy-c-pydrofoil-riscv pypy-c-pydrofoil-riscv

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    cd pypy2/pypy/goal
    mkdir $out
    PYTHONPATH=${pypy2_}/lib/pypy2.7/site-packages ${pypy2_}/bin/pypy \
      ../tool/release/package.py \
      --override_pypy_c=pypy-c-pydrofoil-riscv \
      --make-portable \
      --archive-name=pypy-pydrofoil-scripting-experimental \
      --targetdir=$out
    cd $out
    tar -xjf pypy-pydrofoil-scripting-experimental.tar.bz2 --strip-components=1
    rm $out/pypy-pydrofoil-scripting-experimental.tar.bz2

    # FIXME: package.py omits bzip2/zlib RPATHs
    cp ${bzip2.out}/lib/libbz2.so.1 ${zlib.out}/lib/libz.so.1 $out/lib
    printf "libbz2.so.1\nlibz.so.1\n" >> $out/lib/PYPY_PORTABLE_DEPS.txt
    patchelf --set-rpath $out/lib $out/bin/lib${libPrefix}-c.so

    ln -s $out/bin/lib${libPrefix}-c.so $out/bin/libpypy3-c.so

    runHook postInstall
  '';

  preFixup = ''
    pushd /
    $out/bin/${executable} -c "from test import support"
    popd
  '';

  doInstallCheck = true;
  installCheckPhase =
    let
      modules = [
        "curses"
        "sqlite3"
        "tkinter"
        "lzma"
        "_pydrofoil"
      ];
      imports = lib.concatMapStringsSep "; " (x: "import ${x}") modules;
    in
    ''
      echo "Testing whether we can import modules"
      $out/bin/${executable} -c '${imports}'
    '';
    enableParallelBuilding = true; # almost no parallelization without STM
})
