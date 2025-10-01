{
  lib,
  stdenv,
  hypothesis ? null,
  pkg-config,
  python3,
  pypy2,
  z3,
  sail-riscv,
  zlib,
  gmp,
  libffi,
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
in
stdenv.mkDerivation (finalAttrs: {
  pname = "pydrofoil-riscv";
  version = "0.0.1-alpha0";

  # NOTE: requires Nix 2.28 or later
  # otherwise `inputs.self.submodules` will fail in flake.nix
  src = ./.;

  nativeBuildInputs = [
    pkg-config
    pypy2_
    python3_
    z3
    sail-riscv
  ];

  buildInputs = [
    zlib
    gmp
    libffi
  ];

  buildPhase = ''
    runHook preBuild

    make -C pydrofoil/softfloat/SoftFloat-3e/build/Linux-RISCV-GCC/ softfloat.o
    pkg-config libffi

    # export PYTHONPATH=$PWD:${pypy2_}/lib/pypy2.7/site-packages # not sure if this is still needed
    PYTHONPATH=. ${pypy2_}/bin/pypy pypy2/rpython/bin/rpython -Ojit --output=pydrofoil-riscv riscv/targetriscv.py

    runHook postBuild
  '';

  doCheck = true;

  checkPhase = ''
    ${pypy2_}/bin/pypy pypy2/pytest.py -v pydrofoil/ riscv/
  '';

  installPhase = ''
    runHook preInstall

    mkdir -p $out/bin
    install -Dm755 pydrofoil-riscv $out/bin

    runHook postInstall
  '';
})
