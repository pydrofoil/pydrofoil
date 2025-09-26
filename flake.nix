{
  description = "Pydrofoil development environment with flake-parts";

  inputs = {
    self.submodules = true;
    nixpkgs.url = "github:NixOS/nixpkgs/release-25.05";
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      perSystem =
        { config, pkgs, ... }:
        {
          devShells.default =
            let
              pypy2PackageOverrides = [
                (self: super: {
                  # Fix rply
                  appdirs = super.appdirs.overridePythonAttrs (oldAttrs: {
                    disabled = false;
                  });

                  # Fix hypothesis
                  hypothesis = self.callPackage ./nix/hypothesis.nix { };
                })
              ];

              pypy2_ =
                (pkgs.pypy2.override {
                  packageOverrides = pkgs.lib.composeManyExtensions pypy2PackageOverrides;
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

              python3_ = pkgs.python3.withPackages (
                ps: with ps; [
                  pip
                  pytest
                  setuptools
                ]
              );
            in
            pkgs.mkShell {
              shellHook = ''
                echo 1>&2 "Welcome to the development shell!"
                echo 1>&2 "PyPy location: $(which pypy)"
              '';

              buildInputs = with pkgs; [
                zlib
                gmp
                libffi
              ];

              packages = with pkgs; [
                pypy2_
                self'.packages.${system}.pydrofoil-riscv-plugin
              ];
            };

          packages = rec {
            pydrofoil-riscv = pkgs.callPackage ./package.nix {
              hypothesis = pkgs.pypy2Packages.callPackage ./nix/hypothesis.nix { };
            };
            pydrofoil-riscv-plugin = pkgs.callPackage ./nix/package-plugin.nix {
              hypothesis = pkgs.pypy2Packages.callPackage ./nix/hypothesis.nix { };
            };
            default = pydrofoil-riscv;
          };
        };
    };
}
