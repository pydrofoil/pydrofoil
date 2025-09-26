# Borrowed from nixpkgs/nixos-22.05, with several fixes
{
  lib,
  buildPythonPackage,
  fetchFromGitHub,
  fetchPypi,
  isPy3k,
  coverage,
  pexpect,
  doCheck ? false,
  pytest,
  pytest-xdist,
  flaky,
  mock,
  sortedcontainers,
}:

let
  attrs = buildPythonPackage rec {
    pname = "attrs";
    version = "21.2.0";

    src = fetchPypi {
      inherit pname version;
      hash = "sha256-72qqw8ps2SkEzdDYP2KaFfGAU+yE5kMhBvek0Erk9fs=";
    };

    doCheck = false;
  };

  enum34 = buildPythonPackage rec {
    pname = "enum34";
    version = "1.1.10";

    src = fetchPypi {
      inherit pname version;
      sha256 = "cce6a7477ed816bd2542d03d53db9f0db935dd013b70f336a95c73979289f248";
    };

    doCheck = false;
  };
in
buildPythonPackage rec {
  # https://hypothesis.readthedocs.org/en/latest/packaging.html

  # Hypothesis has optional dependencies on the following libraries
  # pytz fake_factory django numpy pytest
  # If you need these, you can just add them to your environment.

  version = "4.39.3";
  pname = "hypothesis";

  # Use github tarballs that includes tests
  src = fetchFromGitHub {
    owner = "HypothesisWorks";
    repo = "hypothesis-python";
    rev = "hypothesis-python-${version}";
    sha256 = "1qcpcrk6892hzyjsdr581pw6i4fj9035nv89mcjrcrzcmycdlfds";
  };

  postUnpack = "sourceRoot=$sourceRoot/hypothesis-python";

  propagatedBuildInputs = [
    attrs
    coverage
    sortedcontainers
  ] ++ lib.optional (!isPy3k) enum34;

  checkInputs = [
    pytest
    pytest-xdist
    flaky
    mock
    pexpect
  ];

  inherit doCheck;

  checkPhase = ''
    rm tox.ini # This file changes how py.test runs and breaks it
    py.test tests/cover
  '';

  meta = with lib; {
    description = "A Python library for property based testing";
    homepage = "https://github.com/HypothesisWorks/hypothesis";
    license = licenses.mpl20;
  };
}
