{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell
{
  buildInputs = with pkgs;
  [
    coq_8_20
    coqPackages_8_20.coqide
    coqPackages_8_20.equations
  ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]CoqMTL\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo -e "MTL-like monadic machinery in Coq"
    echo ""
    echo -e "''${GREEN}./build.sh''${RESET}   — Regenerate the makefile, then build"
    echo -e "''${GREEN}make''${RESET}         — Build"
    echo -e "''${GREEN}make clean''${RESET}   — Clean build artifacts"
    echo -e "''${GREEN}coqide''${RESET}       — Start CoqIDE"
  '';
}
