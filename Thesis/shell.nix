{ pkgs ? import <nixpkgs> {} }:

let
  build = import ./default.nix { inherit pkgs; };
in

pkgs.mkShell
{
  name = "CoqMTL";

  inputsFrom = [ build ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]Axi\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo "Axi theory development shell"
    echo ""
    echo -e "''${GREEN}./build.sh''${RESET}   — Build PDF"
    echo -e "''${GREEN}latexmk''${RESET}      — Build PDF manually"
    echo -e "''${GREEN}latexmk -C''${RESET}   — Clean build artifacts"
  '';
}
