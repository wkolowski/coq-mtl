{ pkgs ? import <nixpkgs> {} }:

let
  coq = import ./src/shell.nix    { inherit pkgs; };
  tex = import ./Thesis/shell.nix { inherit pkgs; };
in

{
  inherit coq tex;

  default = pkgs.mkShell
  {
    inputsFrom =
    [
      coq
      tex
    ];
  };
}
