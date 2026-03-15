{ pkgs ? import <nixpkgs> {} }:

let
  coq = import ./src/default.nix    { inherit pkgs; };
  tex = import ./Thesis/default.nix { inherit pkgs; };
in

{
  inherit coq tex;

  default = pkgs.symlinkJoin
  {
    name = "CoqMTL";

    paths =
    [
      coq
      tex
    ];
  };
}
