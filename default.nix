{ pkgs ? import <nixpkgs> {} }:

let
  coq = import ./src/default.nix { inherit pkgs; };
in

{
  inherit coq;

  default = coq;
}
