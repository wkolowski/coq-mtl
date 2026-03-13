{ pkgs ? import <nixpkgs> {} }:

let
  coq = import ./src/shell.nix { inherit pkgs; };
in

{
  inherit coq;

  default = coq;
}