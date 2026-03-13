{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  name = "CoqMTL";

  src = pkgs.lib.cleanSource ./.;

  enableParallelBuilding = true;

  buildInputs =
  [
    pkgs.coq_8_20
    pkgs.coqPackages_8_20.equations
  ];

  buildPhase =
  ''
    patchShebangs build.sh
    ./build.sh
  '';

  installPhase =
  ''
    INSTALLPATH=$out/lib/coq/${pkgs.coq_8_20.coq-version}/user-contrib/CoqMTL

    mkdir -p $INSTALLPATH
    find . -name "*.v" -o -name "*.vo" -o -name "*.glob" | xargs cp --parents -t $INSTALLPATH/
  '';
}
