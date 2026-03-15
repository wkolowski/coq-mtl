{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  name = "CoqMTL";

  src = pkgs.lib.cleanSource ./.;

  enableParallelBuilding = true;

  buildInputs = with pkgs;
  [
    graphviz
    (python3.withPackages (ps: [ ps.pygments ]))
    (texlive.combine
    {
      inherit (pkgs.texlive)
      scheme-basic
      latexmk
      # For slides.
      beamer
      # Polish support.
      babel-polish
      lh              # OT4 font encoding for Polish
      cm-super
      polski
      # minted and its dependencies
      minted
      fvextra
      upquote
      catchfile
      xstring
      framed
      newfloat
      # Common thesis packages
      amsmath
      amsfonts
      amscls
      geometry
      graphics
      hyperref
      titling
      lineno
      ;
    })
  ];

  buildPhase =
  ''
    patchShebangs ./build.sh
    ./build.sh
  '';

  installPhase =
  ''
    INSTALLPATH=$out/share/doc/coq-mtl/

    mkdir -p $INSTALLPATH
    cp Thesis.pdf $INSTALLPATH/
    cp Defense/Slides.pdf $INSTALLPATH/
  '';
}
