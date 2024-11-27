# shell.nix
let
  pkgs = import <nixos-unstable> {};

  tex = (pkgs.texlive.combine {
    inherit (pkgs.texlive) scheme-minimal mathtools
    latexmk xetex etoolbox unicode-math dvisvgm pdfcrop;
  });
  python = pkgs.python3.override {
    self = python;
    packageOverrides = pyfinal: pyprev: {
      leanblueprint = pyfinal.callPackage ./leanblueprint.nix {};
    };
  };

in pkgs.mkShell {
  packages = [
    tex
    pkgs.graphviz
    pkgs.ghostscript
    pkgs.pdf2svg
    (python.withPackages (python-pkgs: with python-pkgs; [
      # select Python packages- here
      pygraphviz
      leanblueprint
    ]))
  ];
}
