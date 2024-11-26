# shell.nix
let
  pkgs = import <nixos-unstable> {};

  python = pkgs.python3.override {
    self = python;
    packageOverrides = pyfinal: pyprev: {
      leanblueprint = pyfinal.callPackage ./leanblueprint.nix {};
    };
  };

in pkgs.mkShell {
  packages = [
    (python.withPackages (python-pkgs: with python-pkgs; [
      # select Python packages- here
      pygraphviz
      leanblueprint
    ]))
  ];
}
