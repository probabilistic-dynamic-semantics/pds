let nixpkgs_source = (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-25.05.tar.gz);
in
{ pkgs ? import nixpkgs_source {
    inherit system;
  }
, system ? builtins.currentSystem
}:
let
  ghc = pkgs.haskellPackages.ghcWithPackages (ps: with ps; ([
    base
    containers
    mtl
    transformers
    hspec
  ]));
in
pkgs.stdenv.mkDerivation {
  name = "my-env-0";
  buildInputs = [
    pkgs.cabal-install
    ghc
  ];
  shellHook = ''
    export LANG=C.UTF-8
    export LC_ALL=C.UTF-8
  '';
}
