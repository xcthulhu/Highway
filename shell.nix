{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    hostname
    isabelle
    perl
    (texlive.combine { inherit (texlive) scheme-basic ulem; })

    # keep this line if you use bash
    bashInteractive
  ];
}
