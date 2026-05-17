{
  description = "A basic flake with a shell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      treefmt-nix,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        treefmtEval = treefmt-nix.lib.evalModule pkgs {
          projectRootFile = "flake.nix";
          programs = {
            nixfmt.enable = true;
            rustfmt.enable = true;
          };
        };
      in
      {
        devShells.default =
          with pkgs;
          mkShell {
            nativeBuildInputs = [ pkgs.pkg-config ];
            buildInputs =
              [
                pkgs.udev
                pkgs.libevdev
              ]
              ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
                pkgs.xorg.libX11
                pkgs.xorg.libXtst
              ];

            LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath (
              [
                pkgs.udev
                pkgs.libevdev
              ]
              ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
                pkgs.xorg.libX11
                pkgs.xorg.libXtst
              ]
            );
          };

        # nix fmt
        formatter = treefmtEval.config.build.wrapper;

        # nix run .#treefmt
        packages.treefmt = treefmtEval.config.build.wrapper;

        # FIXME:
        # # nix flake check
        # checks.treefmt = treefmtEval.config.build.check;
      }
    );
}
