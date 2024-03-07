{
  description = "functor-products";
  inputs = {
    haskellNix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskellNix/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs =
    { self
    , nixpkgs
    , flake-utils
    , haskellNix
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      projectName = "functor-products";
      ghcVersion = "ghc964";
      overlays = [
        haskellNix.overlay
      ];
      pkgs = import nixpkgs {
        inherit system overlays;
        inherit (haskellNix) config;
      };
      mkProject = v: pkgs.haskell-nix.project' {
        name = projectName;
        src = ./.;
        compiler-nix-name = v;
        shell = {
          withHoogle = false;
          tools = {
            cabal = { };
            hlint = "3.6.1";
            haskell-language-server = { };
            fourmolu = { };
          };
        };
      };
      defaultProject = mkProject ghcVersion;
    in
    rec {
      apps.format = {
        type = "app";
        program = toString (pkgs.writeShellApplication {
          name = "formatHaskell.sh";
          runtimeInputs = [ devShells.default ];
          text = ''
            # shellcheck disable=SC2046
            fourmolu --mode inplace $(git ls-files '**/**.hs')
          '';
        }) + "/bin/formatHaskell.sh";
      };
      devShells = defaultProject.flake'.devShells;
    }
    );
}
