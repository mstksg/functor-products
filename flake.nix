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
      ghcVersions = [
        # "ghc8107"
        # "ghc902"
        "ghc928"
        "ghc948"
        "ghc965"
        "ghc982"
        "ghc9101"
      ];
      latestGhcVersion = pkgs.lib.lists.last ghcVersions;
      pkgs = import nixpkgs {
        inherit system;
        inherit (haskellNix) config;
        overlays = [ haskellNix.overlay ];
      };
      mkProject = v: pkgs.haskell-nix.project' {
        name = projectName;
        src = ./.;
        compiler-nix-name = v;
        shell = {
          withHoogle = false;
          tools = {
            cabal = { };
            hlint = { };
            haskell-language-server = { };
            fourmolu = { };
          };
        };
      };
      defaultProject = mkProject latestGhcVersion;
      allProjects = builtins.listToAttrs (builtins.map (u: { name = u; value = mkProject u; }) ghcVersions)
        // { default = defaultProject; };
      allPackages = name: packages:
        pkgs.symlinkJoin {
          inherit name;
          paths = pkgs.lib.mapAttrsToList (n: p: p) packages;
        };
    in
    rec {
      packages = builtins.mapAttrs (n: p: allPackages n p.flake'.packages) allProjects;
      apps = {
        format = {
          type = "app";
          program = toString
            (pkgs.writeShellApplication {
              name = "formatHaskell.sh";
              runtimeInputs = [ devShells.default ];
              text = ''
                # shellcheck disable=SC2046
                fourmolu --mode inplace $(git ls-files '**/**.hs')
              '';
            }) + "/bin/formatHaskell.sh";
        };
      };
      legacyPackages = pkgs // { "${projectName}" = builtins.mapAttrs (n: p: p.hsPkgs."${projectName}") allProjects; };
      devShells = builtins.mapAttrs (n: p: p.flake'.devShells.default) allProjects;
    }
    );
}
