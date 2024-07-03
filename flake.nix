{
  description = "functor-products";
  inputs = {
    haskellProjectFlake.url = "github:mstksg/haskell-project-flake";
    nixpkgs.follows = "haskellProjectFlake/nixpkgs";
  };
  outputs =
    { self
    , nixpkgs
    , flake-utils
    , haskellProjectFlake
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ haskellProjectFlake.overlays."${system}".default ];
      };
      project-flake = pkgs.haskell-project-flake
        {
          name = "functor-products";
          src = ./.;
          excludeCompilerMajors = [ "ghc810" "ghc90" ];
          defaultCompiler = "ghc982";
        };
    in
    rec {
      packages = project-flake.packages;
      apps = project-flake.apps;
      checks = project-flake.checks;
      devShells = project-flake.devShells;
      legacyPackages.functor-products = project-flake;
    }
    );
}
