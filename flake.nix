{
  description = "Finite probability theory in Coq";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    extructures-instances.url = "github:arthuraa/extructures-instances";
    extructures-instances.inputs.nixpkgs.follows = "nixpkgs";
    finmap.url = "github:math-comp/finmap";
    finmap.flake = false;
  };

  outputs = inputs@{ self, flake-parts, finmap, extructures-instances, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import a flake module
        # 1. Add foo to inputs
        # 2. Add foo as a parameter to the outputs function
        # 3. Add here: foo.flakeModule

      ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        # Per-system attributes can be defined here. The self' and inputs'
        # module parameters provide easy access to attributes of the same
        # system.

        _module.args.pkgs = import self.inputs.nixpkgs {
          inherit system;
          overlays = [
            extructures-instances.overlays.default
            self.overlays.default
          ];
          config = { };
        };

        # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
        packages.default = pkgs.coqPackages.mkCoqDerivation {
          pname = "finprob";
          defaultVersion = "dev";
          release.dev.src = ./.;
          propagatedBuildInputs = with pkgs.coqPackages; [
            deriving
            extructures
            mathcomp.algebra
            mathcomp-finmap
            pkgs.coqPackages.extructures-instances
          ];
        };
      };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

        overlays.default = final: prev: {
          coqPackages = prev.coqPackages.overrideScope (final: prev: {
            mathcomp-finmap = prev.lib.overrideCoqDerivation {
              defaultVersion = "dev";
              release.dev.src = finmap;
            } prev.mathcomp-finmap;
          });
        };

      };
    };
}
