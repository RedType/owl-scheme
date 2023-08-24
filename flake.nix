{
  description = "owl-scheme language interpreter";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    systems.url = "github:nix-systems/default";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs = inputs: inputs.flake-parts.lib.mkFlake { inherit inputs; } {
    systems = import inputs.systems;
    imports = [ inputs.treefmt-nix.flakeModule ];
    perSystem = { config, self', pkgs, lib, system, ... }: let
      cargoToml = builtins.fromTOML (builtins.readFile ./Cargo.toml);
      nonRustDeps = [ pkgs.libiconv ];
    in {
      # Package
      packages.default = pkgs.rustPlatform.buildRustPackage {
        inherit (cargoToml.package) name version;
	src = ./.;
	cargoLock.lockFile = ./Cargo.lock;
      };

      # Dev env
      devShells.default = pkgs.mkShell {
        inputsFrom = [ config.treefmt.build.devShell ];
	shellHook = ''
	  export RUST_SRC_PATH=${pkgs.rustPlatform.rustLibSrc}
	'';
	buildInputs = nonRustDeps;
	nativeBuildInputs = with pkgs; [
	  just
	  rustc
	  cargo
	  cargo-watch
	  rust-analyzer
	];
      };

      treefmt.config = {
        projectRootFile = "flake.nix";
	programs = {
	  nixpkgs-fmt.enable = true;
	  rustfmt.enable = true;
	};
      };
    };
  };
}

