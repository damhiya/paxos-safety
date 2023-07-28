{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages."${system}";
        mkBuildInputs = coq:
          with (pkgs.mkCoqPackages coq); [
            coq
          ];
      in {
        devShell = pkgs.mkShell {
          nativeBuildInputs = [ ];
          buildInputs = mkBuildInputs pkgs.coq;
        };
      });

}

