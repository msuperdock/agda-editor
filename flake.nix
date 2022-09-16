{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  inputs.agda-unused.url = "hg+file:///data/code/agda-unused";

  outputs = { self, agda-unused, nixpkgs }:

  let

    packages = nixpkgs.legacyPackages.x86_64-linux;

  in

  {
    devShell.x86_64-linux = packages.mkShell {
      buildInputs = [
        agda-unused.defaultPackage.x86_64-linux
        packages.haskellPackages.Agda
      ];
    };
  };
}

