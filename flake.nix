{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = {nixpkgs, ...}: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
    typeshedSrc = pkgs.fetchFromGitHub {
      owner = "python";
      repo = "typeshed";
      rev = "1b267b25f2c726291e4e6627b7567f2c8dc04b60";
      sha256 = "sha256-SQJypewNYLfNSIc+Myd9l+nypdMdOx+Fyymmg/YpFW4=";
    };
  in {
    packages.${system}.default = pkgs.rustPlatform.buildRustPackage {
      pname = "zuban";
      version = "0.0.21";
      src = pkgs.lib.cleanSourceWith {
        src = ./.;
        filter = name: type: !(pkgs.lib.hasSuffix ".git" name);
      };

      preBuild = ''
        export TYPESHED_HOME=${typeshedSrc}
        cp -r $TYPESHED_HOME typeshed
      '';
      cargoLock = {
        lockFile = ./Cargo.lock;
        outputHashes = {
          "rust-ini-0.21.1" = "sha256-0NRWwxSdMjnu/T2JW1BNUYNLJdtqk5J5WYs7VXbltRs=";
        };
      };
      doCheck = false;

      postInstall = ''
        mkdir -p $out/${pkgs.python3.sitePackages}/zuban
        cp -r ${typeshedSrc} $out/${pkgs.python3.sitePackages}/zuban/typeshed
      '';
      meta = with pkgs.lib; {
        description = "zuban";
        license = licenses.agpl3Plus;
        maintainers = [];
        platforms = platforms.linux;
      };
    };
  };
}
