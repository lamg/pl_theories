{
  description = "Programming Language Theories — Lean development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;

      # The Lean version is derived from lean-toolchain (e.g.
      # "leanprover/lean4:v4.35.0" -> "4.35.0"), so bumping that file is
      # enough — apart from refreshing the hashes below with:
      #   nix store prefetch-file \
      #     https://github.com/leanprover/lean4/releases/download/v<version>/lean-<version>-linux.tar.zst
      #   nix store prefetch-file \
      #     https://github.com/leanprover/lean4/releases/download/v<version>/lean-<version>-linux_aarch64.tar.zst
      toolchain = nixpkgs.lib.trim (builtins.readFile ./lean-toolchain);
      version = nixpkgs.lib.removePrefix "leanprover/lean4:v" toolchain;

      assets = {
        x86_64-linux = {
          file = "lean-${version}-linux.tar.zst";
          hash = "sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=";
        };
        aarch64-linux = {
          file = "lean-${version}-linux_aarch64.tar.zst";
          hash = "sha256-yPD4o5IOg5cYsTQ+Z4H9gKPpsQJPvNcHjrMPVOgGsCg=";
        };
      };
    in
    {
      packages = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
          asset = assets.${system} or (throw "lean-toolchain: unsupported system ${system}");

          # nixpkgs ships a different Lean version, and elan-downloaded
          # binaries do not run on NixOS, so package the official release
          # tarball matching lean-toolchain and patch it for Nix.
          lean = pkgs.stdenv.mkDerivation {
            pname = "lean-toolchain";
            inherit version;

            src = pkgs.fetchurl {
              url = "https://github.com/leanprover/lean4/releases/download/v${version}/${asset.file}";
              inherit (asset) hash;
            };

            nativeBuildInputs = [
              pkgs.autoPatchelfHook
              pkgs.zstd
            ];
            buildInputs = [ pkgs.stdenv.cc.cc.lib ];

            unpackPhase = ''
              runHook preUnpack
              tar --zstd -xf $src
              runHook postUnpack
            '';
            sourceRoot = "lean-${version}-linux";

            installPhase = ''
              runHook preInstall
              mkdir -p $out
              cp -r bin lib share include src $out/
              runHook postInstall
            '';

            # Bundled clang/lld helpers carry no Nix-incompatible deps
            # beyond libc; missing bundled libs are found via $ORIGIN.
            autoPatchelfIgnoreMissingDeps = [ "*" ];

            meta = {
              description = "Lean ${version} toolchain (from lean-toolchain)";
              homepage = "https://lean-lang.org";
              license = pkgs.lib.licenses.asl20;
              mainProgram = "lean";
            };
          };
        in
        {
          inherit lean;
          default = lean;
        }
      );

      devShells = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          default = pkgs.mkShell {
            name = "pl-theories";

            packages = [
              self.packages.${system}.lean
              pkgs.git # Lake fetches Verso and its dependencies with git
              pkgs.python3 # README preview: python3 -m http.server
            ];

            shellHook = ''
              export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
              echo "pl_theories dev shell — $(lean --version)"
            '';
          };
        }
      );
    };
}
