# SPDX-FileCopyrightText: 2026 Huang Rui <vowstar@gmail.com>
# SPDX-License-Identifier: MIT
{
  description = "DitDah-A1 scalar application processor development";

  inputs = {
    zaozi.url = "github:xinpian-tech/zaozi";
    nixpkgs.follows = "zaozi/nixpkgs";
    flake-utils.follows = "zaozi/flake-utils";
    riscv-dv = {
      url = "github:google/riscv-dv/b7a0b4b0b51346a3c64f159f81ea262d867c14a9";
      flake = false;
    };
    riscv-formal = {
      url = "github:YosysHQ/riscv-formal/2aa7b4934190baeb2ef62b2de414f104b489d3cc";
      flake = false;
    };
  };

  outputs = { self, flake-utils, zaozi, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import ./nix/stable-toolchain.nix {
          inherit zaozi system;
          lock = builtins.fromJSON (builtins.readFile ./flake.lock);
        }).extend (final: prev: {
          mkMavenRepository = args:
            let
              lock = builtins.fromJSON (builtins.readFile args.lockFile);
              metadata = final.lib.filterAttrs (_: artifact:
                builtins.hasAttr "maven-metadata.xml" artifact.files
              ) lock.artifacts;
              pinned = final.lib.mapAttrs (directory: _:
                let
                  prefix = "${directory}/";
                  coordinates = final.lib.filter (path:
                    final.lib.hasPrefix prefix path
                    && !(final.lib.hasInfix "/" (final.lib.removePrefix prefix path))
                  ) (builtins.attrNames lock.artifacts);
                  versions = builtins.sort final.lib.versionOlder
                    (map (final.lib.removePrefix prefix) coordinates);
                  parts = final.lib.splitString "/" directory;
                  artifactId = final.lib.last parts;
                  groupId = final.lib.concatStringsSep "." (final.lib.init parts);
                  latest = final.lib.last versions;
                  xml = final.writeText "pinned-maven-metadata.xml" ''
                    <?xml version="1.0" encoding="UTF-8"?>
                    <metadata>
                      <groupId>${groupId}</groupId><artifactId>${artifactId}</artifactId>
                      <versioning><latest>${latest}</latest><release>${latest}</release>
                        <versions>${final.lib.concatMapStrings (version: "<version>${version}</version>") versions}</versions>
                      </versioning>
                    </metadata>
                  '';
                in final.runCommand "pinned-maven-metadata-${artifactId}" { } ''
                  install -Dm444 ${xml} "$out/${directory}/maven-metadata.xml"
                  sha1sum "$out/${directory}/maven-metadata.xml" | cut -d' ' -f1 \
                    > "$out/${directory}/maven-metadata.xml.sha1"
                  chmod 444 "$out/${directory}/maven-metadata.xml.sha1"
                ''
              ) metadata;
            # Remote version indexes change even when every selected artifact is pinned.
            in prev.mkMavenRepository (pinned // args);
        });
        jar = "${pkgs.zaozi.zaozi-assembly}/share/java/elaborator.jar";
        javaLibraryPath = "${pkgs.circt-install}/lib:${pkgs.mlir-install}/lib";
        scalaArgs = pkgs.lib.escapeShellArgs [
          "--server=false"
          "--java-home" "${pkgs.jdk25}"
          "--extra-jars" jar
          "--scala-version" "3.8.4"
          "-O=-experimental"
          "--java-opt" "--enable-native-access=ALL-UNNAMED"
          "--java-opt" "--enable-preview"
          "--java-opt" "-Djava.library.path=${javaLibraryPath}"
        ];
        configure = pkgs.writeShellScriptBin "configure-ditdah-a1" ''
          set -euo pipefail
          exec ${pkgs.scala-cli}/bin/scala-cli run ${scalaArgs} \
            --main-class com.vowstar.ditdah.a1.DitDahA1Config \
            ditdah_a1/src -- "$@"
        '';
        elaborate = pkgs.writeShellScriptBin "elaborate-ditdah-a1" ''
          set -euo pipefail
          exec ${pkgs.scala-cli}/bin/scala-cli run ${scalaArgs} \
            --main-class "com.vowstar.ditdah.a1.''${DITDAH_A1_GENERATOR:-DitDahA1Module}" \
            "$DITDAH_A1_SOURCE" -- "$@"
        '';
        build = pkgs.writeShellScriptBin "build-ditdah-a1" ''
          set -euo pipefail
          exec python3 scripts/build_rtl.py "$@"
        '';
        configuration = pkgs.runCommand "ditdah-a1-configuration" {
          nativeBuildInputs = [
            pkgs.scala-cli
            (pkgs.mkMavenRepository { lockFile = "${zaozi}/mtf.lock.json"; })
          ];
          JAVA_TOOL_OPTIONS = "--enable-preview";
        } ''
          cp -R ${./ditdah_a1/src} source
          chmod -R u+w source
          cd source
          export COURSIER_CACHE="$NIX_BUILD_TOP/coursier-cache"
          mkdir -p "$out"
          scala-cli run --power --offline ${scalaArgs} \
            --main-class com.vowstar.ditdah.a1.DitDahA1Config \
            . -- --check
          scala-cli run --power --offline ${scalaArgs} \
            --main-class com.vowstar.ditdah.a1.DitDahA1Config \
            . -- --output "$out/ditdah_a1_config.json"
        '';
      in {
        packages.default = configuration;
        apps.default = {
          type = "app";
          program = "${configure}/bin/configure-ditdah-a1";
        };
        devShells.default = pkgs.mkShell {
          buildInputs = [
            configure elaborate build pkgs.scala-cli pkgs.circt-install pkgs.mlir-install
            pkgs.jextract pkgs.verilator pkgs.iverilog pkgs.yosys
            (pkgs.python313.withPackages (ps: [ ps.pytest ]))
          ];
          env = {
            ZAOZI_JAR = jar;
            CIRCT_INSTALL_PATH = pkgs.circt-install;
            MLIR_INSTALL_PATH = pkgs.mlir-install;
            JEXTRACT_INSTALL_PATH = pkgs.jextract;
            JAVA_TOOL_OPTIONS = "--enable-preview -Djextract.decls.per.header=65535";
          };
        };
      }
    );
}
