with import <nixpkgs> {};

let coq = coq_8_13; in
let coqPackages = coqPackages_8_13; in
let ocaml = coq.ocamlPackages.ocaml; in
let ssreflect = coqPackages.mathcomp.ssreflect; in
let mathcomp-algebra = coqPackages.mathcomp.algebra; in

let mkCoqDerivation =
  import <nixpkgs/pkgs/build-support/coq> {
    inherit lib stdenv coqPackages coq fetchzip;
}; in

let deriving = with lib; mkCoqDerivation rec {
  pname = "deriving";
  domain = "github.com";
  owner = "arthuraa";
  version = "0.1.0";
  defaultVersion = "0.1.0";
  release."0.1.0".sha256 = "sha256:11crnjm8hyis1qllkks3d7r07s1rfzwvyvpijya3s6iqfh8c7xwh";
  releaseRev = (v: "v${v}");
  propagatedBuildInputs = [ coq coq.ocaml ssreflect ];
};
in

let extructures = with lib; mkCoqDerivation rec {
  pname = "extructures";
  domain = "github.com";
  owner = "arthuraa";
  version = "0.3.0";
  defaultVersion = "0.3.0";
  release."0.3.0".sha256 = "sha256:14rm0726f1732ldds495qavg26gsn30w6dfdn36xb12g5kzavp38";
  releaseRev = (v: "v${v}");
  propagatedBuildInputs = [ ssreflect deriving ];
};
in

let coq-utils = with lib; mkCoqDerivation rec {
  pname = "coq-utils";
  domain = "github.com";
  owner = "arthuraa";
  version = "20210831";
  defaultVersion = "20210831";
  release."20210831".rev = "81eaf5b6c2ed58d230de0fe3ab1fc19e0c99e297";
  release."20210831".sha256 = "sha256:1iy36dywaryryxfkb0n722cs9h8zsgksy9q64kac8idjcbjlf1ji";
  propagatedBuildInputs = [ ssreflect deriving extructures mathcomp-algebra ];
};
in

mkShell {
  packages = [ coq ocaml ssreflect deriving extructures coq-utils ];
}
