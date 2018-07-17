{ mkDerivation, base, stdenv }:
mkDerivation {
  pname = "categorial-syntax";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [ base ];
  license = stdenv.lib.licenses.bsd3;
}
