{ mkDerivation, ansi-terminal, base, bytestring, case-insensitive
, containers, contravariant, criterion, cryptonite, deepseq
, directory, doctest, exceptions, filepath, formatting, haskeline
, http-client, http-client-tls, insert-ordered-containers
, lens-family-core, megaparsec, memory, mtl, optparse-applicative
, parsers, prettyprinter, prettyprinter-ansi-terminal, repline
, scientific, stdenv, tasty, tasty-hunit, text, transformers
, unordered-containers, vector
}:
mkDerivation {
  pname = "dhall";
  version = "1.14.0";
  src = ./..;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    ansi-terminal base bytestring case-insensitive containers
    contravariant cryptonite directory exceptions filepath formatting
    http-client http-client-tls insert-ordered-containers
    lens-family-core megaparsec memory parsers prettyprinter
    prettyprinter-ansi-terminal scientific text transformers
    unordered-containers vector
  ];
  executableHaskellDepends = [
    ansi-terminal base haskeline megaparsec mtl optparse-applicative
    prettyprinter prettyprinter-ansi-terminal repline text
  ];
  testHaskellDepends = [
    base deepseq doctest insert-ordered-containers prettyprinter tasty
    tasty-hunit text vector
  ];
  benchmarkHaskellDepends = [
    base containers criterion directory text
  ];
  description = "A configuration language guaranteed to terminate";
  license = stdenv.lib.licenses.bsd3;
}
