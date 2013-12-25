The minijavac compiler.

A compilation project for Thrid year students of Telecom Bretagne.

ocamlbuild Main.byte (or native) to build the compiler.

ocamlbuild Main.byte -- filename (or native) to build and then execute
the compiler on the file given.

Unit testing:

Install Ounit through opam:
opam install ounit.2.0.0

Then, to launch the unit tests:
ocamlbuild -use-ocamlfind -pkgs oUnit parseTests.byte --
