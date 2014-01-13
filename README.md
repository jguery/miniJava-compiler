The minijavac compiler.

A compilation project for Third year students of Telecom Bretagne.

ocamlbuild Main.byte (or native) to build the compiler.

ocamlbuild Main.byte -- filename (or native) to build and then execute
the compiler on the file given. Test files can be found under Test/Parsing.


Unit testing:

Install Ounit through opam:
opam install ounit.2.0.0

Then, to launch the unit tests, eg for the parsing module:
ocamlbuild -use-ocamlfind -pkgs oUnit parseTests.d.byte --
