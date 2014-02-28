The minijavac compiler.

A compilation project for Third year students of Telecom Bretagne.

ocamlbuild Main.byte (or native) to build the compiler.

ocamlbuild Main.byte -- filename (or native) to build and then execute
the compiler on the file given. Test files can be found under Test/Parsing.


Unit testing:

Install Ounit through opam:
opam install ounit.2.0.0

I only did the unit tests for the parsing module and the typing module:
ocamlbuild -use-ocamlfind -pkgs oUnit parseTests.d.byte --
ocamlbuild -use-ocamlfind -pkgs oUnit typeTests.d.byte --
ocamlbuild -use-ocamlfind -pkgs oUnit classEnvTests.d.byte --

The evaluation is complete, and even takes account of static attributes 
and methods.

A miniJava file can be evaluated using the following command:
ocamlbuild Main.d.byte -- mjava_file
or using the verbose mode to have information about parsing/typing:
ocamlbuild Main.d.byte -- -v mjava_file