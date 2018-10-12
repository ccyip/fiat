all : conformance

conformance : testall.mli testall.ml conformance.ml
	ocamlfind ocamlopt -linkpkg -thread -package core -package batteries -o $@ $^
