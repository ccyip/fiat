all : list_people

list_people : addressbook.mli addressbook.ml list_people.ml
	ocamlfind ocamlopt -linkpkg -thread -package core -package batteries -o $@ $^
