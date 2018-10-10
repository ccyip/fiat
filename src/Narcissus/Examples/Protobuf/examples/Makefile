all : list_people add_person

list_people : addressbook.mli addressbook.ml list_people.ml
	ocamlfind ocamlopt -linkpkg -thread -package core -package batteries -o $@ $^

add_person : addressbook.mli addressbook.ml add_person.ml
	ocamlfind ocamlopt -linkpkg -thread -package core -package batteries -o $@ $^
