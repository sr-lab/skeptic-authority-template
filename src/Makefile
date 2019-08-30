# Override shell executable from sh to bash.
SHELL:=/bin/bash

main:
	# Compile and make Coq project.
	( echo "-R . authy" ; find . -name "*.v" -print ) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile_Coq
	make -f Makefile_Coq

clean:
	rm -f *.hi *.o .*.aux *~ *.vo *.glob *.so *_stub.h

authority:
	make
	ocamlbuild authority.native -use-ocamlfind -package io-system
	./authority.native
