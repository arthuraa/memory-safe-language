all: Makefile.coq
	make -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: clean

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -rf Makefile.coq
