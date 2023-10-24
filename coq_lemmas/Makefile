


all:
	coq_makefile -f _CoqProject -o Makefile.coq
	cn ../page_alloc.c --only list_empty --lemmata theories/Gen_Spec.v
	make -f Makefile.coq

