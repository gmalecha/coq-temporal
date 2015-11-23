coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: _CoqPath _CoqConfig Makefile
	@ echo "# Generating _CoqProject"
	@ echo "# including: _CoqConfig"
	@ cp _CoqConfig _CoqProject
ifneq ("$(wildcard _CoqPath)","")
	@ echo "# including: _CoqPath"
	@ cat _CoqPath >> _CoqProject
endif

_CoqPath:
	@ echo > /dev/null

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq _CoqProject

install: Makefile.coq
	$(MAKE) -f Makefile.coq install
