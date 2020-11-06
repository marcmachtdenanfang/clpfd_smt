SICSTUS_ARGS=--noinfo --nologo

make:
	for n in 1 2 3 4 5 ; do \
		echo "Iteration: $$n" ; \
		sicstus $(SICSTUS_ARGS) --goal "[alpha_z3], main,halt." ; \
		echo "\n" ; \
		sicstus $(SICSTUS_ARGS) --goal "[alpha_clpfd], main,halt." ; \
		echo "\n\n" ; \
	done
	