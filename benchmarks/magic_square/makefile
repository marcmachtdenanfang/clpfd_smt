# Call with multiple threads via:
# make -jN --output-sync
# N shoud be Number of CPU cores times 1.5
SICSTUS_ARGS=--noinfo --nologo

.PHONY: all
all: j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14

j1:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_z3.pl --goal "main_single(4), main(4), main_single(4), main_single(4), main_single(4), main_single(4), halt."

j2:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_z3.pl --goal "main_single(5), main_single(5), halt."

j3:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_z3.pl --goal "main_single(5), main_single(5), halt."

j4:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_z3.pl --goal "main_single(5), main_single(5), halt."

j5:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_z3.pl --goal "main_single(6), main_single(6), halt."

j6:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_z3.pl --goal "main_single(6), main_single(6), halt."

j7:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_z3.pl --goal "main_single(6), main_single(6), halt."

	

j8:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_clpfd.pl --goal "main_single(4), main(4), main_single(4), main_single(4), main_single(4), main_single(4), halt."

j9:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_clpfd.pl --goal "main_single(5), main_single(5), halt."

j10:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_clpfd.pl --goal "main_single(5), main_single(5), halt."

j11:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_clpfd.pl --goal "main_single(5), main_single(5), halt."

j12:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_clpfd.pl --goal "main_single(6), main_single(6), halt."

j13:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_clpfd.pl --goal "main_single(6), main_single(6), halt."

j14:
	echo $@
	sicstus -f $(SICSTUS_ARGS) -l magic_square_clpfd.pl --goal "main_single(6), main_single(6), halt."

