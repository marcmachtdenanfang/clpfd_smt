SICSTUS_BIN_PATH:=""
SICSTUS_INCLUDE_PATH:="/path/to/sicstus/include"
Z3_INCLUDE_PATH:="/path/to/Z3.h"
Z3_LIB_PATH:="" #"/path/to/libz3.so"

install:
	$(SICSTUS_BIN_PATH)splfr clpfd_z3.pl clpfd_z3.c --cflag=-lz3  --cflag=-I$(Z3_INCLUDE_PATH) -lz3 -L$(Z3_LIB_PATH)
	rm -f clpfd_z3_glue.c clpfd_z3_glue.h clpfd_z3_glue.o clpfd_z3.o

debug:
	$(SICSTUS_BIN_PATH)sicstus -f --noinfo --nologo --goal "use_module(library(fligen)),splfr_prepare_foreign_resource('clpfd_z3','clpfd_z3.pl','clpfd_z3_glue.c','clpfd_z3_glue.h', [])."
	gcc -I$(SICSTUS_INCLUDE_PATH) -I"." -g -O2 -pipe -D_REENTRANT -D_GNU_SOURCE -D_FILE_OFFSET_BITS=64 -fPIC -DSPDLL  -DSP_RESNAME=clpfd_0x5Fz3 -DSICSTUS_TARGET_VERSION=40600 -c clpfd_z3.c -o clpfd_z3.o -lz3 -I$(Z3_INCLUDE_PATH)
	gcc -I$(SICSTUS_INCLUDE_PATH) -I"." -g -O2 -pipe -D_REENTRANT -D_GNU_SOURCE -D_FILE_OFFSET_BITS=64 -fPIC -DSPDLL  -DSP_RESNAME=clpfd_0x5Fz3 -DSICSTUS_TARGET_VERSION=40600 -c clpfd_z3_glue.c -o clpfd_z3_glue.o
	gcc -shared -Wl,--version-script=clpfd_z3_glue.mapfile clpfd_z3.o clpfd_z3_glue.o -o clpfd_z3.so -lz3 -L$(Z3_LIB_PATH) -ldl -lm -lpthread -lrt

clean:
	rm -f clpfd_z3.so

# splfr clpfd_z3.pl clpfd_z3.c --cflag=-lz3  --cflag=-I"/home/marc/anaconda3/include" --verbose --keep
# splfr clpfd_z3.pl clpfd_z3.c --cflag=-lz3  --cflag=-I"/home/marc/anaconda3/include" --verbose --keep
# -lz3 -L. -Wl,-rpath,/usr/local/lib
# -L. checks for libraries in the current folder
# -Wl,-rpath,<Path> does not work, because --cflag=<option> assumes that comma is a separator for multiple options. Flag will be interpreted wrongly.
# -Wl sends following options directly to linker
# -rpath specifies libraries to be searched at runtime, so that "ldd clpfd_z3.so" will show the dependency on libz3.so

