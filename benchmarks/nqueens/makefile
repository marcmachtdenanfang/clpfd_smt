# https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus/N-Queens.html

# Call with
# time make -j X FIRST=M LAST=N
# X is number of CPU cores times 1.5, i.e. 8-core CPU: X = 12
# X can be lower than that.
# M and N make the range for which you want the program to be executed, i.e. M=4, N=6 equals running 4-queens, 5-queens, and 6-queens (in parallel)



Targets = f1 f2
nqueens_N := 109
sicstus_args := -f --noinfo --nologo

#make:
#	sicstus $(sicstus_args) --goal "[nqueens_z3], set_z3_logic(qffd), main($(nqueens_N)),halt."
#	@echo ""
#	sicstus $(sicstus_args) --goal "[nqueens_clpfd], main($(nqueens_N), Rows),halt."


# from https://stackoverflow.com/a/12110773/13467614
FIRST := 4
LAST := 20
NUMBERS := $(shell seq ${FIRST} ${LAST})
JOBS := $(addprefix job,${NUMBERS})
.PHONY: all ${JOBS}
all: ${JOBS} ; echo "$@ success"
${JOBS}: job%: ; sicstus $(sicstus_args) --goal "[nqueens_z3], main($*),halt." 
#; sicstus $(sicstus_args) --goal "[nqueens_clpfd], main($*, Rows),halt."



# Sicstus starts to bug out starting at N=108.
# N = 108 takes 5 seconds on Z3, 300 seconds on Sicstus.
# N = 109 takes 10 seconds on Z3, 0.114 seconds on Sicstus.
# N = 110 takes 4 seconds on Z3,  217 seconds on Sicstus.
# N = 120 takes 9.3 seconds on Z3, 152 seconds on Sicstus.
# N = 115 had not terminated after 50 minutes.


#Compilation of 100 variables took: 0.422 seconds
#Compilation of 101 variables took: 0.438 seconds
#Compilation of 102 variables took: 0.475 seconds
#Compilation of 103 variables took: 0.346 seconds
#Compilation of 104 variables took: 0.417 seconds
#Compilation of 105 variables took: 0.552 seconds
#Compilation of 106 variables took: 0.402 seconds
#Compilation of 107 variables took: 0.324 seconds
#Compilation of 108 variables took: 0.336 seconds
#Compilation of 109 variables took: 0.581 seconds
#Compilation of 110 variables took: 0.366 seconds
#Compilation of 111 variables took: 0.483 seconds
#Compilation of 112 variables took: 0.389 seconds
#Compilation of 113 variables took: 0.383 seconds
#Compilation of 114 variables took: 0.573 seconds
#Compilation of 115 variables took: 0.687 seconds
#Compilation of 116 variables took: 0.713 seconds
#Compilation of 117 variables took: 0.660 seconds
#Compilation of 118 variables took: 0.696 seconds
#Compilation of 119 variables took: 1.059 seconds
#Compilation of 120 variables took: 0.725 seconds

#100-queens Z3 took: 7.882 seconds
#101-queens Z3 took: 13.490 seconds!
#102-queens Z3 took: 6.083 seconds
#103-queens Z3 took: 9.311 seconds
#104-queens Z3 took: 16.136 seconds!
#105-queens Z3 took: 12.199 seconds!
#106-queens Z3 took: 15.235 seconds!
#107-queens Z3 took: 9.695 seconds
#108-queens Z3 took: 11.060 seconds
#109-queens Z3 took: 20.914 seconds!
#110-queens Z3 took: 9.664 seconds
#111-queens Z3 took: 12.658 seconds
#112-queens Z3 took: 28.518 seconds!
#113-queens Z3 took: 13.733 seconds
#114-queens Z3 took: 11.137 seconds
#115-queens Z3 took: 23.671 seconds!
#116-queens Z3 took: 8.245 seconds
#117-queens Z3 took: 11.400 seconds!
#118-queens Z3 took: 9.341 seconds
#119-queens Z3 took: 23.753 seconds!
#120-queens Z3 took: 14.143 seconds!



#100-queens clpfd took: 0.110 seconds
#101-queens clpfd took: 11.215 seconds!
#102-queens clpfd took: 0.157 seconds
#103-queens clpfd took: 0.159 seconds
#104-queens clpfd took: 0.247 seconds
#105-queens clpfd took: 1.317 seconds!
#106-queens clpfd took: 0.286 seconds
#107-queens clpfd took: 0.226 seconds
#108-queens clpfd took: 319.812 seconds!
#109-queens clpfd took: 0.225 seconds
#110-queens clpfd took: 237.690 seconds!
#111-queens clpfd took: 0.431 seconds!
#112-queens clpfd took: 0.151 seconds
#113-queens clpfd took: 0.225 seconds
#114-queens clpfd took: 0.212 seconds
# 115 aborted after more than 50 minutes!
#116-queens clpfd took: 0.318 seconds
#117-queens clpfd took: 0.871 seconds!
#118-queens clpfd took: 0.196 seconds
#119-queens clpfd took: 25.625 seconds!
#120-queens clpfd took: 164.719 seconds!
