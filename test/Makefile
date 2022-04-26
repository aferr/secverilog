SHELL := /bin/bash
BENCHS=$(shell ls *.v)

BENCH_EXP=$(BENCHS:.v=.expected)
BENCH_SMT=$(BENCHS:.v=z3)
BENCH_OUT=$(BENCHS:.v=.out)
BENCH_LATTICE=$(BENCHS:.v=.lattice)
BENCH_FUN=$(BENCHS:.v=.fun)


all: $(BENCH_OUT)
	@echo "All Tests passed!"
.PRECIOUS: %.z3

%.z3: %.v %.lattice %.fun
	@../bin/iverilog -F $*.fun -l $*.lattice -z $*.v

%.out: %.z3 %.expected
	@diff $*.expected <(z3 -smt2  $< | grep "sat") > $@


.PHONY: clean
clean:
	@rm -rf *.out *.z3


