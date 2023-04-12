# HOW TO RUN GDB BECAUSE THIS PROJECT IS VERY WEIRD

This is monumentally stupid because `ivl` is a dll, so it is a pain to
run the debugger on it.

The normal `iverilog` binary is a driver that calls into the `ivl`
dll. `ivl` is the real program that you want to debug.

- run the preprocessor, because `ivl` does not support macros.
```verilog-0.9.6/ivlpp/ivlpp <your-verilog-file> > preprocessed.v```

- Now run `gdb` on `verilog-0.9.6/ivl`, and run with the arguments
  `-z preprocessed.v`
  You cannot pass a lattice/fun file to `ivl`, but you are probably
  just trying to get a backtrace from a segfault, so you shouldn't
  care :)



todo maybe write more here
