# This Makefile produces the CakeML compiler executable by linking the
# bootstrapped CakeML compiler with the implementation of the FFI primitives.
# It also includes rules for compiling CakeML programs with the CakeML compiler
# then similarly linking the resulting machine code with the FFI primitives to
# produce executables. It is designed to work on GNU/Linux, macOS, and Windows.

# To set the stack and heap sizes for CakeML programs, set the
# CML_STACK_SIZE and CML_HEAP_SIZE environment variables (or see basis_ffi.c)
# The unit of measure for both arguments is mebibytes (1024 * 1024 bytes).

OS ?= $(shell uname)

ifeq ($(OS),Windows_NT)
	PREF =
	SUFF = .exe
	EVALFLAG =
else
	PREF = ./
	SUFF =
	EVALFLAG = -DEVAL
endif

ifeq ($(OS),Darwin)
	# These options avoid linker warnings on macOS
	LDFLAGS += -Wl,-no_pie
	EVALFLAG =
endif

CFLAGS+=-O2
LDLIBS+=-lm
CMLS = $(wildcard *.cml)
CML_PROGS = $(patsubst %.cml,%.cake$(SUFF),$(CMLS))

# Links the CakeML compiler and compiles all the .cml files in this directory
all: cake$(SUFF)

# Linking the CakeML compiler

cake$(SUFF): cake.S basis_ffi.c
	$(CC) $(CFLAGS) $< basis_ffi.c $(LOADLIBES) $(EVALFLAG) -o $@ $(LDFLAGS) $(LDLIBS)

# Using the CakeML compiler

# The conventions used here for extensions, namely,
# *.cml          # CakeML source program
# *.cake.S       # CakeML-generated machine-code
# *.cake$(SUFF)  # CakeML-generated executable
# are not required in general when using CakeML.
# (They are not used here for the compiler itself.)

%.cake.S : %.cml cake$(SUFF)
	$(PREF)cake$(SUFF) $(CAKEFLAGS) <$< >$@

%.cake$(SUFF) : %.cake.S basis_ffi.c
	$(CC) $< basis_ffi.c $(LOADLIBES) $(LDLIBS) -o $@ $(LDFLAGS) $(LDLIBS)

clean:
	$(RM) basis_ffi.o cake.o cake$(SUFF) *.cake.o *.cake.S *.cake$(SUFF)
