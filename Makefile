#########################################################################
#                                                                       #
#                                 OCaml                                 #
#                                                                       #
#            Xavier Leroy, projet Cristal, INRIA Rocquencourt           #
#                                                                       #
#   Copyright 1999 Institut National de Recherche en Informatique et    #
#   en Automatique.  All rights reserved.  This file is distributed     #
#   under the terms of the Q Public License version 1.0.                #
#                                                                       #
#########################################################################

# The main Makefile

include config/Makefile

#Used by makefile builtin rules
CC=$(BYTECC)

BOOT_DIR=boot
BYTERUN_DIR=byterun_build
YACC_DIR=yacc
STDLIB_DIR=stdlib
STDLIB_CMI=$(STDLIB_DIR)/stdlib.cmi.stamp
STDLIB_BYTE=$(STDLIB_DIR)/stdlib.byte.stamp
STDLIB_OPT=$(STDLIB_DIR)/stdlib.opt.stamp

OCAMLRUN=$(BYTERUN_DIR)/ocamlrun$(EXE)
OCAMLYACC=$(YACC_DIR)/ocamlyacc$(EXE)
VERSION_H=config/version.h

BOOT_OCAMLC=$(OCAMLRUN) $(BOOT_DIR)/ocamlc
BOOT_OCAMLDEP=$(OCAMLRUN) $(BOOT_DIR)/ocamldep
BOOT_OCAMLLEX=$(OCAMLRUN) $(BOOT_DIR)/ocamllex

#Compiled using boot compiler
FIRST_OCAMLC_LOC=./ocamlc
FIRST_OCAMLOPT_LOC=./ocamlopt
FIRST_OCAMLDEP_LOC=./ocamldep
FIRST_OCAMLC=$(OCAMLRUN) $(FIRST_OCAMLC_LOC)
FIRST_OCAMLOPT=$(OCAMLRUN) $(FIRST_OCAMLOPT_LOC)
FIRST_OCAMLDEP=$(OCAMLRUN) $(FIRST_OCAMLDEP_LOC)

COMPFLAGS=-strict-sequence -w +33..39 -g -warn-error A -nostdlib
OPTCOMPFLAGS=-warn-error A -nostdlib -g
LINKFLAGS=-nostdlib
YACCFLAGS=-v


#temporary
all: stdlib/stdlib.cma stdlib/stdlib.cmxa $(OCAMLYACC)

.PHONY: force

include Makefile.byterun

include Makefile.stdlib

include Makefile.yacc

include Makefile.compiler

include Makefile.generating

