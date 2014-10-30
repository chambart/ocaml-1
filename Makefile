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

#temporary
all: stdlib/stdlib.cma

include config/Makefile

#Used by makefile builtin rules
CC=$(BYTECC)
CFLAGS=-DCAML_NAME_SPACE -O $(BYTECCCOMPOPTS) $(IFLEXDIR) -I $(BYTERUN_DIR)
DFLAGS=-DCAML_NAME_SPACE -g -DDEBUG $(BYTECCCOMPOPTS) $(IFLEXDIR) -I $(BYTERUN_DIR)

BOOT_DIR=boot
BYTERUN_DIR=byterun

OCAMLRUN=$(BYTERUN_DIR)/ocamlrun$(EXE)
BOOT_OCAMLC=$(OCAMLRUN) $(BOOT_DIR)/ocamlc
BOOT_OCAMLOPT=$(OCAMLRUN) $(BOOT_DIR)/ocamlopt
BOOT_OCAMLDEP=$(OCAMLRUN) $(BOOT_DIR)/ocamldep

COMPFLAGS=-strict-sequence -w +33..39 -g -warn-error A -nostdlib
OPTCOMPFLAGS=-warn-error A -nostdlib -g

include byterun/Makefile.include

include stdlib/Makefile.include

