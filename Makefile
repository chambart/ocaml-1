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
BYTERUN_DIR=byterun
YACC_DIR=yacc

OCAMLRUN=$(BYTERUN_DIR)/ocamlrun$(EXE)
OCAMLYACC=$(YACC_DIR)/ocamlyacc$(EXE)
BOOT_OCAMLC=$(OCAMLRUN) $(BOOT_DIR)/ocamlc
BOOT_OCAMLOPT=$(OCAMLRUN) $(BOOT_DIR)/ocamlopt
BOOT_OCAMLDEP=$(OCAMLRUN) $(BOOT_DIR)/ocamldep

COMPFLAGS=-strict-sequence -w +33..39 -g -warn-error A -nostdlib
OPTCOMPFLAGS=-warn-error A -nostdlib -g

#temporary
all: stdlib/stdlib.cma $(OCAMLYACC)


#version
VERSION_H=config/version.h

$(VERSION_H) : VERSION
	echo "#define OCAML_VERSION \"`sed -e 1q $<`\"" > $@

clean::
	rm -f $(VERSION_H)

include byterun/Makefile.include

include stdlib/Makefile.include

include yacc/Makefile.yacc.include

