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

# Makefile for the parser generator.

YACC_CFLAGS=-O -DNDEBUG $(BYTECCCOMPOPTS)

YACC_OBJS:= closure.o error.o lalr.o lr0.o main.o mkpar.o output.o reader.o \
  skeleton.o symtab.o verbose.o warshall.o

YACC_OBJS:=$(addprefix $(YACC_DIR)/, $(YACC_OBJS))

$(OCAMLYACC): $(YACC_OBJS)
	$(CC) $(CFLAGS) $(CCLINKFLAGS) -o $@ $^

$(YACC_DIR)/%.o: $(YACC_DIR)/%.c
	$(CC) $(CFLAGS) $(CPPFLAGS) $(TARGET_ARCH) -c $(OUTPUT_OPTION) $(YACC_CFLAGS) $<

clean::
	rm -f $(YACC_DIR)/*.o $(OCAMLYACC)

$(YACC_OBJS):  $(YACC_DIR)/defs.h
$(YACC_DIR)/main.o: $(VERSION_H)
