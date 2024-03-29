##########################################################################
#                                                                        #
#  Ocamlgraph: a generic graph library for OCaml                         #
#  Copyright (C) 2004-2010                                               #
#  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        #
#                                                                        #
#  This software is free software; you can redistribute it and/or        #
#  modify it under the terms of the GNU Library General Public           #
#  License version 2.1, with the special exception on linking            #
#  described in file LICENSE.                                            #
#                                                                        #
#  This software is distributed in the hope that it will be useful,      #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  #
#                                                                        #
##########################################################################

# Where to install the binaries
DESTDIR	=
prefix	=/usr/local
exec_prefix=${prefix}
datarootdir=${prefix}/share
BINDIR	=$(DESTDIR)${exec_prefix}/bin

# Where to install the man page
MANDIR=${datarootdir}/man

# Other variables set by ./configure
OCAMLC   = ocamlc.opt
OCAMLOPT = ocamlopt.opt
OCAMLDEP = ocamldep -slash
OCAMLDOC = ocamldoc.opt
OCAMLLEX = ocamllex.opt
OCAMLYACC= ocamlyacc -v
OCAMLLIB = /home/bytekid/.opam/4.08.0/lib/ocaml
OCAMLBEST= opt
OCAMLVERSION = 4.08.0
OCAMLWEB = true
OCAMLWIN32 = no
OCAMLFIND = ocamlfind
EXE = 
LIBEXT = .a
OBJEXT = .o

# Others global variables
OCAMLGRAPH_SRCDIR	= src
OCAMLGRAPH_LIBDIR	= lib

INCLUDES= -I $(OCAMLGRAPH_SRCDIR) -I $(OCAMLGRAPH_LIBDIR)
BFLAGS = $(INCLUDES) -g -dtypes -w +a -w -4 -w -44 -w -50 -w -48 -w -29
OFLAGS = $(INCLUDES)

# main target
#############

NAME=ocamlgraph

ifeq (no,yes)
all: byte $(OCAMLBEST) viewer dgraph editor
else
all: byte $(OCAMLBEST)
endif

# bytecode and native-code compilation
######################################

OCAMLGRAPH_LIB= unionfind heap bitv persistentQueue
OCAMLGRAPH_LIB:=$(patsubst %, $(OCAMLGRAPH_LIBDIR)/%.cmo, $(OCAMLGRAPH_LIB))

CMO =	version util blocks persistent imperative \
	delaunay builder classic rand oper \
	components path nonnegative traverse coloring topological kruskal flow \
	prim dominator graphviz gml dot_parser dot_lexer dot pack \
	gmap minsep cliquetree mcs_m md strat fixpoint leaderlist contraction \
	graphml merge mincut clique weakTopological chaoticIteration
CMO := $(OCAMLGRAPH_LIB) $(patsubst %, $(OCAMLGRAPH_SRCDIR)/%.cmo, $(CMO))

CMX = $(CMO:.cmo=.cmx)
CMA = graph.cma
CMXA = graph.cmxa
ifeq (yes,yes)
CMXS = graph.cmxs
endif

CMI = sig sig_pack dot_ast
CMI := $(patsubst %, src/%.cmi, $(CMI))

GENERATED = META \
	src/gml.ml src/version.ml \
	src/dot_parser.ml src/dot_parser.mli src/dot_lexer.ml

$(CMX): OFLAGS += -for-pack Graph

byte: $(CMA)
opt: $(CMXA) $(CMXS)

graph.cma: graph.cmo
	$(OCAMLC) $(INCLUDES) -a -g -o $@ $^

graph.cmxa: graph.cmx
	$(OCAMLOPT) $(INCLUDES) -a -o $@ $^

graph.cmxs: graph.cmx
	$(OCAMLOPT) $(INCLUDES) -shared -o $@ $^

graph.cmi: graph.cmo
graph.o: graph.cmx

graph.cmo: $(CMI) $(CMO)
	$(OCAMLC) $(INCLUDES) -pack -g -o $@ $^

graph.cmx: $(CMI) $(CMX)
	$(OCAMLOPT) $(INCLUDES) -pack -o $@ $^

VERSION=1.8.8

ifdef SOURCE_DATE_EPOCH
BUILD_DATE=$(shell date -u -d "@$(SOURCE_DATE_EPOCH)" 2>/dev/null || date -u -r "$(SOURCE_DATE_EPOCH)" 2>/dev/null || date)
else
BUILD_DATE=$(shell date)
endif

src/version.ml: Makefile
	rm -f $@
	echo "let version = \""$(VERSION)"\"" > $@
	echo 'let date = "'"$(BUILD_DATE)"'"' >> $@

# gtk2 graph editor
###################

ED_DIR=editor

editor: $(ED_DIR)/editor.byte $(ED_DIR)/editor.$(OCAMLBEST)

ED_CMO = ed_hyper ed_graph ed_draw ed_display ed_main
ED_CMO:= $(patsubst %, $(ED_DIR)/%.cmo, $(ED_CMO))
ED_CMX = $(ED_CMO:.cmo=.cmx)
ED_CMI = $(ED_CMO:.cmo=.cmi)

ED_INCLUDES =  -I +threads -I $(ED_DIR) -I .

$(ED_CMI) $(ED_CMO): BFLAGS+= $(ED_INCLUDES)
$(ED_CMI) $(ED_CMO): $(CMA)
$(ED_CMX): OFLAGS+= $(ED_INCLUDES)
$(ED_CMX): $(CMXA)

$(ED_DIR)/editor.byte: $(CMA) $(ED_CMO)
	$(OCAMLC) -g -o $@ $(ED_INCLUDES) \
		lablgtk.cma lablgnomecanvas.cma unix.cma $^

$(ED_DIR)/editor.opt: $(CMXA) $(ED_CMX)
	$(OCAMLOPT) -o $@ $(ED_INCLUDES) \
		lablgtk.cmxa lablgnomecanvas.cmxa unix.cmxa $^

# gtk2 graph viewer (deprecated)
###################

VIEWER_DIR=view_graph

viewer: $(VIEWER_DIR)/viewgraph.byte $(VIEWER_DIR)/viewgraph.$(OCAMLBEST)

VIEWER_CMO=viewGraph_core viewGraph_select viewGraph_utils viewGraph_test
VIEWER_CMO:=$(patsubst %,$(VIEWER_DIR)/%.cmo, $(VIEWER_CMO))
VIEWER_CMX=$(VIEWER_CMO:.cmo=.cmx)
VIEWER_CMI=$(VIEWER_CMO:.cmo=.cmi)
VIEWER_MLI=$(VIEWER_CMI:.cmi=.mli)

VIEWER_INCLUDES=  -I $(VIEWER_DIR) -I .

$(VIEWER_CMI) $(VIEWER_CMO): BFLAGS+= $(VIEWER_INCLUDES)
$(VIEWER_CMX): OFLAGS+= $(VIEWER_INCLUDES) -for-pack Viewgraph
$(VIEWER_CMI) $(VIEWER_CMO): $(CMA)
$(VIEWER_CMX): $(CMXA)

VIEWER_CMOLIB	= $(VIEWER_DIR)/viewgraph.cmo
VIEWER_CMILIB	= $(VIEWER_DIR)/viewgraph.cmi
VIEWER_CMXLIB	= $(VIEWER_DIR)/viewgraph.cmx

$(VIEWER_CMOLIB): $(filter-out $(VIEWER_DIR)/viewGraph_test.cmo, $(VIEWER_CMO))
	$(OCAMLC) -o $@ $(VIEWER_INCLUDES) -pack $^

$(VIEWER_CMXLIB): $(filter-out $(VIEWER_DIR)/viewGraph_test.cmx, $(VIEWER_CMX))
	$(OCAMLOPT) -o $@ $(VIEWER_INCLUDES) -pack $^

$(VIEWER_DIR)/viewgraph.byte: $(CMA) $(VIEWER_CMOLIB)
	$(OCAMLC) -g -o $@ $(VIEWER_INCLUDES) \
		lablgtk.cma gtkInit.cmo lablgnomecanvas.cma unix.cma $^

$(VIEWER_DIR)/viewgraph.opt: $(CMXA) $(VIEWER_CMXLIB)
	$(OCAMLOPT) -o $@ $(VIEWER_INCLUDES) \
		lablgtk.cmxa gtkInit.cmx lablgnomecanvas.cmxa unix.cmxa $^

# new gtk2 graph viewer: dgraph
###############################

DGRAPH_DIR=dgraph

dgraph: $(DGRAPH_DIR)/dgraph.byte $(DGRAPH_DIR)/dgraph.$(OCAMLBEST)

DGRAPH_CMO=xDotDraw xDot \
	dGraphModel \
	dGraphTreeLayout dGraphSubTree dGraphTreeModel \
	dGraphViewItem dGraphView \
	dGraphRandModel dGraphContainer \
	dGraphViewer
DGRAPH_CMO:=$(patsubst %,$(DGRAPH_DIR)/%.cmo, $(DGRAPH_CMO))
DGRAPH_CMX=$(DGRAPH_CMO:.cmo=.cmx)
DGRAPH_CMI=$(filter-out dgraph/dGraphViewer.cmi, $(DGRAPH_CMO:.cmo=.cmi))

DGRAPH_INCLUDES=  -I $(DGRAPH_DIR) -I .

$(DGRAPH_CMI) $(DGRAPH_CMO): BFLAGS+= $(DGRAPH_INCLUDES)
$(DGRAPH_CMX): OFLAGS+= $(DGRAPH_INCLUDES) -for-pack Dgraph

$(DGRAPH_CMI) $(DGRAPH_CMO): $(CMA)
$(DGRAPH_CMX): $(CMXA)

DGRAPH_CMOLIB	= $(DGRAPH_DIR)/dgraph.cmo
DGRAPH_CMILIB	= $(DGRAPH_DIR)/dgraph.cmi
DGRAPH_CMXLIB	= $(DGRAPH_DIR)/dgraph.cmx

dgraph/dGraphViewer.cmo: $(DGRAPH_CMOLIB)
dgraph/dGraphViewer.cmx: $(DGRAPH_CMXLIB)

$(DGRAPH_CMOLIB): $(filter-out dgraph/dGraphViewer.cmo, $(DGRAPH_CMO))
	$(OCAMLC) -o $@ $(DGRAPH_INCLUDES) -pack $^

$(DGRAPH_CMXLIB): $(filter-out dgraph/dGraphViewer.cmx, $(DGRAPH_CMX))
	$(OCAMLOPT) -o $@ $(DGRAPH_INCLUDES) -pack $^

$(DGRAPH_DIR)/dgraph.byte: $(CMA) $(DGRAPH_CMOLIB) \
  $(DGRAPH_DIR)/dGraphViewer.cmo
	$(OCAMLC) -g -o $@ $(DGRAPH_INCLUDES) \
		lablgtk.cma gtkInit.cmo lablgnomecanvas.cma $^

$(DGRAPH_DIR)/dgraph.opt: $(CMXA) $(DGRAPH_CMXLIB) \
  $(DGRAPH_DIR)/dGraphViewer.cmx
	$(OCAMLOPT) -o $@ $(DGRAPH_INCLUDES) \
		lablgtk.cmxa gtkInit.cmx lablgnomecanvas.cmxa $^

# Fixing issue with "make -j"
#############################

# wait than all bytecodes are done before packing the native library:
# without these extra dependencies, building graph.cmx also rebuilds the .cmi
# while graph.cmi may be required at the same time by some .cmo of the
# bytecodes, leading to tentative access to a corrupted graph.cmi.

ifeq (no,yes)
graph.cmx: | $(DGRAPH_DIR)/dgraph.byte \
	$(VIEWER_DIR)/viewgraph.byte \
	$(ED_DIR)/editor.byte
endif

$(CMX): | $(OCAMLGRAPH_SRCDIR)/blocks.cmo

# No .mli for blocks.ml: so, to avoid clash when generating block.cmi
# from both ocamlc and ocamlopt, force to fully compile the bytecode library
# before the native one
$(OCAMLGRAPH_SRCDIR)/blocks.cmx: | graph.cmo

# Examples
##########

EXAMPLESBIN=bin/demo.$(OCAMLBEST) bin/demo_planar.$(OCAMLBEST) \
  bin/bench.$(OCAMLBEST) bin/color.$(OCAMLBEST) bin/sudoku.$(OCAMLBEST) \
  bin/test.$(OCAMLBEST)

.PHONY: examples
examples: $(EXAMPLESBIN)

.PHONY: demo
demo: bin/demo.$(OCAMLBEST)

bin/demo.byte: $(CMXA) examples/demo.cmo
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cma unix.cma $^

bin/demo.opt: $(CMXA) examples/demo.cmx
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cmxa unix.cmxa $^

bin/fgtest.opt: $(CMXA) myTest/fgtest.cmx
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cmxa unix.cmxa $^

bin/demo_planar.byte: $(CMA) examples/demo_planar.cmo
	mkdir -p bin
	$(OCAMLC) -o $@ graphics.cma unix.cma $^

bin/demo_planar.opt: $(CMXA) examples/demo_planar.cmx
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cmxa unix.cmxa $^

bin/compare_prim_kruskal.opt: $(CMXA) examples/compare_prim_kruskal.ml
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cmxa unix.cmxa $^

bin/demo_prim.opt: $(CMXA) examples/demo_prim.ml
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cmxa unix.cmxa $^

bin/color.byte: $(CMA) examples/color.cmo
	mkdir -p bin
	$(OCAMLC) -o $@ graphics.cma unix.cma $^

bin/color.opt: $(CMXA) examples/color.cmx
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cmxa unix.cmxa $^

bin/sudoku.byte: $(CMA) examples/sudoku.cmo
	mkdir -p bin
	$(OCAMLC) -o $@ graphics.cma unix.cma $^

bin/sudoku.opt: $(CMXA) examples/sudoku.cmx
	mkdir -p bin
	$(OCAMLOPT) -o $@ graphics.cmxa unix.cmxa $^

test: $(CMA) tests/test.ml
	ocaml unix.cma graphics.cma $^

test-bf: $(CMA) tests/test_bf.ml
	ocaml unix.cma graphics.cma $^

test-johnson: $(CMA) tests/test_johnson.ml
	ocaml unix.cma graphics.cma $^

bin/test-ts: $(CMXA) tests/test_topsort.ml
	mkdir -p bin
	$(OCAMLOPT) -o $@ unix.cmxa $^

test-ts: bin/test-ts
	bin/test-ts 10

nonneg: $(CMA) tests/nonneg.ml
	ocaml unix.cma graphics.cma $^

test-graphml: $(CMA) tests/testgraphml.ml
	ocaml unix.cma $^

bin/test.byte: $(CMA) tests/test.cmo
	$(OCAMLC) -g -unsafe -o $@ unix.cma graphics.cma $^

bin/test.opt: $(CMXA) tests/test.cmx
	$(OCAMLOPT) -unsafe -inline 100 -o $@ unix.cmxa graphics.cmxa $^

bin/test_bf.byte: $(CMA) tests/test_bf.ml
	$(OCAMLC) -g -o $@ unix.cma graphics.cma $^

bin/nonneg.byte: $(CMA) tests/nonneg.ml
	$(OCAMLC) -g -o $@ unix.cma graphics.cma $^

bench: bin/bench.$(OCAMLBEST)
	bin/bench.opt

bin/bench.opt: $(CMXA) tests/bench.ml
	$(OCAMLOPT) -unsafe -inline 100 -o $@ unix.cmxa $^

bin/testunix.opt: $(CMXA) myTest/testunix.ml
	$(OCAMLOPT) -unsafe -inline 100 -o $@ unix.cmxa $^

check: $(CMA) tests/check.ml bin/test-ts
	ocaml -I . $(CMA) tests/test_clique.ml tests/check.ml
	bin/test-ts 10

# Additional rules
##################

EXAMPLES = demo color demo_planar sudoku
EXAMPLESBIN:=$(patsubst %, bin/%.opt, $(EXAMPLES))
EXAMPLES:= $(patsubst %, examples/%.ml, $(EXAMPLES))

examples: $(EXAMPLESBIN)

TESTS = test check
TESTS := $(patsubst %, tests/%.ml, $(TESTS))

DPD_GRAPH_ML= $(TESTS) $(EXAMPLES)

$(DPD_GRAPH_ML:.ml=.cmo): $(CMA)
$(DPD_GRAPH_ML:.ml=.cmx): $(CMXA)

# installation
##############

INSTALL_LIBDIR=$(DESTDIR)$(OCAMLLIB)/ocamlgraph

install: install-$(OCAMLBEST) install-byte
	mkdir -p $(BINDIR)
ifeq (no,yes)
ifeq ($(OCAMLBEST),byte)
	cp -f $(BINDIR)/graph-editor.byte $(BINDIR)/graph-editor$(EXE)
	cp -f $(BINDIR)/graph-viewer.byte $(BINDIR)/graph-viewer$(EXE)
else
	cp -f $(BINDIR)/graph-editor.opt $(BINDIR)/graph-editor$(EXE)
	cp -f $(BINDIR)/graph-viewer.opt $(BINDIR)/graph-viewer$(EXE)
endif
endif

install-byte:
	mkdir -p $(INSTALL_LIBDIR)
	cp -f graph.cmo graph.cmi $(CMA) $(INSTALL_LIBDIR)
	cp -f $(OCAMLGRAPH_SRCDIR)/*.mli $(INSTALL_LIBDIR)
ifeq (no,yes)
	mkdir -p $(BINDIR)
	cp -f $(ED_DIR)/editor.byte $(BINDIR)/graph-editor.byte
	cp -f $(VIEWER_CMILIB) $(VIEWER_CMOLIB) $(INSTALL_LIBDIR)
	cp -f $(DGRAPH_CMILIB) $(DGRAPH_CMOLIB) $(INSTALL_LIBDIR)
	cp -f $(VIEWER_DIR)/*.mli $(DGRAPH_DIR)/*.mli $(INSTALL_LIBDIR)
	cp -f $(DGRAPH_DIR)/dgraph.byte $(BINDIR)/graph-viewer.byte
endif

install-opt: install-byte
	mkdir -p $(INSTALL_LIBDIR)
	cp -f graph$(OBJEXT) graph$(LIBEXT) graph.cmi graph.cmx \
		$(CMXA) $(CMXS) $(INSTALL_LIBDIR)
	cp -f $(OCAMLGRAPH_SRCDIR)/*.mli $(INSTALL_LIBDIR)
ifeq (no,yes)
	mkdir -p $(BINDIR)
	cp -f $(ED_DIR)/editor.opt $(BINDIR)/graph-editor.opt
	cp -f $(VIEWER_CMILIB) $(VIEWER_CMXLIB) $(VIEWER_CMXLIB:.cmx=.o) \
		$(INSTALL_LIBDIR)
	cp -f $(DGRAPH_CMILIB) $(DGRAPH_CMXLIB) $(DGRAPH_CMXLIB:.cmx=.o) \
		$(INSTALL_LIBDIR)
	cp -f $(DGRAPH_DIR)/dgraph.opt $(BINDIR)/graph-viewer.opt
	cp -f $(VIEWER_DIR)/*.mli $(DGRAPH_DIR)/*.mli $(INSTALL_LIBDIR)
endif

ifdef DESTDIR
OCAMLFINDDEST := -destdir $(DESTDIR)
endif

ifeq ($(OCAMLBEST),byte)
  OCAMLFIND_OPT_FILES=
else
  OCAMLFIND_OPT_FILES=graph$(OBJEXT) graph$(LIBEXT) graph.cmx $(CMXA) $(CMXS)
  ifeq (no,yes)
    OCAMLFIND_OPT_FILES+=\
      $(VIEWER_CMXLIB) $(VIEWER_CMXLIB:.cmx=.o) \
      $(DGRAPH_CMXLIB) $(DGRAPH_CMXLIB:.cmx=.o)
  endif
endif

install-findlib: META
ifdef OCAMLFIND
ifeq (no,yes)
	$(OCAMLFIND) install $(OCAMLFINDDEST) ocamlgraph META \
		$(OCAMLGRAPH_SRCDIR)/*.mli $(VIEWER_DIR)/*.mli $(DGRAPH_DIR)/*.mli \
		graph.cmo graph.cmi \
		$(CMA) \
		$(VIEWER_CMOLIB) $(VIEWER_CMILIB) \
                $(DGRAPH_CMOLIB) $(DGRAPH_CMILIB) \
                $(OCAMLFIND_OPT_FILES)
else
	$(OCAMLFIND) install $(OCAMLFINDDEST) ocamlgraph META \
		$(OCAMLGRAPH_SRCDIR)/*.mli $(VIEWER_DIR)/*.mli $(DGRAPH_DIR)/*.mli \
		graph$(LIBEXT) graph.cmo graph.cmi $(CMA) \
	        $(OCAMLFIND_OPT_FILES)
endif
endif

META: META.in Makefile
	sed -e s/VERSION/$(VERSION)/ -e s/CMA/$(CMA)/ -e s/CMXA/$(CMXA)/ -e s/CMXS/$(CMXS)/ \
		$@.in > $@

# documentation
###############

DOCFILES=$(NAME).ps $(NAME).html

NODOC	= blocks dot_parser dot_lexer version
NODOC	:= $(patsubst %, $(OCAMLGRAPH_SRCDIR)/%.cmo, $(NODOC))
DOC_CMO	= $(filter-out $(NODOC) $(OCAMLGRAPH_LIB), $(CMO))
DOC_SRC	= $(CMI:.cmi=.mli) $(DOC_CMO:.cmo=.mli) $(DOC_CMO:.cmo=.ml)
ifeq (no,yes)
DOC_SRC := $(DOC_SRC) $(DGRAPH_CMI:.cmi=.mli)
endif
DOC_CHARSET = utf-8

.PHONY: doc
doc: $(DOC_CMO)
	mkdir -p doc
	rm -f doc/*
	$(OCAMLDOC) -charset $(DOC_CHARSET) -d doc -html $(DGRAPH_INCLUDES) \
		-I lib -I src $(DOC_SRC)

# literate programming
$(NAME).tex: $(DOC_SRC)
	$(OCAMLWEB) -o $@ $^

wc:
	ocamlwc -p $(OCAMLGRAPH_SRCDIR)/*.mli $(OCAMLGRAPH_SRCDIR)/*.ml

# file headers
##############

headers:
	headache \
	   -c misc/headache_config.txt \
	   -h misc/header.txt \
	   Makefile.in configure.in README.adoc \
	   $(OCAMLGRAPH_LIBDIR)/*.ml $(OCAMLGRAPH_LIBDIR)/*.ml[ily] \
	   $(OCAMLGRAPH_SRCDIR)/*.ml $(OCAMLGRAPH_SRCDIR)/*.ml[ily] \
	   $(ED_DIR)/*.ml $(ED_DIR)/*.mli
	headache \
	   -c misc/headache_config.txt \
	   -h $(DGRAPH_DIR)/headers/CEA_LGPL \
	   $(DGRAPH_DIR)/*.ml $(DGRAPH_DIR)/*.mli
# export
########

EXPORTDIR=$(NAME)-$(VERSION)
TAR=$(EXPORTDIR).tar

FTP = /users/www-perso/projets/ocamlgraph/download
WWW = /users/www-perso/projets/ocamlgraph

FILES = src/*.ml* lib/*.ml* Makefile.in configure configure.in META.in  \
	.depend editor/ed_*.ml* editor/Makefile \
	editor/tests/*.dot editor/tests/*.gml \
	view_graph/*.ml view_graph/*.mli \
	view_graph/README view_graph/Makefile \
	dgraph/*.ml dgraph/*.mli \
	examples/*.ml tests/*.ml \
	README.adoc FAQ CREDITS INSTALL.adoc COPYING LICENSE CHANGES

export: source export-doc export-web export-delaunay

source:
	mkdir -p export
	cd export; rm -rf $(EXPORTDIR)
	mkdir -p export/$(EXPORTDIR)/bin
	cp --parents $(FILES) export/$(EXPORTDIR)
	cd export ; tar cf $(TAR) $(EXPORTDIR) ; gzip -f --best $(TAR)
	cp export/$(TAR).gz $(FTP)
	cp README.adoc FAQ CREDITS COPYING LICENSE CHANGES $(EXAMPLES) $(FTP)

# Build and install the .tar.gz requiered by Frama-C
framac: EXPORTDIR=ocamlgraph
framac: FTP=$$HOME/GIT/frama-c.master
framac:
	mkdir -p export
	cd export; rm -rf $(EXPORTDIR)
	mkdir -p export/$(EXPORTDIR)/bin
	cp --parents $(FILES) export/$(EXPORTDIR)
	cd export ; tar cf $(TAR) $(EXPORTDIR) ; gzip -f --best $(TAR)
	cp export/$(TAR).gz $(FTP)
	make -C $(FTP) force-ocamlgraph

www/version.prehtml: Makefile.in
	echo "<#def version>$(VERSION)</#def>" > www/version.prehtml

export-web: www/version.prehtml
	make -C www install

export-doc: $(DOC_CMO)
	rm -f $(WWW)/doc/*
	-$(OCAMLDOC) -d $(WWW)/doc -html $(DGRAPH_INCLUDES) -I lib -I src $(DOC_SRC)

MISCFTP = $(HOME)/WWW/ftp/ocaml/misc
DELAUNAY=delaunay.ml delaunay.mli
export-delaunay:
	cd src; cp -f $(DELAUNAY) $(MISCFTP)
	cd src; rm -f delaunay.annot; caml2html -noannot -d $(MISCFTP) $(DELAUNAY)

# generic rules
###############

.SUFFIXES: .mli .ml .cmi .cmo .cmx .mll .mly .tex .dvi .ps .html

.mli.cmi:
	$(OCAMLC) -c $(BFLAGS) $<

.ml.cmo:
	$(OCAMLC) -c $(BFLAGS) $<

.ml.o:
	$(OCAMLOPT) -c $(OFLAGS) $<

.ml.cmx:
	$(OCAMLOPT) -c $(OFLAGS) $<

.mll.ml:
	$(OCAMLLEX) $<

.mly.ml:
	$(OCAMLYACC) -v $<

.mly.mli:
	$(OCAMLYACC) -v $<

.tex.dvi:
	latex $< && latex $<

.dvi.ps:
	dvips $< -o $@

.tex.html:
	hevea $<

# Emacs tags
############

otags:
	otags -r src editor view_graph

tags:
	find . -name "*.ml*" | sort -r | xargs \
	etags "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"

# Makefile is rebuilt whenever Makefile.in or configure.in is modified
######################################################################

Makefile: Makefile.in config.status
	if test -e $@; then chmod a+w $@; fi
	./config.status
	chmod a-w $@

config.status: configure
	./config.status --recheck

configure: configure.in
	autoconf

# clean
#######

clean:
	rm -f *~
	for d in $(OCAMLGRAPH_SRCDIR) $(OCAMLGRAPH_LIBDIR) $(ED_DIR) $(VIEWER_DIR) $(DGRAPH_DIR) \
		tests examples; \
	do \
	  rm -f $$d/*.cm[iox] $$d/*$(OBJEXT) $$d/*~ $$d/*.annot; \
	done
	rm -f $(GENERATED) $(OCAMLGRAPH_SRCDIR)/dot_parser.output
	rm -f graph.*a graph.cm* graph.o graph$(LIBEXT)
	rm -f $(ED_DIR)/editor.byte $(ED_DIR)/editor.opt
	rm -f $(VIEWER_DIR)/viewgraph.byte $(VIEWER_DIR)/viewgraph.opt
	rm -f $(DGRAPH_DIR)/dgraph.byte $(DGRAPH_DIR)/dgraph.opt
	rm -f $(DGRAPH_DIR)/dgraph
	rm -f *.haux *.aux *.log $(NAME).tex $(NAME).dvi $(DOCFILES)
	rm -f $(EXAMPLESBIN)

dist-clean distclean:: clean
	rm -f Makefile config.cache config.log config.status *.byte *.opt

svnclean svn-clean:: dist-clean
	rm -f config.* configure configure.lineno

# depend
########

.PHONY: depend
.depend depend: $(GENERATED)
	rm -f .depend
	$(OCAMLDEP) $(INCLUDES) -I $(ED_DIR) -I $(VIEWER_DIR) -I $(DGRAPH_DIR)\
		$(OCAMLGRAPH_LIBDIR)/*.ml $(OCAMLGRAPH_LIBDIR)/*.mli \
		$(OCAMLGRAPH_SRCDIR)/*.ml $(OCAMLGRAPH_SRCDIR)/*.mli \
		$(ED_DIR)/*.mli $(ED_DIR)/*.ml \
		$(VIEWER_DIR)/*.mli $(VIEWER_DIR)/*.ml \
		$(DGRAPH_DIR)/*.mli $(DGRAPH_DIR)/*.ml > .depend

include .depend
