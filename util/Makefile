# Makefile for utilities 
# Created: 2011-12-01 Christoph Sticksel

########################################################################
# Configuration

# export OCAMLLIBDIR=$(OCAMLLIB)
# export OCAMLINCDIR=$(OCAMLLIB)
# export OCAMLLIBDIR=/usr/lib/ocaml
# export OCAMLINCDIR=/usr/lib/ocaml
# export OCAMLLIBDIR=/home/chris/lib/ocaml
# export OCAMLINCDIR=/home/chris/lib/ocaml
# export OCAMLLIBDIR=/shareddata/homes/sticksec/lib/ocaml
# export OCAMLINCDIR=/shareddata/homes/sticksec/lib/ocaml

MINISATDIR=$(CURDIR)/minisat
HHLMUCDIR=$(CURDIR)/Haifa-HLMUC
FIVERDIR=$(CURDIR)/Fiver

export CXX=g++
export AR=ar
export OCAMLC=ocamlc
export OCAMLOPT=ocamlopt
export OCAMLMKLIB=ocamlmklib
export OCAMLMKTOP=ocamlmktop
export RANLIB=ranlib


########################################################################
# Top-level targets

all: minisat-ocaml fiver-ocaml # hhlmuc-ocaml

.PHONY : clean

clean: clean-minisat-ocaml clean-fiver-ocaml # clean-hhlmuc-ocaml


########################################################################
# Make Fiver OCaml interface using generic Makefile.clib

# Set variables $(CLIBNAME), $(CLIBINCDIR) and $(CLIBLIBDIR)
fiver-opt-ocaml-lib fiver-nonopt-ocaml-lib fiver-test clean-fiver-ocaml: export CLIBNAME=fiver

fiver-opt-ocaml-lib: export CLIBLIBDIR=$(FIVERDIR)/stOpt64

fiver-nonopt-ocaml-lib: export CLIBLIBDIR=$(FIVERDIR)/st64

fiver-opt-ocaml-lib fiver-nonopt-ocaml-lib fiver-test: export CLIBINCDIR=$(FIVERDIR)

# Make optimised library by default
fiver-ocaml: fiver-opt-ocaml-lib

# Make Fiver interface
fiver-opt-ocaml-lib fiver-nonopt-ocaml-lib: 
	$(MAKE) -f Makefile.clib fiver-ocaml

# Make testing executable for Fiver interface
fiver-test: 
	$(MAKE) -f Makefile.clib fiver-test

# Clean interface 
clean-fiver-ocaml: 
	$(MAKE) -f Makefile.clib clean-fiver-ocaml


########################################################################
# Make MiniSat using generic Makefile.minisat

# Set variable $(MINISATDIR)
# minisat-lib-standard \
# minisat-lib-profile \
# minisat-lib-debug \
# minisat-lib-release \
# minisat-exec-standard \
# minisat-exec-profile \
# minisat-exec-debug \
# minisat-exec-release \
# minisat-exec-static \
# clean-minisat-lib: export MINISATDIR:=$(MINISATDIR)
export MINISATDIR:=$(MINISATDIR)

# Set variable $(MINISAT)
# minisat-lib-standard \
# minisat-lib-profile \
# minisat-lib-debug \
# minisat-lib-release \
# minisat-exec-standard \
# minisat-exec-profile \
# minisat-exec-debug \
# minisat-exec-release \
# minisat-exec-static \
# clean-minisat-lib: export MINISAT=minisat
export MINISAT=minisat

minisat-lib-standard:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-lib-standard

minisat-lib-profile:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-lib-profile

minisat-lib-debug:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-lib-debug

minisat-lib-release:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-lib-release

minisat-exec-standard:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-exec-standard

minisat-exec-profile:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-exec-profile

minisat-exec-debug:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-exec-debug

minisat-exec-release:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-exec-release

minisat-exec-static:
	$(MAKE) -f $(CURDIR)/Makefile.minisat minisat-exec-static

clean-minisat-lib:
	$(MAKE) -f $(CURDIR)/Makefile.minisat clean-minisat


# ########################################################################
# # Make Haifa-HLMUC using generic Makefile.minisat

# # Set variable $(MINISATDIR)
# hhlmuc-lib-standard \
# hhlmuc-lib-profile \
# hhlmuc-lib-debug \
# hhlmuc-lib-release \
# hhlmuc-exec-standard \
# hhlmuc-exec-profile \
# hhlmuc-exec-debug \
# hhlmuc-exec-release \
# hhlmuc-exec-static \
# clean-hhlmuc-lib: export MINISATDIR=$(HHLMUCDIR)

# # Set variable $(MINISAT)
# hhlmuc-lib-standard \
# hhlmuc-lib-profile \
# hhlmuc-lib-debug \
# hhlmuc-lib-release \
# hhlmuc-exec-standard \
# hhlmuc-exec-profile \
# hhlmuc-exec-debug \
# hhlmuc-exec-release \
# hhlmuc-exec-static \
# clean-hhlmuc-lib: export MINISAT=hhlmuc

# hhlmuc-lib-standard:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-lib-standard

# hhlmuc-lib-profile:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-lib-profile

# hhlmuc-lib-debug:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-lib-debug

# hhlmuc-lib-release:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-lib-release

# hhlmuc-exec-standard:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-exec-standard

# hhlmuc-exec-profile:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-exec-profile

# hhlmuc-exec-debug:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-exec-debug

# hhlmuc-exec-release:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-exec-release

# hhlmuc-exec-static:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat hhlmuc-exec-static

# clean-hhlmuc-lib:
# 	$(MAKE) -f $(CURDIR)/Makefile.minisat clean-hhlmuc


########################################################################
# Make MiniSat OCaml interface using generic Makefile.clib

# Set variables $(CLIBNAME), $(CLIBINCDIR) and $(CLIBLIBDIR)
# minisat-ocaml-lib \
# minisat-test \
# clean-minisat-ocaml-lib: export CLIBNAME=minisat
export CLIBNAME=minisat

# minisat-ocaml-lib \
# minisat-test \
# clean-minisat-ocaml-lib: export CLIBINCDIR=$(MINISATDIR)
export CLIBINCDIR=$(MINISATDIR)

# minisat-ocaml-lib \
# minisat-test \
# clean-minisat-ocaml-lib: export CLIBLIBDIR=$(MINISATDIR)/simp
export CLIBLIBDIR=$(MINISATDIR)/simp

# Make release library by default
minisat-ocaml: minisat-ocaml-release 

# Make test executable with debug library 
minisat-test: minisat-ocaml-debug minisat-ocaml minisat-test-ocaml-lib

# Clean library and interface 
clean-minisat-ocaml: clean-minisat-lib clean-minisat-ocaml-lib

# Make standard library and interface 
minisat-ocaml-standard: minisat-lib-standard minisat-ocaml-lib

# Make debug library and interface 
minisat-ocaml-debug: minisat-lib-debug minisat-ocaml-lib

# Make profiling library and interface 
minisat-ocaml-profile: minisat-lib-profile minisat-ocaml-lib

# Make release library and interface 
minisat-ocaml-release: minisat-lib-release minisat-ocaml-lib

# Make MiniSat interface
minisat-ocaml-lib: 
	$(MAKE) -f Makefile.clib minisat-ocaml

# Make testing executable for MiniSat interface
minisat-test-ocaml-lib: 
	$(MAKE) -f Makefile.clib minisat-test

# Clean interface 
clean-minisat-ocaml-lib: clean-minisat-lib
	$(MAKE) -f Makefile.clib clean-minisat-ocaml

# ########################################################################
# # Make Haifa-HLMUC OCaml interface using generic Makefile.clib

# # Set variables $(CLIBNAME), $(CLIBINCDIR) and $(CLIBLIBDIR)
# hhlmuc-ocaml-lib \
# hhlmuc-test \
# clean-hhlmuc-ocaml-lib: export CLIBNAME=hhlmuc

# hhlmuc-ocaml-lib \
# hhlmuc-test \
# clean-hhlmuc-ocaml-lib: export CLIBINCDIR=$(HHLMUCDIR)

# hhlmuc-ocaml-lib \
# hhlmuc-test \
# clean-hhlmuc-ocaml-lib: export CLIBLIBDIR=$(HHLMUCDIR)/simp

# # Make release library by default
# hhlmuc-ocaml: hhlmuc-ocaml-release

# # Clean library and interface 
# clean-hhlmuc-ocaml: clean-hhlmuc-lib clean-hhlmuc-ocaml-lib

# # Make standard library and interface 
# hhlmuc-ocaml-standard: hhlmuc-lib-standard hhlmuc-ocaml-lib

# # Make debug library and interface 
# hhlmuc-ocaml-debug: hhlmuc-lib-debug hhlmuc-ocaml-lib

# # Make profiling library and interface 
# hhlmuc-ocaml-profile: hhlmuc-lib-profile hhlmuc-ocaml-lib

# # Make release library and interface 
# hhlmuc-ocaml-release: hhlmuc-lib-release hhlmuc-ocaml-lib

# # Make Haifa-HLMUC interface
# hhlmuc-ocaml-lib: 
# 	$(MAKE) -f Makefile.clib hhlmuc-ocaml

# # Clean interface 
# clean-hhlmuc-ocaml-lib: clean-hhlmuc-lib
# 	$(MAKE) -f Makefile.clib clean-hhlmuc-ocaml


