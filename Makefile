# first run './configure' to create Makefile.extras
# 'make' for standard version
# make ASSERT=-noassert to switch off asserts which can be more efficient
# 'make clean' clean most
# 'make clean_all' clean all

# 'make STATIC=true' to link glibc statically; works only under linux (e.g. for starexec)

# 'make PROFILE=true' for profile 
# for debugging 'make debug=true', 
#     records backtraces run koalaopt with --dbg_backtrace true

# 'make OBJSIZE=true' to use OBJSIZE library to determine OCaml object sizes

OCAML=ocaml
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
EPROVER_PATH="./E_Prover" 
VCLAUSIFIER_PATH="./VClausifier"
OPT=true
OBJPATH=obj/
ADDTONAME=
PROFILE=
C_PROFFLAGS=
OCAMLOPTOPT=ocamlopt.opt
OCAMLDEP=ocamldep
INCLUDES=
# debug=true
debug=
CPP=
OCAMLGRAPH_PATH=./ocamlgraph
CSOLVER=solver

#
# OBJSIZE include/lib settings
#

OBJSIZE=
#OBJSIZE=true

ifeq ($(OBJSIZE),true)
  OBJSIZE_DIR=util/objsize-0.16
else
  OBJSIZE_DIR=util/objsize-stub
endif

ifeq ($(STATIC),true)
#  STATIC_FLAGS=-ccopt -static
# changed in OCaml 4.06
   STATIC_FLAGS=-ccopt -static -ccopt -Wl,--no-export-dynamic 
endif

ASSERT=
#ASSERT=-noassert
OCAMLOPTFLAGS=$(shell ocamlopt -config | grep -q "flambda: true"; if [ $$? -eq 0 ]; then echo "-O3"; else echo "-inline 10"; fi)
OCAMLFLAGS= -w @6+5+7+44+45 $(OCAMLOPTFLAGS) $(ASSERT) -I obj/ -I util/lib  -I ocamlgraph/ -I $(OBJSIZE_DIR)
LEXER = lexer_tptp lexer_fof
PARSER = parser_tptp

include Makefile.extras

BASE_NAMES_BEFORE_LEXER = \
	lib \
  ref_cnt \
	hashcons \
	union_find \
	options \
	statistics \
	signals \
	bit_vec \
	assignMap \
	tableArray \
	heap \
	priority_queue \
	priority_queues \
	tree \
	trie \
	trie_func \
	vectorIndex \
	abstDB \
	abstAssignDB \
	symbol \
	symbolDB \
	var \
	term \
	termDB \
	orderings \
	subst \
	substBound \
	dismatching \
	clause \
	shared_clauses \
	systemDBs \
	important_lit \
	logic_interface \
	cone_symb \
	finiteDomain \
	parser_types \
	problem_properties \

#large theories are removed at the moment/attaend later
BASE_NAMES_AFTER_LEXER = \
	parser_tptp \
	instantiation_env \
	parseFiles \
	definitions \
	splitting_grd \
	splitting_nvd \
	splitting_cvd \
	splitting \
	unif \
	unifIndex \
	discrTree \
	discrTree_func \
	unifIndexMap \
	unifIndexDiscrTree \
	unifIndexDebug \
	subsetSubsume \
	subsumptionIndex \
	eq_axioms \
	symbol_reach \
	type_inf \
	inference_rules \
	finite_models \
	lazyList \
	constraint \
	sGGS \
	git_info

BASE_NAMES_WITHOUT_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(BASE_NAMES_AFTER_LEXER)
BASE_NAMES_WITH_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(LEXER) $(BASE_NAMES_AFTER_LEXER)

OBJ_BASE_NAMES = $(BASE_NAMES_WITH_LEXER) 

#For testing

TEST_NAMES_AFTER_LEXER = parser_tptp 
TEST_NAMES_WITHOUT_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(TEST_NAMES_AFTER_LEXER)
TEST_NAMES = $(BASE_NAMES_BEFORE_LEXER) $(LEXER) $(TEST_NAMES_AFTER_LEXER)
TEST_INTERFACE = $(TEST_NAMES_WITHOUT_LEXER:%=obj/%.cmi) 
TEST_OBJ = $(TEST_NAMES:%=obj/%.cmx) 
#---

IPROVER_BASE_NAME = koala


ifeq ($(OPT),true)
  COMPILE=$(OCAMLOPT)
  ADDTONAME=opt
 OBJ = $(OBJ_BASE_NAMES:%=obj/%.cmx) 
    IPROVER_ADD_OBJ = obj/$(IPROVER_BASE_NAME).cmx
else 	
  IPROVERFLAGS= -custom
  COMPILE=$(OCAMLC)
  OBJ = $(OBJ_BASE_NAMES:%=%.cmo) 
  IPROVER_ADD_OBJ = $(IPROVER_ADD_OBJ_BASE_NAMES:%=%.cmo) 
  CFLAGS    = -I$(OCAMLLIB) -std=c99
endif

ifeq ($(PROFILE),true)
  OCAMLFLAGS += -p -g 
  C_PROFFLAGS = -pg -g
  ADDTONAME=prof

endif


ifeq ($(debug),true)
#:= "Simply expanded variable"
#-g for debugging recording backtraces
  OCAMLFLAGS:=$(OCAMLFLAGS) -g
endif


INTERFACE = $(BASE_NAMES_WITHOUT_LEXER:%=obj/%.cmi) 

IPROVER_NAME = $(IPROVER_BASE_NAME)$(ADDTONAME)$(ADDTONAME_CPP)

.PHONY : git_info_clean git_info_gen_t util_make objsize

$(IPROVER_NAME) : git_info_clean util_make objsize\
		  $(INTERFACE) $(LEXER:%=src/%.ml)\
                  $(OBJ) $(IPROVER_C_OBJ) $(IPROVER_ADD_OBJ) src/$(IPROVER_BASE_NAME).ml 
	$(COMPILE) $(STATIC_FLAGS) $(IPROVERFLAGS) $(IPROVER_C_OBJ) -o $@ \
        -cclib -L$(OBJSIZE_DIR) objsize.cmxa \
        $(OCAMLFLAGS) unix.cmxa str.cmxa $(OCAMLGRAPH_PATH)/graph.cmxa $(OBJ) $(IPROVER_ADD_OBJ)

git_info_clean:
	rm -f obj/git_info.*
	./git_info_gen

src/git_info.ml: src/git_info.mli

src/git_info.mli:
	./git_info_gen


objsize:
	cd $(OBJSIZE_DIR); make lib

export OCAMLLIBDIR=$(OCAMLLIB)
export OCAMLINCDIR=$(OCAMLLIB)

util_make :
	cd ocamlgraph && ./configure && make


util/lib/hhlmuc.cmxa:
	cd util && $(MAKE) -f Makefile hhlmuc-ocaml

test : $(TEST_INTERFACE)\
       $(TEST_OBJ)
	echo "test passed" > test



src/lexer_tptp.mli src/lexer_tptp.ml : src/lexer_tptp.mll
	ocamllex $<

src/lexer_fof.mli src/lexer_fof.ml : src/lexer_fof.mll
	ocamllex $<



#generates both mli and ml from mly
src/$(PARSER).mli src/$(PARSER).ml: src/$(PARSER).mly
	ocamlyacc src/$(PARSER).mly


obj/%.cmi : src/%.mli 
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $< 

obj/%.cmx : src/%.ml 
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $<

.PHONY : clean clean-util archive docs

docs: $(INTERFACE)
	ocamldoc -dot -I obj/ -I util/lib -d docs $(BASE_NAMES_WITHOUT_LEXER:%=src/%.mli) $(BASE_NAMES_WITHOUT_LEXER:%=src/%.ml) src/$(IPROVER_BASE_NAME).ml

clean: clean-util
	rm -f $(IPROVER_NAME) $(IPROVER_NAME)_cpp $(IPROVER_BASE_NAME)prof $(IPROVER_NAME)_cpp $(LEXER:%=src/%.ml) src/$(PARSER).ml src/$(PARSER).mli obj/*.cmo obj/*.cmx obj/*.cmi obj/*.o
	cd $(OBJSIZE_DIR) && make clean


clean-util:
	cd util && $(MAKE) -f Makefile clean

clean_all: clean
	rm -f .depend;\
	if [ -d $(EPROVER_PATH) ]; then cd $(EPROVER_PATH); make clean; rm -f eprover; cd ../; fi;\
#	if [ -d $(VCLAUSIFIER_PATH) ]; then cd $(VCLAUSIFIER_PATH); make clean; rm -f vclausify_rel; cd ../; fi;\
	if [ -d $(OCAMLGRAPH_PATH) ]; then cd $(OCAMLGRAPH_PATH); make clean; cd ../; fi
# keep vclausify_rel
	if [ -d $(OCAMLGRAPH_PATH) ]; then cd $(OCAMLGRAPH_PATH); make clean; cd ../; fi
	cd $(OBJSIZE_DIR) && make clean

ARCHIVE_IPROVER_NAMES=\
	./src \
	./LICENSE \
	./LICENSE_OCAMLGRAPH \
	./README \
	./Makefile \
	./Makefile.extras \
	./configure \
  ./git_info_gen \
	./Changelog \
	./problem.p \

ARCHIVE_UTIL_NAMES=\
	./util/Makefile \
	./util/Makefile.clib \
	./util/lib \
	./util/objsize-0.16 \
	./util/objsize-stub \
	./util/src \

ARCHIVE_LTB_NAMES=\
	./LTB/koala_sine.sh \
	./LTB/koala_sine_single.sh \
	./LTB/koala_sine_turing.sh \
	./LTB/koala_sine_reduced_cores.sh \
	./LTB/create_ltb_batch.sh \
	./LTB/Makefile \
	./LTB/TreeLimitedRun.c \
	./LTB/MZR.header \
	./LTB/MZR_turing.header \
	./LTB/SMO.header \
	./LTB/ISA.header \
	./LTB/MZR_bushy_rand_100.list \
	./LTB/MZR_chainy_rand_100.list \
	./LTB/SMO_2011.list \
	./LTB/ISA_2011.list \
	./LTB/MZR_bushy.list \
	./LTB/MZR_chainy.list

ARCHIVE_SAT_NAMES=\
	./SAT/koala_sat_single.sh

#use this to temporally adding some names
ARCHIVE_Extras=Makefile_build Makefile_OCamlMakefile $(OCAMLGRAPH_PATH)


ifeq ($(E),true) 
   ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(EPROVER_PATH) $(ARCHIVE_Extras)
   ARCHIVE_BASE_DIR="koala_e_bundle"
else 
 ifeq ($(V),true)
  ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(VCLAUSIFIER_PATH) $(ARCHIVE_Extras) $
  ARCHIVE_BASE_DIR="koala_vampire_clausifier_bundle"
 else	
   ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(ARCHIVE_Extras)
   ARCHIVE_BASE_DIR="koala"
 endif
endif 

# do not add src/lexer_tptp.mli src/lexer_tptp.ml; they are regenerated during .depend which will cause a loop
ML_SRC_dep = src/lexer_fof.mll src/lexer_tptp.mll src/parser_tptp.mly $(BASE_NAMES_BEFORE_LEXER:%=src/%.ml) $(BASE_NAMES_AFTER_LEXER:%=src/%.ml) $(BASE_NAMES_BEFORE_LEXER:%=src/%.mli) $(BASE_NAMES_AFTER_LEXER:%=src/%.mli) $(IPROVER_BASE_NAME:%=src/%.ml) 


ML_SRC_ocamldep = src/lexer_tptp.ml src/lexer_tptp.mli src/lexer_fof.ml src/lexer_fof.mli  src/parser_tptp.ml src/parser_tptp.mli $(ML_SRC_dep)

C_SRC=src/*.h src/*.c
CPP_SRC=src/*.cpp src/*.hpp



# a bit ugly but can not use $(DPLL_SRC_DIR) due to escaping /
.depend: $(ML_SRC_dep) $(C_SRC)
	@rm -f .depend
	@touch .depend
	@ocamldep -native -I src $(ML_SRC_ocamldep) > deps.tmp
	@sed 's/src\//obj\//g' deps2.tmp > deps3.tmp
	@cat deps3.tmp >> .depend
	@gcc -MM $(CFLAGS) $(C_SRC) > deps.tmp
	@sed 's/^\([^ 	]\{1\}\)/obj\/\1/' deps.tmp > deps2.tmp
	@cat deps2.tmp >> .depend
	@g++ -MM $(CFLAGS) $(CPP_SRC) > deps.tmp
	@sed 's/^\([^ 	]\{1\}\)/obj\/\1/' deps.tmp > deps2.tmp
	@cat deps2.tmp >> .depend
	@rm -f deps.tmp deps2.tmp


-include .depend
