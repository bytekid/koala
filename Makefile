# first run './configure' to create Makefile.extras
# 'make' for standard version
# make ASSERT=-noassert to switch off asserts which can be more efficient
# 'make clean' clean most
# 'make clean_all' clean all

# for c++ version of minisat change "module SatSolver =  Minisat  (* CMinisat *)" in src/propSolver.ml
## obsolete 'make CPP=true' for c++ version of minisat
# 'make LGL=true' lingeling for solving/for proofs/unsat cores minisat will still be used
# 'make PicoSAT=true' PicoSAT version

# 'make STATIC=true' to link glibc statically; works only under linux (e.g. for starexec)

# 'make PROFILE=true' for profile 
# for debugging 'make debug=true', 
#     records backtraces run koalaopt with --dbg_backtrace true

# 'make OBJSIZE=true' to use OBJSIZE library to determine OCaml object sizes

# to archive "make archive"
# to archive E bundle "make E=true archive"
# to archive Vampire's clausifier bundle "make V=true archive"

# time koalaopt_lgl --inst_out_proof false --prep_sem_filter none --schedule verification_epr --bmc1_incremental true --bmc1_add_unsat_core none --bmc1_max_bound 10 /M/Intel_Examples/ijcar-paper-cnf/scdpd_miter_full-range.cnf



OCAML=ocaml
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
#OCAMLLIB=/usr/local/lib/ocaml
#OCAMLLIB=/usr/lib/ocaml/3.10.2
#OCAMLLIB is set in Make.extras
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
#OCAMLFLAGS=$(INCLUDES)
#OCAMLOPTFLAGS=$(INCLUDES)
#STATIC_FLAGS=
#CPP=true for CPP solver
CPP=
OCAMLGRAPH_PATH=./ocamlgraph
#different modifications of MiniSat solver
#CSOLVER=solver_mod_inc_clauses 
CSOLVER=solver
#CSOLVER=solver_basic

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
#OCAMLOPTFLAGS=ocamlopt -config | grep "lambda: true"; if [ $$? -eq 0 ]; then echo "-O3" else echo "-inline 10" fi
#OCAMLOPTFLAGS=$(echo | grep "lambda: true"; if [ $$? -eq 0 ]; then echo "-O3" else echo "-inline 10" fi)
OCAMLOPTFLAGS=$(shell ocamlopt -config | grep -q "flambda: true"; if [ $$? -eq 0 ]; then echo "-O3"; else echo "-inline 10"; fi)

OCAMLFLAGS= -w @6+5+7+44+45 $(OCAMLOPTFLAGS) $(ASSERT) -I obj/ -I util/lib  -I ocamlgraph/ -I $(OBJSIZE_DIR)

#OCAMLFLAGS= -w @6+5+7+44+45 -inline 10 $(ASSERT) -I obj/ -I util/lib  -I ocamlgraph/ -I $(OBJSIZE_DIR)
#OCAMLFLAGS= -w @6+5+7+44+45 -O3 $(ASSERT) -I obj/ -I util/lib  -I ocamlgraph/ -I $(OBJSIZE_DIR)
#LIB  = lib

#LEXER = lexer_tptp lexer_fof
LEXER = lexer_tptp lexer_fof
PARSER = parser_tptp
#BEFORE_PARSING = lib parser_types 
#PARSER_TYPES = parser_types
#PARSING= src/$(LEXER).ml src/$(PARSER).ml

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
	aigCommon \
	aigLoader \
	aigWitness \
	aigOptimiser \
	bmc1Common \
	aigClausifier \
	parseFiles \
	aigSaver \
	definitions \
	splitting_grd \
	splitting_nvd \
	splitting_cvd \
	splitting \
	prep_unary_pred \
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
	cMinisat \
	propSolver \
	unsatCore \
	prop_solver_exchange \
	symbol_reach \
	type_inf \
	prep_sem_filter \
	prep_sem_filter_unif \
	inference_rules \
	simplify \
	predElim \
	passiveQueues \
	clauseUnifIndex \
	tstpProof \
	resolution_env \
	resolution_sel \
	resolution_loop \
	implied_units \
	bin_hyper_res \
	def_discovery \
	preprocess \
	instantiation_sel \
	instantiation_loop \
	lemma_lifting \
	bmc1Equal \
	bmc1Axioms \
	bmc1Deadlock \
	bmc1InitTarget \
	bmc1SplitPredicate \
	model_inst \
	model_res \
	bmc1Witness \
	finite_models \
	proof_search_loop \
  abstr_ref \
  abstr_ref_process \
	finite_models_loop \
	proof_search_schedule \
	bmc1_loop \
	lazyList \
	sGGS \
	git_info

#inside src/prop_sat
BASE_NAMES_PROP_SAT=\
                 prop_var\
                 prop_env\
	         prop_fof

#inside src/qbf_Eval
BASE_NAMES_QBF=\
                qbf_env \
	        qbf_preprocess \
                qbf_fof


BASE_NAMES_WITHOUT_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(BASE_NAMES_PROP_SAT) $(BASE_NAMES_AFTER_LEXER) $(BASE_NAMES_QBF) 
BASE_NAMES_WITH_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(BASE_NAMES_PROP_SAT) $(LEXER) $(BASE_NAMES_AFTER_LEXER) $(BASE_NAMES_QBF)

#OBJ_BASE_NAMES = $(BEFORE_PARSING) $(LEXER) $(PARSER) $(BASE_NAMES)
OBJ_BASE_NAMES = $(BASE_NAMES_WITH_LEXER) 

#For testing

TEST_NAMES_AFTER_LEXER = parser_tptp 
TEST_NAMES_WITHOUT_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(TEST_NAMES_AFTER_LEXER)
TEST_NAMES = $(BASE_NAMES_BEFORE_LEXER) $(LEXER) $(TEST_NAMES_AFTER_LEXER)
TEST_INTERFACE = $(TEST_NAMES_WITHOUT_LEXER:%=obj/%.cmi) 
TEST_OBJ = $(TEST_NAMES:%=obj/%.cmx) 
#---

IPROVER_BASE_NAME = koala

#IPROVER_ADD_OBJ_BASE_NAMES = discount instantiation 

ifeq ($(OPT),true)
  COMPILE=$(OCAMLOPT)
  ADDTONAME=opt
 OBJ = $(OBJ_BASE_NAMES:%=obj/%.cmx) 
#OBJ = $(BASE_NAMES_BEFORE_LEXER:%=obj/%.cmx) $(LEXER:%=src/%.ml) $(LEXER:%=obj/%.cmx) $(BASE_NAMES_AFTER_LEXER:%=obj/%.cmx)
 # IPROVER_ADD_OBJ = $(IPROVER_ADD_OBJ_BASE_NAMES:%=obj/%.cmx) obj/$(IPROVER_BASE_NAME).cmx
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
#OCAMLFLAGS -I obj/ -I util/lib -I ocamlgraph
  C_PROFFLAGS = -pg -g
  ADDTONAME=prof

endif


AIGER_NAMES = aiger aigLoad

ifeq ($(CPP),true)	
  CC = g++
  PROP_SOLVER_NAMES=$(AIGER_NAMES) Solver_cpp minisat_c_wrapper minisat_ocaml_wrapper
  IPROVERFLAGS= -cc g++ -ccopt -L$(OCAMLLIB) -I $(OCAMLLIB)
  CFLAGS = -I$(OCAMLLIB) $(C_PROFFLAGS)
  ADDTONAME_CPP="_cpp"	
else
ifeq ($(LGL),true)
   CC=gcc
   PROP_SOLVER_NAMES = $(AIGER_NAMES) lglib lgl_ocaml_wrapper
   CFLAGS = -I$(OCAMLLIB) $(C_PROFFLAGS) -Wall -O3 -DNLGLOG -DNDEBUG -DNCHKSOL -DNLGLPICOSAT
  ADDTONAME_CPP="_lgl"	
else
ifeq ($(PicoSAT),true)
   CC=gcc
   PROP_SOLVER_NAMES = $(AIGER_NAMES) picosat picosat_ocaml_wrapper
   CFLAGS = -I$(OCAMLLIB) $(C_PROFFLAGS) -Wall -O3 -DNLGLOG -DNDEBUG -DNCHKSOL -DNLGLPICOSAT
  ADDTONAME_CPP="_picosat"	
else # default C minisat
  CC=gcc
  PROP_SOLVER_NAMES= $(AIGER_NAMES) $(CSOLVER) solver_interface
  CFLAGS = -O3 -I$(OCAMLLIB) $(C_PROFFLAGS)
endif
endif
endif

# tsar
#PROP_SOLVER_NAMES = $(PROP_SOLVER_NAMES) aiger aigLoader

ifeq ($(debug),true)
#:= "Simply expanded variable"
#-g for debugging recording backtraces
  OCAMLFLAGS:=$(OCAMLFLAGS) -g
endif



IPROVER_C_OBJ= $(PROP_SOLVER_NAMES:%=obj/%.o)

#INTERFACE = $(BEFORE_PARSING:%=obj/%.cmi) obj/$(PARSER).cmi $(BASE_NAMES:%=obj/%.cmi) 

INTERFACE = $(BASE_NAMES_WITHOUT_LEXER:%=obj/%.cmi) 
#IPROVER_INTERFACE_ADD = $(IPROVER_ADD_OBJ_BASE_NAMES:%=obj/%.cmi)


IPROVER_NAME = $(IPROVER_BASE_NAME)$(ADDTONAME)$(ADDTONAME_CPP)

# $(IPROVER_NAME) : util/lib/minisat.cmxa util/lib/hhlmuc.cmxa \

.PHONY : git_info_clean git_info_gen_t util_make objsize

$(IPROVER_NAME) : git_info_clean util_make objsize\
		  $(INTERFACE) $(LEXER:%=src/%.ml)\
                  $(OBJ) $(IPROVER_C_OBJ) $(IPROVER_ADD_OBJ) src/$(IPROVER_BASE_NAME).ml 
	$(COMPILE) $(STATIC_FLAGS) $(IPROVERFLAGS) $(IPROVER_C_OBJ) -o $@ \
        -cclib -L$(OBJSIZE_DIR) objsize.cmxa \
        $(OCAMLFLAGS) unix.cmxa str.cmxa util/lib/minisat.cmxa $(OCAMLGRAPH_PATH)/graph.cmxa $(OBJ) $(IPROVER_ADD_OBJ)
#        $(OCAMLFLAGS) unix.cmxa str.cmxa util/lib/minisat.cmxa util/lib/hhlmuc.cmxa $(OBJ) $(IPROVER_ADD_OBJ)
#        $(OCAMLFLAGS) unix.cmxa str.cmxa $(OBJ) $(IPROVER_ADD_OBJ) 

git_info_clean:
	rm -f obj/git_info.*
	./git_info_gen

src/git_info.ml: src/git_info.mli

src/git_info.mli:
	./git_info_gen


objsize:
	cd $(OBJSIZE_DIR); make lib


# util/lib/minisat.cmxa: export OCAMLLIBDIR=$(OCAMLLIB)
# util/lib/minisat.cmxa: export OCAMLINCDIR=$(OCAMLLIB)

# Better use per-target exports as above, also restore in
# util/lib/hhlmuc.cmxa target below
export OCAMLLIBDIR=$(OCAMLLIB)
export OCAMLINCDIR=$(OCAMLLIB)

#util/lib/minisat.cmxa: util/src/minisat_stubs.cpp util/src/minisat.ml util/src/minisat.mli
##	cd util && $(MAKE) -f Makefile minisat-ocaml-profile
#	cd util && $(MAKE) -f Makefile minisat-ocaml
##	cd util && $(MAKE) -f Makefile minisat-ocaml-debug

# util/lib/hhlmuc.cmxa: export OCAMLLIBDIR=$(OCAMLLIB)
# util/lib/hhlmuc.cmxa: export OCAMLINCDIR=$(OCAMLLIB)

util_make : 
#	cd util && $(MAKE) -f Makefile minisat-ocaml-profile
	cd util && $(MAKE) -f Makefile minisat-ocaml
#	cd util && $(MAKE) -f Makefile minisat-ocaml-debug


util/lib/hhlmuc.cmxa:
	cd util && $(MAKE) -f Makefile hhlmuc-ocaml

test : $(TEST_INTERFACE)\
       $(TEST_OBJ)
	echo "test passed" > test

#$(IPROVER_NAME) : $(PARSING) $(INTERFACE) $(IPROVER_INTERFACE_ADD)\
#                  $(OBJ) $(IPROVER_C_OBJ) $(IPROVER_ADD_OBJ) src/$(IPROVER_BASE_NAME).ml
#	$(COMPILE) $(IPROVERFLAGS) $(IPROVER_C_OBJ) -o $@ \
#        $(OCAMLFLAGS) unix.cmxa str.cmxa $(OBJ) $(IPROVER_ADD_OBJ) 


#------------satandalone prop solver----------------------------------------

STANDALONE_OCAML_NAMES=lib statistics cMinisat options propSolver
STANDALONE_OCAML_INT=$(STANDALONE_OCAML_NAMES:%=obj/%.cmi)
STANDALONE_OCAML_OBJ=$(STANDALONE_OCAML_NAMES:%=obj/%.cmx)
STANDALONE_OBJ=$(STANDALONE_OCAML_OBJ) $(IPROVER_C_OBJ)
prop_solver_standalone :  util/lib/minisat.cmxa $(STANDALONE_OCAML_INT) $(STANDALONE_OBJ)  src/prop_solver_standalone.ml
	$(COMPILE) $(IPROVERFLAGS)  -cclib -L$(OBJSIZE_DIR) objsize.cmxa -o $@ \
        $(OCAMLFLAGS) unix.cmxa str.cmxa  util/lib/minisat.cmxa $(STANDALONE_OBJ) src/prop_solver_standalone.ml

#--------------------------
#        DPLL        
#-------------------------- 


DPLL_IPROVER_LIBS = lib
DPLL_SRC_DIR = src/prop_sat
DPLL_OCAML_LIB_NAMES = \
                 prop_var\
                 prop_env

DPLL_EXEC = dpll_imp dpll_fun

DPLL_SRC = $(DPLL_OCAML_LIB_NAMES:%=$(DPLL_SRC_DIR)/%.ml) $(DPLL_OCAML_LIB_NAMES:%=$(DPLL_SRC_DIR)/%.mli) $(DPLL_EXEC:%=$(DPLL_SRC_DIR)/%.ml)

DPLL_OCAML_INT = $(DPLL_IPROVER_LIBS:%=obj/%.cmi) $(DPLL_OCAML_LIB_NAMES:%=obj/%.cmi) 
DPLL_OCAML_OBJ = $(DPLL_IPROVER_LIBS:%=obj/%.cmx) $(DPLL_OCAML_LIB_NAMES:%=obj/%.cmx) 

DPLL_EXEC = dpll_imp dpll_fun

DPLL_SRC = $(DPLL_OCAML_LIB_NAMES:%=$(DPLL_SRC_DIR)/%.ml) $(DPLL_OCAML_LIB_NAMES:%=$(DPLL_SRC_DIR)/%.mli) $(DPLL_EXEC:%=$(DPLL_SRC_DIR)/%.ml)

DPLL_OCAML_INT = obj/union_find.cmi $(DPLL_IPROVER_LIBS:%=obj/%.cmi) $(DPLL_OCAML_LIB_NAMES:%=obj/%.cmi) 
DPLL_OCAML_OBJ = obj/union_find.cmx $(DPLL_IPROVER_LIBS:%=obj/%.cmx) $(DPLL_OCAML_LIB_NAMES:%=obj/%.cmx) 



dpll_imp : $(DPLL_OCAML_INT) $(DPLL_OCAML_OBJ) $(DPLL_SRC_DIR)/dpll_imp.ml 
	$(COMPILE) $(IPROVERFLAGS)  -cclib -L$(OBJSIZE_DIR) objsize.cmxa -o $@ \
	$(OCAMLFLAGS) unix.cmxa str.cmxa  $(DPLL_OCAML_OBJ) $(DPLL_SRC_DIR)/dpll_imp.ml

dpll_fun : $(DPLL_OCAML_INT) $(DPLL_OCAML_OBJ) $(DPLL_SRC_DIR)/dpll_fun.ml 
	$(COMPILE) $(IPROVERFLAGS)  -cclib -L$(OBJSIZE_DIR) objsize.cmxa -o $@ \
	$(OCAMLFLAGS) unix.cmxa str.cmxa $(DPLL_OCAML_OBJ) $(DPLL_SRC_DIR)/dpll_fun.ml

# dpll_func : $(DPLL_OCAML_INT) $(DPLL_OCAML_OBJ) src/dpll_func.ml 
# 	$(COMPILE) $(IPROVERFLAGS)  -cclib -L$(OBJSIZE_DIR) objsize.cmxa -o $@ \
# 	$(OCAMLFLAGS) unix.cmxa str.cmxa  util/lib/minisat.cmxa $(DPLL_OCAML_OBJ) src/dpll_func.ml

# dpll : $(DPLL_OCAML_INT) $(DPLL_OCAML_OBJ) src/dpll.ml 
# 	$(COMPILE) $(IPROVERFLAGS)  -cclib -L$(OBJSIZE_DIR) objsize.cmxa -o $@ \
# 	$(OCAMLFLAGS) unix.cmxa str.cmxa  $(DPLL_OCAML_OBJ) src/dpll.ml


#------------------
#      QBF TODO: remove and replace QBF_OCAML_LIB_NAMES with BASE_NAMES_QBF above
#------------------
QBF_IPROVER_LIBS = lib def_discovery prop_var prop_env prop_fof

QBF_SRC_DIR=src/qbf_eval

QBF_OCAML_LIB_NAMES = \
                 qbf_env \
	         qbf_preprocess \
                 qbf_fof 

QBF_EXEC=koala_qbf

QBF_SRC = $(QBF_OCAML_LIB_NAMES:%=$(QBF_SRC_DIR)/%.ml) $(QBF_OCAML_LIB_NAMES:%=$(QBF_SRC_DIR)/%.mli) $(QBF_EXEC:%=$(QBF_SRC_DIR)/%.ml)

QBF_OCAML_INT = $(QBF_IPROVER_LIBS:%=obj/%.cmi) $(QBF_OCAML_LIB_NAMES:%=obj/%.cmi) 
QBF_OCAML_OBJ = $(QBF_IPROVER_LIBS:%=obj/%.cmx) $(QBF_OCAML_LIB_NAMES:%=obj/%.cmx) 



$(QBF_EXEC): $(QBF_OCAML_INT) $(QBF_OCAML_OBJ) $(QBF_SRC_DIR)/$(QBF_EXEC).ml 
	$(COMPILE) $(IPROVERFLAGS)  -cclib -L$(OBJSIZE_DIR) objsize.cmxa -o $@ \
	$(OCAMLFLAGS) unix.cmxa str.cmxa  $(QBF_OCAML_OBJ) $(QBF_SRC_DIR)/$(QBF_EXEC).ml



#-----

#src/$(LEXER).ml : $(@l)
#$(LEXER:%=src/%.ml) : $(@l)
#	ocamllex $<

#$(LEXER:%=src/%.ml) : $(LEXER:%=src/%.mll) 
#	ocamllex $<

src/lexer_tptp.mli src/lexer_tptp.ml : src/lexer_tptp.mll
	ocamllex $<

src/lexer_fof.mli src/lexer_fof.ml : src/lexer_fof.mll
	ocamllex $<



#generates both mli and ml from mly
src/$(PARSER).mli src/$(PARSER).ml: src/$(PARSER).mly
	ocamlyacc src/$(PARSER).mly



#implicit rules
obj/%.o : src/%.c
	$(CC) $(CFLAGS) -c -o $@ $<
#	gcc $(CFLAGS) -c -o $@ $<

obj/%.o : src/%.C
	$(CC) $(CFLAGS) -c -o $@ $<

obj/%.o : src/%.cpp
	$(CC) $(CFLAGS) -c -o $@ $<


obj/%.cmi : src/%.mli 
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $< 

obj/%.cmx : src/%.ml 
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $<

obj/%.cmi : $(DPLL_SRC_DIR)/%.mli 
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $< 

obj/%.cmx : $(DPLL_SRC_DIR)/%.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $<

obj/%.cmi : $(QBF_SRC_DIR)/%.mli 
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $< 

obj/%.cmx : $(QBF_SRC_DIR)/%.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $<

.PHONY : clean clean-util archive docs

docs: $(INTERFACE)
	ocamldoc -dot -I obj/ -I util/lib -d docs $(BASE_NAMES_WITHOUT_LEXER:%=src/%.mli) $(BASE_NAMES_WITHOUT_LEXER:%=src/%.ml) src/$(IPROVER_BASE_NAME).ml

clean: clean-util
	rm -f $(IPROVER_NAME) $(IPROVER_NAME)_picosat $(IPROVER_NAME)_lgl $(IPROVER_NAME)_cpp $(IPROVER_BASE_NAME)prof $(IPROVER_NAME)_cpp $(DPLL_EXEC) $(QBF_EXEC) $(LEXER:%=src/%.ml) src/$(PARSER).ml src/$(PARSER).mli obj/*.cmo obj/*.cmx obj/*.cmi obj/*.o
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
	./LICENSE_PicoSAT \
	./LICENSE_MiniSAT \
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
	./util/Makefile.minisat	\
	./util/lib \
	./util/minisat \
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

#ARCHIVE_LTB_NAMES=./LTB

#use this to temporally adding some names
ARCHIVE_Extras=Makefile_build Makefile_OCamlMakefile $(OCAMLGRAPH_PATH)


#to archive E bundle "make E=true archive"

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

archive: clean_all
	add=$$(date +%Y_%-b_%-d_%-kh); \
	echo $(ARCHIVE_BASE_DIR); \
	new_dir="$(ARCHIVE_BASE_DIR)_$${add}";\
	name_tar="$${new_dir}.tar.gz"; \
	mkdir $${new_dir}; \
	mkdir "$${new_dir}/obj";\
	mkdir "$${new_dir}/util";\
	mkdir "$${new_dir}/LTB"; \
	mkdir "$${new_dir}/SAT";\
	mkdir "$${new_dir}/$(DPLL_SRC_DIR)/";\
	mkdir "$${new_dir}/$(QBF_SRC_DIR)/";\
	cp -r $(ARCHIVE_NAMES) "$${new_dir}";\
	cp -r $(ARCHIVE_UTIL_NAMES) "$${new_dir}/util/";\
	cp -r $(ARCHIVE_LTB_NAMES) "$${new_dir}/LTB/";\
	cp -r $(ARCHIVE_SAT_NAMES) "$${new_dir}/SAT/";\
	cp -r $(DPLL_SRC) "$${new_dir}/$(DPLL_SRC_DIR)/";\
	cp -r $(QBF_SRC) "$${new_dir}/$(QBF_SRC_DIR)/";\
	rm -f "$${new_dir}/src"/lgl*;\
	pwd;\
	tar -czvf "$${name_tar}" "$${new_dir}"; \
	rm -rf $${new_dir};\
	if [ -d "Archive" ]; \
	then mv "$${name_tar}" "Archive/"; fi;



#archive_with_e: clean_all
#	add=$$(date +%-d%-b%-kh_%Y); new_dir="koala_e_bundle_$${add}"; name_tar="$${new_dir}.tar.gz"; mkdir $${new_dir}; mkdir "$${new_dir}/obj"; cp -r $(IPROVER_ARCHIVE_NAMES) ./E_Prover "$${new_dir}"; pwd; tar -czvf "$${name_tar}" "$${new_dir}"; rm -rf $${new_dir}; if [ -d "Archive" ]; then mv "$${name_tar}" "Archive/"; fi;



# do not add src/lexer_tptp.mli src/lexer_tptp.ml; they are regenerated during .depend which will cause a loop
ML_SRC_dep = src/lexer_fof.mll src/lexer_tptp.mll src/parser_tptp.mly $(BASE_NAMES_BEFORE_LEXER:%=src/%.ml) $(BASE_NAMES_AFTER_LEXER:%=src/%.ml) $(BASE_NAMES_BEFORE_LEXER:%=src/%.mli) $(BASE_NAMES_AFTER_LEXER:%=src/%.mli) $(IPROVER_BASE_NAME:%=src/%.ml) $(DPLL_SRC) $(QBF_SRC) 


ML_SRC_ocamldep = src/lexer_tptp.ml src/lexer_tptp.mli src/lexer_fof.ml src/lexer_fof.mli  src/parser_tptp.ml src/parser_tptp.mli $(ML_SRC_dep)

C_SRC=src/*.h src/*.c
CPP_SRC=src/*.cpp src/*.hpp



# a bit ugly but can not use $(DPLL_SRC_DIR) due to escaping /
.depend: $(ML_SRC_dep) $(C_SRC)
	@rm -f .depend
	@touch .depend
	@ocamldep -native -I src -I $(DPLL_SRC_DIR) -I $(QBF_SRC_DIR)  $(ML_SRC_ocamldep) > deps.tmp
	@sed 's/src\/prop_sat\//obj\//g' deps.tmp > deps1.tmp
	@sed 's/src\/qbf_eval\//obj\//g' deps1.tmp > deps2.tmp
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
