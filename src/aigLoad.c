#include <assert.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <stdio.h>

#include "aiger.h"

// aiger itself
struct aiger* aig = NULL;
// current AND structure
struct aiger_and* cur_and = NULL;
// current SYMBOL structure
struct aiger_symbol* cur_symbol = NULL;

value C_clear_aiger ( value unit )
{
	aiger_reset(aig);
	aig = NULL;
	return unit;
}

value C_init_aiger ( value filename )
{
	if ( aig != NULL )
		C_clear_aiger(Val_unit);

	const char* fn = String_val(filename);
	FILE* input = fopen(fn,"rb");
	if ( input == NULL )
	{
	    printf("Could not open file %s\n", fn);
	    return Val_true;
	}

	// init aiger
	aig = aiger_init();
	const char* error = aiger_read_from_file(aig,input);
	if ( error )
	{
	    printf("%s\n", fn);
		return Val_true;
	}
	return Val_false;
}

value C_get_and_lhs ( value unit )
{
	return Val_int(cur_and->lhs);
}

value C_get_and_rhs0 ( value unit )
{
	return Val_int(cur_and->rhs0);
}

value C_get_and_rhs1 ( value unit )
{
	return Val_int(cur_and->rhs1);
}


value C_get_symbol_lit ( value unit )
{
	return Val_int(cur_symbol->lit);
}

value C_get_symbol_next ( value unit )
{
	return Val_int(cur_symbol->next);
}

value C_get_symbol_reset ( value unit )
{
	return Val_int(cur_symbol->reset);
}

value C_get_symbol_size ( value unit )
{
	return Val_int(cur_symbol->size);
}

value C_get_symbol_just ( value index )
{
	return Val_int(cur_symbol->lits[Int_val(index)]);
}

value C_get_symbol_name ( value unit )
{
	return copy_string(cur_symbol->name);
}


value C_n_vars ( value unit )
{
	return Val_int(aig->maxvar);
}


value C_num_ands ( value unit )
{
	return Val_int(aig->num_ands);
}

value C_num_ins ( value unit )
{
	return Val_int(aig->num_inputs);
}

value C_num_outs ( value unit )
{
	return Val_int(aig->num_outputs);
}

value C_num_bads ( value unit )
{
	return Val_int(aig->num_bad);
}

value C_num_latches ( value unit )
{
	return Val_int(aig->num_latches);
}

value C_num_constraints ( value unit )
{
	return Val_int(aig->num_constraints);
}

value C_num_fairness ( value unit )
{
	return Val_int(aig->num_fairness);
}

value C_num_justice ( value unit )
{
	return Val_int(aig->num_justice);
}


value C_set_cur_and ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_ands);
	cur_and = aig->ands + idx;
	return Val_unit;
}

value C_set_cur_in ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_inputs);
	cur_symbol = aig->inputs + idx;
	return Val_unit;
}

value C_set_cur_out ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_outputs);
	cur_symbol = aig->outputs + idx;
	return Val_unit;
}

value C_set_cur_bad ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_bad);
	cur_symbol = aig->bad + idx;
	return Val_unit;
}

value C_set_cur_latch ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_latches);
	cur_symbol = aig->latches + idx;
	return Val_unit;
}

value C_set_cur_constraint ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_constraints);
	cur_symbol = aig->constraints + idx;
	return Val_unit;
}

value C_set_cur_fairness ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_fairness);
	cur_symbol = aig->fairness + idx;
	return Val_unit;
}

value C_set_cur_justice ( value index )
{
	assert(aig);
	int idx = Int_val(index);
	assert(idx >= 0);
	assert(idx < aig->num_justice);
	cur_symbol = aig->justice + idx;
	return Val_unit;
}



