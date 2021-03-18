<lib/prelude.pvs
#booleans
#equalities
#notequal
#if_def
#boolean_props
xor_def
quantifier_props
defined_types
exists1
equality_props
if_props
functions
## functions_alt only redefines some functions of the "functions" theory
## we skip it since we do not handle overloading
#functions_alt
transpose
restrict
restrict_props
extend
#extend_bool
extend_props
#extend_func_props
## K_conversion
#K_props
#identity
#identity_props
relations
orders
orders_alt
#restrict_order_props # Consist only of judgements
#extend_order_props   # Consist only of judgements
wf_induction
measure_induction
epsilons
decl_params
sets
#sets_lemmas # Module is nil, weird
function_inverse_def
function_inverse
# Requires `assuming' processing
#function_inverse_alt
function_image
#function_props # Translation fails because of resolution
function_props_alt
function_props2
relation_defs
relation_props
relation_props2
relation_converse_props
indexed_sets
operator_defs
numbers
number_fields
reals
real_axioms
bounded_real_defs
bounded_real_defs_alt
real_types
rationals
integers
naturalnumbers
min_nat
#real_defs # Error on application judgement
real_props
extra_real_props
extra_tegies
rational_props
integer_props
floor_ceil
#exponentiation # Contains a recursive function definition
euclidean_division
divides
modulo_arithmetic
subrange_inductions
bounded_int_inductions
bounded_nat_inductions
subrange_type
int_types
nat_types
nat_fun_props
finite_sets
restrict_set_props
extend_set_props
function_image_aux
function_iterate
sequences
seq_functions
#finite_sequences # Use dependent records
#more_finseq # Depends on finite_sequences
#ordstruct # Is a Datatype
#ordinals # Recursive function
#lex2 # Depends on ordinals
#lex3 # Depends on ordinals
#lex4 # Depends on ordinals
#list # Is a datatype
#list_props # Recursive function
map_props
more_map_props
#filters # Recursive functions
#list2finseq # Depends on list
#list2set # Recursive functions, depends on list
#disjointess # Recursive functions
#character # Is datatype
#strings # Depends on finite_sequence
#lift # Is a datatype
#union # Datatype
mucalculus
ctlops
fairctlops
#Fairctlops # Recursive functions
bit
bv
#exp2 # Recursive functions
bv_concat_def
bv_bitwise
#bv_nat # Recursive
empty_bv
bv_caret
mod
bv_arith_nat_defs
bv_int_defs
#bv_arithmetic_defs # Recursive functions
bv_extend_defs
integertypes
# infinite_sets_def # Macros
#finite_sets_of_sets # Recursive functions
EquivalenceClosure
QuotientDefinition
KernelDefinition
QuotientKernelProperties
QuotientSubDefinition
QuotientExtensionProperties
QuotientDistributive
QuotientIteration
#PartialFunctionDefinitions # Contains a record
#PartialFunctionComposition # Depends on previous thy