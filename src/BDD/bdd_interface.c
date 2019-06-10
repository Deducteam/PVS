/* -------------------------------------------------------------------- */
/* PVS */
/* Copyright (C) 2006, SRI International.  All Rights Reserved. */

/* This program is free software; you can redistribute it and/or */
/* modify it under the terms of the GNU General Public License */
/* as published by the Free Software Foundation; either version 2 */
/* of the License, or (at your option) any later version. */

/* This program is distributed in the hope that it will be useful, */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the */
/* GNU General Public License for more details. */

/* You should have received a copy of the GNU General Public License */
/* along with this program; if not, write to the Free Software */
/* Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA. */
/* -------------------------------------------------------------------- */
#include <stdio.h>

#include "bdd_fns.h"

int debug = 0;
int warnings = 1;

/* Make list macros available */
int null_list_p (LIST x) { return x == NULL; }
void *elem_contents (LIST_ELEM_PTR x) { return ELEM_CONTENTS (x); }
LIST_ELEM_PTR list_first (LIST x) { return LIST_FIRST (x); }
LIST_ELEM_PTR list_last (LIST x) { return LIST_LAST (x); }
int list_info (LIST x) { return LIST_INFO (x); }
LIST_ELEM_PTR list_next (LIST_ELEM_PTR x) { return LIST_NEXT (x); }

/* Provide a means for setting global variables */
void set_bdd_do_gc (int flag) { bdd_do_gc = flag; }
void set_bdd_do_dynamic_ordering (int flag) { bdd_do_dynamic_ordering = flag; }
void set_bdd_verbose (int flag) { bdd_verbose = flag; }
void set_bdd_use_neg_edges (int flag) { bdd_use_neg_edges = flag; }
void set_bdd_use_inv_edges (int flag) { bdd_use_inv_edges = flag; }


unsigned int bdd_varid (BDDPTR f) { return BDD_VARID (f); }

int bdd_0_p (BDDPTR f) { return BDD_0_P (f); }
int bdd_1_p (BDDPTR f) { return BDD_1_P (f); }
int bdd_x_p (BDDPTR f) { return BDD_X_P (f); }
int bdd_term_p (BDDPTR f) { return BDD_TERM_P (f); }
int bdd_lit_p (BDDPTR f) { return BDD_LIT_P (f); }
BDDPTR bdd_cofactor_pos_ (BDDPTR f) { return BDD_COFACTOR_POS (f); }
BDDPTR bdd_cofactor_neg_ (BDDPTR f) { return BDD_COFACTOR_NEG (f); }


BDD_LIST bdd_sum_of_cubes (BDDPTR f, int irredundant)
{
  if (BDD_VOID_P (f))
    return NULL_LIST;
  
  return irredundant ? bdd_irredundant_sum_of_cubes_as_list (f)
	             : bdd_sum_of_cubes_as_list (f);
  
}

