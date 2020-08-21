/* 

Interface for the Mu-calculus model-checker.
Author: Hassen Saidi, Sam Owre, and Dave Stringer-Calvert
Date: 05/09/98

*/

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


/*

#include <stdio.h>

#include "alloc.h"
#include "hash.h"  */

#include "bdd_fns.h" 
#include "mu.h"

#include <setjmp.h> /* For interrupt handling */

#include <signal.h>

#ifdef __linux__
// GLIBC 2.11 includes __longjmp_chk, not defined in earlier versions
__asm__(".symver __longjmp_chk,siglongjmp@GLIBC_2.2.5");
#endif

int __attribute__ ((aligned (16))) bdd_interrupted = 0;
sigjmp_buf bddcatch;
struct sigaction lisp_handler;
void restore_sigint(void);

void new_handler(int sig)
{
  restore_sigint();
  siglongjmp(bddcatch, -1);
}

void
set_sigint(void)		   
{
  struct sigaction new;
  sigset_t mask;

  /* setup new signal handling struct */
  new.sa_handler = new_handler;
  new.sa_flags = 0;
#ifdef SA_RESTART
  new.sa_flags |= SA_RESTART;
#endif
#ifdef SA_INTERRUPT
  new.sa_flags &= ~ SA_INTERRUPT;
#endif
  sigemptyset(&mask); 
  new.sa_mask = mask;

  /* install our signal handler, saving detail of lisp one */
  if (sigaction(SIGINT, &new, &lisp_handler) < 0)
    perror("sigaction in set_sigint");
}

void
restore_sigint(void)
{
  if (sigaction(SIGINT, &lisp_handler, NULL) < 0)
    perror("sigaction in restore_sigint");
}


extern int debug;
extern int warnings;
int negate = 0;
/*
#define ODD(n)			((n)  & 1)
#define MUL2(n)			((n) << 1)
*/

#define DIV2(n)			((n) >> 1)
/*
#define VAR_ID_2_BDD_IDX(i)	MUL2(i-1)
*/

#define BDD_IDX_2_VAR_ID(b)	(DIV2(b)+1)

/*
#define PHV_ID_2_BDD_IDX(i)	(MUL2(i) | 1)  
#define BDD_IDX_2_PHV_ID(b)	DIV2(b)        
*/

/* dummy definitions */
void yyerror (const char *format, ...) { fputs ("", stderr); } 
void yywarning (const char *format, ...) { fputs ("", stderr); } 
//static const char *bdd_output_strings ;

/* setting flags */
int set_mu_warnings           (int flag) {warnings = flag; return 0;}
int set_mu_simplify_frontier  (int flag) {mu_simplify_frontier = flag; return 0;}
int set_mu_verbose            (int flag) {mu_verbose = flag; return 0;}



/* mk Terms and Formulas  */

Term mu_mk_not_term (Term fml1)
 {  return mu_mk_unary_term  (MU_T_NOT, fml1);}

Formula mu_mk_not_formula (Formula fml1)
 {  return mu_mk_unary_formula  (MU_NOT, fml1);}

Term mu_mk_and_term (Term fml1, Term fml2)
 {  return mu_mk_binary_term  (MU_T_AND, fml1, fml2);}

Formula mu_mk_and_formula (Formula fml1, Formula fml2)
 {  return mu_mk_binary_formula (MU_AND, fml1, fml2);}

Term mu_mk_or_term (Term fml1, Term fml2)
 {  return mu_mk_binary_term  (MU_T_OR, fml1, fml2) ;}

Formula mu_mk_or_formula  (Formula fml1, Formula fml2)
 {  return mu_mk_binary_formula  (MU_OR, fml1, fml2);}

Term mu_mk_equiv_term (Term fml1, Term fml2)
 {  return mu_mk_binary_term  (MU_T_EQUIV, fml1, fml2);}

Formula mu_mk_equiv_formula (Formula fml1, Formula fml2)
 {  return mu_mk_binary_formula  (MU_EQUIV, fml1, fml2);}

Term mu_mk_implies_term (Term fml1, Term fml2)
 {  return mu_mk_binary_term  (MU_T_IMPLIES, fml1, fml2);}

Formula mu_mk_implies_formula (Formula fml1, Formula fml2)
 {  return mu_mk_binary_formula  (MU_IMPLIES, fml1, fml2);}

Formula mu_mk_cofactor (Formula fml1 , Formula fml2)
 {  return mu_mk_binary_formula  (MU_COFACTOR, fml1, fml2);}

Formula mu_mk_forall (LIST listvars, Formula fml)
 {  return mu_mk_quantified_formula (MU_UNIV, listvars, fml);}

Formula mu_mk_exists (LIST listvars, Formula fml)
 {  return mu_mk_quantified_formula (MU_EXIST, listvars, fml);} 

Formula mu_mk_curry_application (Term fml1, LIST listargs)
 {  return  mu_mk_application (fml1, listargs, 0) ;}


Term mu_mk_l_fixed_point (int relvar , Term fml1)
 {  return mu_mk_fixed_point (MU_L_FIXED_POINT, Ip, relvar, fml1, INT_MAX);}

Term mu_mk_g_fixed_point (int relvar, Term fml1)
 {  return mu_mk_fixed_point (MU_G_FIXED_POINT, Ip, relvar, fml1, INT_MAX);}
/*
Make bool variables
*/

Term mu_mk_rel_var_ (char *name)
{return mu_mk_rel_var (Ip,name);}

Formula mu_check_mk_bool_var (char *name)
 { Formula R ;
  mu_check_bool_var (name) ; 
  R = mu_mk_bool_var (name) ; 
  return R;
 }

LIST empty_list ()
{return NULL_LIST;}

/* returns the name of a boolean variable */
const char* get_mu_bool_var_name (int bdd_idx)
{   return (mu_bool_var_name (BDD_IDX_2_VAR_ID (bdd_idx))) ; }


/*
Main function
*/ 

  FILE *mu_output_stream ;
//FILE *bdd_output_stream; 

  extern char *optarg;
  extern int opterr;
  extern int optind;
//extern FILE *freopen ();
  int option;
  extern int yyparse ();
/*  extern int yylineno = 0;  */

BDDPTR mu___modelcheck_formula (Formula fml)
 { auto int return_value;
   extern BDDPTR modelcheck_formula();
   BDDPTR mcvalue;

   bdd_interrupted = 0;
   if ((return_value = sigsetjmp(bddcatch,1)) != 0) {
     bdd_interrupted = 1;
     restore_sigint();
     return BDD_0;
   }

   set_sigint();
   mcvalue = modelcheck_formula(fml);
   restore_sigint();
   return mcvalue;
 }

BDD_LIST bdd___bdd_sum_of_cubes (BDDPTR f, int irredundant)
 { auto int return_value;
   extern BDD_LIST bdd_sum_of_cubes();
   BDD_LIST mcvalue;

   bdd_interrupted = 0;
   if ((return_value = sigsetjmp(bddcatch,1)) != 0) {
     bdd_interrupted = 1;
     restore_sigint();
     return NULL_LIST;
   }
   
   set_sigint();
   mcvalue = bdd_sum_of_cubes (f, irredundant);
   restore_sigint();
   return mcvalue;
 }

BDDPTR modelcheck_formula (Formula fml)
 { BDDPTR R;
   bdd_use_neg_edges = 1;
   bdd_do_dynamic_ordering = 1;
   bdd_do_gc  = 1;
   bdd_use_inv_edges = 0;
   mu_verbose = 1;  /* 1 */
   mu_echo = 1;  /* 1 */
   mu_use_and_smooth = 1;
   
     fprintf (stdout, "  \n");  
     mu_print_formula_infix (stdout, fml); 
     fprintf (stdout, ";\n ");  
     fflush (stdout);
   
   R = mu_interpret_formula (fml, Ip, NULL);
   mu_free_formula(fml);
 /*   bdd_print_as_sum_of_cubes (stdout, R,0) ; */
   if (mu_verbose) {
    fprintf (stdout, "Formula amounts to %d BDD nodes.\n", BDD_bdd_size (R));
    fflush (stdout);
   }
 return R;
 }

void pvs_mu_print_formula (Formula fml)
{mu_print_formula_infix (stdout, fml);
 fflush (stdout);  
}

void pvs_mu_print_term (Term t)
{mu_print_term_infix (stdout, t);
 fflush (stdout);  
}
