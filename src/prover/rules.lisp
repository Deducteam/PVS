;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rules.lisp -- 
;; Author          : N. Shankar
;; Created On      : Sat Oct 31 03:06:11 1998
;; Last Modified By: Sam Owre
;; Last Modified On: Sat Oct 31 03:10:45 1998
;; Update Count    : 1
;; Status          : Unknown, Use with caution!
;; 
;; HISTORY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package 'pvs)

(defmacro addrule (name required-args optional-args body docstring
			&optional format-string)
  `(let* ((entry (gethash ,name *rulebase*))
	  (form (cons ,name (append (quote ,required-args);;NSH(11.9.94)
				    (if (consp (quote ,optional-args))
					(if (eq (car (quote ,optional-args))
						'&rest)
					    (quote ,optional-args)
					    (cons '&optional
						  (quote ,optional-args)))
					nil))))
	  (docstr (format nil "~s: ~%    ~a" form
			  ,docstring))
	  )
     (cond ((null entry)
	    (add-symbol-entry ,name
			      (make-instance 'rule-entry
				'name ,name
				'required-args (quote ,required-args)
				'optional-args (quote ,optional-args)
				'rule-function 
				,(macroexpand
				  `(make-lambda-macro ,required-args
						      ,optional-args
						      ,body))
				'docstring docstr
				'format-string ,format-string)
			      *rulebase*)
	    (push ,name *rulenames*)
	    (push (cons ,name (make-prover-keywords
			       (append (quote ,required-args)
				       (quote ,optional-args))))
			*prover-keywords*)
	    #+lucid (record-source-file ,name 'strategy)
	    (format t "~%Added rule ~a.~%" ,name))
	   (t;;NSH(8-5)(y-or-n-p "Do you really want to change rule ~a?" ,name)
	    (setf (required-args entry) (quote ,required-args)
		  (optional-args entry) (quote ,optional-args)
		  (docstring entry) docstr
		  (format-string entry) ,format-string
		  (rule-function  entry)
		  ,(macroexpand `(make-lambda-macro ,required-args ,optional-args
						    ,body)))
	    (let ((old (assoc ,name *prover-keywords*)))
	      (if old
		  (setf (cdr old) (make-prover-keywords
			       (append (quote ,required-args)
				       (quote ,optional-args))))
		  (push (cons ,name (make-prover-keywords
			       (append (quote ,required-args)
				       (quote ,optional-args))))
			*prover-keywords*)))
	    #+lucid (record-source-file ,name 'strategy)
	    (format t "~%Changed rule ~a.~%" ,name))
	   (t (format t "~%No change.~%")))))

(defun internal-pc-typecheck (expr &key expected fnums
				   (context *current-context*)
				   (tccs nil given)
				   (uniquely? T))
  (let ((*generate-tccs* (if given tccs *generate-tccs*))
	(*current-context* context))
    (pc-typecheck expr :expected expected :fnums fnums
		  :uniquely? uniquely?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun sort-hashtable (htable &key key)
  (let ((list nil))
    (maphash #'(lambda (x y) (push y list)) htable)
    (sort list #'string< :key key)))

;;The help rule
(defun help-rule-fun (rule-name)
  #'(lambda (ps)
  (cond ((eq rule-name '*)
	 (funcall (help-rule-fun 'rules) ps)
	 (funcall (help-rule-fun 'defined-rules) ps)
	 (funcall (help-rule-fun 'strategies) ps))
	((eq rule-name 'rules)
	 (format t "~%~70,,,'-@a" "")
	 (format t "~%The rules (in alphabetical order) are: ~%")
	 (setq *rulenames* (sort *rulenames* #'string<))
	 (loop for rule-name in *rulenames*
	       do (format t "~%~a~%"
		    (docstring
		     (gethash rule-name *rulebase*)))))
	((eq rule-name 'defined-rules)
	 (format t "~%~70,,,'-@a" "")
	 (format t "~%The defined rules (in alphabetical order) are: ~%")
	 (loop for x in (sort-hashtable *rules* :key #'name)
	       unless (defhelper-entry? x)
	       do (format t "~%~a~%" (docstring x))))
	((eq rule-name 'strategies)
	 (format t "~%~70,,,'-@a" "")
	 (format t "~%The strategies (in alphabetical order) are: ~%")
	 (loop for x in (sort-hashtable *steps* :key #'name)
	       unless (or (defhelper-entry? x)
			  (defstep-entry? x))
	       do (format t "~%~a~%" (docstring x))))
	(t (let* ((rule-entry (gethash rule-name *rulebase*))
		  (defrule-entry (gethash rule-name *rules*))
		  (step-entry (gethash rule-name *steps*))
		  (entry (cond (rule-entry)(defrule-entry)(step-entry)(t nil))))
	     (if (null entry)
		 (format t "~%No such rule, defined rule or strategy.~%")
		 (format t "~%~a~%" (docstring entry))))))
  (values 'X nil nil)))

(addrule 'help () ((name  *) )
	 (help-rule-fun name) 
	 "Describes rule or all the rules but behaves like SKIP otherwise.
 (HELP <rule-or-strategy-name>) returns the help information for the
     given rule or strategy;
 (HELP rules) returns help for all the primitive commands;
 (HELP defined-rules) returns help for all the defined rules;
 (HELP strategies) returns help for all the strategies;
 (HELP) returns all of the above and should be avoided in
    favor of the Emacs command M-x help-pvs-prover.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;The failure rule
(defun failure-rule ()
  #'(lambda (ps)
      (declare (ignore ps))
      (values 'XX nil nil)))

(defun fail-rule ()
  (make-instance 'rule
    'rule-part #'failure-rule
    ))

(addrule 'fail nil nil (failure-rule)
	 "Signals a failure.  This is primarily used within strategies.
For example, a top-level strategy of the form (then (strat1)(fail))
applies strat1 and quits the proof unless strat1 completes the proof.
See the prover manual for more details.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;The skip rule, i.e. do nothing.
(defun skip ()
  #'(lambda (ps)
      (declare (ignore ps))
      (values 'X nil nil)))

(defun skip-rule ()
  (make-instance 'rule
    'rule-part #'skip))

(addrule 'skip nil nil (skip) "Does nothing.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;The postpone rule
(defun postpone (&optional print?)
  #'(lambda (ps)
      (declare (ignore ps))
      (format-if "~%Postponing ~a.~%" *label*)
      (values '* nil nil)))

(defun postpone-rule ()
  (make-instance 'rule
    'rule-part #'postpone
    ))

(addrule 'postpone nil (print?) (postpone)
	"Places current goal on parent's list of pending (unproved)
subgoals, moving to the next one.  Repeated POSTPONEs cycle through the
pending subgoals.  When PRINT? is T, commentary is suppressed." )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;The undo rule can take either a number, a label, or an input command
;;and it undoes the proof back to the appropriate point, and queries the
;;user.
;;NSH(8-14): Should I add an optional arg. indicating the number of
;;levels to be undone for a particular command input.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun undo (to)
  #'(lambda (ps) (undo1 to ps)))

(defun undo1 (to ps)
  (declare (ignore ps))
  (if (or (numberp to)
	  (stringp to)
	  (let ((name (if (consp to)(car to) to)))
	    (memq name (prover-commands)))) ;;NSH(7.25.94) using CRW's
					    ;;prover-commands. 
      (values to nil nil)
      (values 'X nil nil)))
	    
(addrule 'undo () ((to 1)) (undo to)
  "(undo <to[1]>): Undoes proof back n steps or to label,
command name, command")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun lisp-rule (lexp)
	 #'(lambda (ps)
	     (declare (ignore ps))
	     (format t "~%~s~%"  (eval lexp))
	     (values 'X nil nil)))

(addrule 'lisp (lexp) nil (lisp-rule lexp)
	 "(lisp <exp>):  Evaluates a Lisp expression.")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;The propositional axiom rule
(defun prop-axiom-rule ()
  #'(lambda (ps)
  (let ((s-forms (s-forms (current-goal ps))))
    (if (eq (check-prop-axiom s-forms) '!)
	(values '! nil) ;;( (substitution ps))
	(values 'X nil)))))

(defun negate (formula)
  (if (and (typep formula 'application)
	   (typep (operator formula) 'name-expr))
      (if (negation? formula)
	  (fstarg formula)
	  (make-negation formula))
      (make-negation formula)))

(defun check-prop-axiom (s-forms)
  (let ((forms (mapcar #'formula s-forms)))
    (check-prop-axiom* forms)))

(defun check-prop-axiom* (forms)
  (if (consp forms)
      (if (essentially-true? (car forms) (cdr forms))
	  '!
	  (check-prop-axiom* (cdr forms)))
      'X))

(defmethod essentially-true? ((form name-expr) remforms)
  (or (tc-eq form *true*)
      (member form remforms :test #'neg-tc-eq)))

(defmethod essentially-true? ((form negation) remforms)
  (with-slots (argument) form
    (or (tc-eq argument *false*)
	(member argument remforms :test #'tc-eq))))

(defmethod essentially-true? ((form equation) remforms)
  (with-slots (argument) form
    (or (apply #'tc-eq (exprs argument))
	(member form remforms :test #'neg-tc-eq))))

(defmethod essentially-true? ((form expr) remforms)
  (member form remforms :test #'neg-tc-eq))

(defmethod neg-tc-eq ((e1 expr) (e2 negation))
  (with-slots ((arg2 argument)) e2
    (tc-eq e1 arg2)))

(defmethod neg-tc-eq ((e1 expr) (e2 expr))
  nil)

(addrule 'propax nil nil (prop-axiom-rule)
	 "Checks if sequent has form ...,A |- ...A or ...|- a = a, ..., in
which case it considers the subgoal proved and moves to the next pending
(unproved) subgoal, if any.  If there are no more pending subgoals, the
proof is complete.  Note that this rule is processed automatically after
every proof step, and is rarely invoked by the user."
  "~%which is a propositional axiom.")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;delete rule: deletes a sequent formula. (NSH: 1/22/91)

(defun delete-rule-fun (sformnums)
  #'(lambda (ps)
      (let* ((goalsequent (current-goal ps))
	     (sformnums 
	      (loop for sf in sformnums
		    nconc (if (consp sf) sf (list sf)))))
	(multiple-value-bind
	      (signal subgoal)
	    (sequent-reduce goalsequent
			    #'(lambda (sform)
				(declare (ignore sform))
				(values '? nil))
			    sformnums)
	  (declare (ignore signal))
	  (values signal (list subgoal);;(substitution ps)
		  )))))


(addrule 'delete nil (&rest fnums)  (delete-rule-fun fnums)
	 "Deletes a list of formulas that may have become irrelevant.
The HIDE rule is a more conservative alternative, since hidden formulas
may be revealed.
See also HIDE, REVEAL"
	 "~%Deleting some formulas,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun apply-step (step &optional comment save? time?)
  #'(lambda (ps)
      (apply-step-body ps step comment save? time?)))

(defun apply-step-body (ps step comment save? time?)
  (let* ((*generate-tccs* 'NONE)
	 (strat (let ((*in-apply* ps));;NSH(8.22.94)
		  ;;otherwise (apply (query*)) misbehaves.
		  (strat-eval* step ps))))
    (cond ((or (typep strat 'strategy)
	       (typep strat 'rule-instance))
	   (let* ((new-strat
		   (if (typep strat 'strategy)
		       strat
		       (make-instance 'strategy
			 'topstep strat)))
		  (newps0 (copy ps
			    'strategy
			    new-strat
			    'parent-proofstate nil))
		  (newps (if (typep newps0 'top-proofstate)
			     (change-class newps0 'proofstate)
			     newps0))
		  (*noninteractivemode* t)
		  (*suppress-printing* t)
		  (*dependent-decls* nil)
		  (init-time (get-internal-run-time))
		  (result		;catch 'abort-in-apply ;;NSH(8.22.94)
		   (let ((*in-apply* ps)
			 )
		     (prove* newps)))
		  (end-time (/ (- (get-internal-run-time) init-time)
			       internal-time-units-per-second)))
                         ;;;;(break "in-apply")
	     ;;		 if (null result);;when aborted ;;NSH(8.22.94)
	     ;;		     if *in-apply*
	     ;;			 (throw 'abort-in-apply nil)
	     ;;			 (values 'X nil nil)
	     (let* ((subgoals (collect-subgoals newps))
		    (justif (collect-justification newps))
		    (xrule `(apply
				(rerun
				 ,(editable-justification
				   justif nil T)))))
	       ;; (format t "~%step= ~a~%decls = ~a" step *dependent-decls*)
	       (when time? (format t "~%;;;Used ~,2F seconds in ~s." end-time step))
	       (if (eq (status-flag newps) 'XX)
		   (values 'X nil nil);;was 'XX
		   (if (or (eq (status-flag newps) 'X)
			   (and (singleton? subgoals)
				(or (and (not (consp (car subgoals)))
					 (exequal (car subgoals)
						  (current-goal ps)))
				    (and (consp (car subgoals))
					 (exequal (caar subgoals)
						  (current-goal ps))
					 (eq
					  (nth 8 (car subgoals))
					;(nth 6 (car subgoals))
					  (current-auto-rewrites newps))))))
		       (if save?
			   (values '? (list (current-goal newps)) nil)
			   (values 'X nil nil))
		       (if (eq (status-flag newps) '!);;(null subgoals)
			   (values '! nil
				   (list 'dependent-decls
					 *dependent-decls*
					 'current-xrule
					 xrule))
			   (values '? subgoals
				   (list;;NSH(4.20.95)
				    ;;'dependent-decls
				    ;; *dependent-decls*
				    'current-xrule
				    xrule))))))))
	  (t (values 'X nil nil)))))

(defmethod collect-subgoals ((ps proofstate) &optional accum)
  (mapcar #'(lambda (x) (pushnew x *dependent-decls*))
			(dependent-decls ps))
  (cond ((and (eq (status-flag ps) '*)
	      (null (remaining-subgoals ps)))
	 (cond ((null (pending-subgoals ps))
		(cons (list (current-goal ps)
			    'alists (alists ps)
			    'dp-state (dp-state ps)
			    'context (context ps)
			    'current-auto-rewrites (current-auto-rewrites ps)
			    'subtype-hash (subtype-hash ps)
			    'rewrite-hash (rewrite-hash ps)
			    'dependent-decls *dependent-decls*
			    'comment (comment ps))
		      accum))
	       (t (collect-subgoals (nreverse (pending-subgoals ps))
				    accum))))
	(t (collect-subgoals (remaining-subgoals ps) accum))))

(defmethod collect-subgoals ((pslist list) &optional accum)
  (cond ((null pslist) accum)
	(t (collect-subgoals (car pslist)
			     (collect-subgoals (cdr pslist) accum)))))

			    
(addrule 'apply (strategy) (comment save? time?) (apply-step strategy comment save? time?) 
	 "Applies STRATEGY as if it were a rule, and prints COMMENT string.
If SAVE? is T, then the APPLY step is saved even if the strategy
does nothing, e.g., (SKIP), which is useful for setting values of
globals, e.g., (APPLY (LISP (setq *xx* ...)) \"recording value of *xx*\" T).
This is the basic way of converting a glass-box strategy into an
atomic step so that internal execution of the strategy is hidden
and only the resulting subgoals are returned.  E.g.,
 (apply (then (skosimp*)(flatten)(inst?))
      \"Skolemizing, flattening, and instantiating\")."
	 "~%Applying ~%   ~s,~@[~%~a~]")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(addrule 'split () ((fnum *) depth) ;; labels
	 (split-rule-fun fnum depth)
 "Conjunctively splits formula FNUM.  If FNUM is -, + or *, then
the first conjunctive sequent formula is chosen from the antecedent,
succedent, or the entire sequent.  Splitting eliminates any
top-level conjunction, i.e., positive AND, IFF, or IF-THEN-ELSE, and
negative OR, IMPLIES, or IF-THEN-ELSE."
"~%Splitting conjunctions,")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(addrule 'flatten () (&rest fnums) (flatten fnums)
; "Disjunctively simplifies chosen formulas.  It eliminates any
;top-level antecedent conjunctions, equivalences, and negations, and
;succedent disjunctions, implications, and negations from the sequent."
; "~%Applying disjunctive simplification to flatten sequent,")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'lift-if () (fnums (updates? T))  (liftif-step fnums updates?)
	 "Lifts IF occurrences to the top of chosen formulas.
CASES, COND, and WITH applications, are treated as IF occurrences.
The UPDATE? flag controls whether update-applications are converted
into IF-THEN-ELSE form and lifted.  IF-lifting is the transformation
that takes f(IF A THEN b ELSE c ENDIF) to
(IF A THEN f(b) ELSE f(c) ENDIF).  LIFT-IF only lifts the
leftmost-innermost contiguous block of conditionals  so it might
have to be applied repeatedly to lift all the conditionals. E.g.,
 (lift-if) : applies IF-lifting to every sequent formula.
 (lift-if - :updates? nil): lifts only antecedent IF that are not
  applications of updates."
	 "~%Lifting IF-conditions to the top level," )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(addrule 'lemma (name) (subst) (lemma-rule-fun name subst)
	 "Adds lemma named NAME as the first antecedent formula
 after applying the substitutions in SUBST to it.  Example:
  (LEMMA \"assoc\" (\"x\" 1 \"y\" 2 \"z\" 3))."
	 "~%Applying ~a ~@[where ~{~%  ~a gets ~a,~}~]")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(addrule 'typepred ()(&rest exprs) (typepred-fun exprs nil)
	 "Extract subtype constraints for EXPRS and add as antecedents.
 Note that subtype constraints are also automatically recorded by
the decision procedures. E.g.,
 (typepred \"abs(c)\"): Adds abs(c) > 0 to the antecedent."
	 "~%Adding type constraints for ~@{ ~a,~}")

(addrule 'typepred! (exprs)(all?) (typepred-fun exprs all?)
	 "Extract subtype constraints for EXPRS and add as antecedents.
ALL? flag when T also brings in integer_pred, rational_pred,
real_pred type constraints.  Note that subtype constraints are
also automatically recorded by the decision procedures. E.g.,
 (typepred! \"abs(c)\"): Adds abs(c) > 0 to the antecedent."
	 "~%Adding type constraints for ~a")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(addrule 'iff nil (&rest fnums)  (iff-rule-fun fnums)
	 "Converts top level Boolean equality into an IFF.
Otherwise, propositional simplification (other than by BDDSIMP)
is not applied to such equalities."
	 "~%Converting equality to IFF,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(addrule 'case nil (&rest formulas) (case-rule-fun formulas)
	 "Splits according to the truth or falsity of the formulas in FORMULAS.
 (CASE a b c) on a sequent A |- B generates subgoals:
 a, b, c, A  |- B;
   a, b, A |- c, B;
   a, A |- b, B;
   A |- a, B.
 See also CASE-REPLACE, CASE*"
	 "~%Case splitting on ~@{~%   ~a, ~}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'extensionality (type) nil (extensionality type)
	 "Adds extensionality axiom for given TYPE as a sequent formula.
 Example axioms for given type include:
  [nat->nat]: (FORALL (f, g: [nat->nat]): (FORALL (i:nat): f(i) = g(i))
                 IMPLIES f = g);
  [nat, nat]: (FORALL (r, s: [nat, nat]):
                PROJ_1(r) = PROJ_1(s) AND PROJ_2(r) = PROJ_2(s)
                IMPLIES r = s);
  [# a: nat, b: nat #]: (FORALL (r, s: [# a: nat, b: nat #]):
                           a(r) = a(s) AND b(r) = b(s) IMPLIES r = s)
  (cons?): (FORALL (l, m: (cons?)): car(l) = car(m) AND cdr(l) = cdr(m)
                                    IMPLIES l = m).
 See also ETA,  APPLY-EXTENSIONALITY and REPLACE-EXTENSIONALITY."

	 "~%Adding extensionality axioms for type: ~a,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'name (name expr) nil (add-name name expr)
	 "Introduces an EXPR = NAME premise.
Useful for generalizing the goal, and replacing exprs with bound
variables, so that the ground prover can be applied to them.
See also NAME-REPLACE"
	 "~%Letting ~a name ~a," )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'instantiate (fnum terms) (copy?)
	 (quant-rule-fun fnum terms copy?)
 "Instantiates the top quantifier in the formula FNUM with the TERMS.
FNUM can also be *, +, or -, in which case the first suitably quantified
formula is chosen for instantiation.  Each term in TERMS is typechecked
against the type of the variable it instantiates.  A copy of the
quantified formula is hidden by default and can be reintroduced by REVEAL.
If COPY? is T, then the copy is not hidden.  TERMS is a list of
expressions or underscores, corresponding to the bound variables of the
specified formula.  Underscores indicate that the corresponding variables
are to be left uninstantiated.
 Example: (instantiate 2 (\"x\" _ \"2\"))
   Instantiates the first and third bound variables in formula number 2.
 See also INST, INST?"
 "~%Instantiating the top quantifier in ~a with the terms: ~% ~a,")


(addrule 'skolem  (fnum constants) ()
	 (skolem-rule-fun fnum constants)
	 "Replaces the universally quantified variables in FNUM with new
skolem constants in CONSTANTS.
Example: (skolem 1 (\"A\" \"B\"))
See also SKOLEM!, SKOSIMP, SKOSIMP*."
"~%For the top quantifier in ~a, we introduce Skolem constants: ~a,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'reveal () (&rest fnums)
	 (reveal-step fnums)
	 "Moves the hidden formulas (hidden by HIDE or quantifier
instantiation) in FNUMS back to the sequent.  Use the Emacs command
M-x show-hidden-formulas to see the hidden formulas."
	 "~%Revealing hidden formulas,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'hide () (&rest fnums) (hide-step fnums)
	 "(hide <fnums>): Hides the formulas in FNUMS.
  See REVEAL and DELETE, and also the Emacs command M-x show-hidden-formulas."
	 "~%Hiding formulas: ~@{ ~a,~}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'replace (fnum) ((fnums *) dir hide? actuals?)
	 (replace-rule-fun fnum fnums dir hide? actuals?)
	 "Rewrites the given formulas in FNUMS with the formula FNUM.  If
FNUM is an antecedent equality, then it rewrites left-to-right if DIR is
LR (the default), and right-to-left if DIR is RL.  If FNUM is not an
antecedent equality, then any occurrence of the formula FNUM in FNUMS is
replaced by TRUE if FNUM is an antecedent, FALSE for a succedent.  If
HIDE? is T, then FNUM is hidden afterward.  When ACTUALS?  is T, the
replacement is done within actuals of names in addition to the expression
level replacements."
	 "~%Replacing using formula ~a,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'beta ()((fnums *) rewrite-flag)
	 (beta-step fnums rewrite-flag)
 "Beta-reduces chosen formulas. If REWRITE-FLAG is LR(RL), then
left(right)-hand-side is left undisturbed for rewriting using
REWRITE and REWRITE-LEMMA.  Example reduction steps are:
 (LAMBDA x, y: x + y)(2, 3) to 2 + 3
 (LET x := 1, y := 2 in x + y) to 1 + 2
 b((# a:=1, b:= 2 #)) to 2
 PROJ_2(2, 3) to 3
 cons?(nil) to FALSE
 car(cons(2, nil)) to 2." 
	 "~%Applying beta-reduction,")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(addrule 'simplify
	 ()
	 ((fnums *) record? rewrite? 
	   rewrite-flag flush? linear? cases-rewrite? (type-constraints? T)
	   ignore-prover-output?
	   ;(assert-connectives? T)
	   )
	 (invoke-simplification fnums record? rewrite?
				rewrite-flag flush? linear?
				cases-rewrite? type-constraints?
				ignore-prover-output?
				;assert-connectives?
				)
	 "Uses the decision procedures to to simplify the formulas in
FNUM and record them for further simplification.  The proof steps
ASSERT, RECORD, SIMPLIFY, DO-REWRITE are instances of this primitive
rule and should always be preferred.  The arguments have the following
effect:
 RECORD?: If T, the formula is simplified and recorded as true or false
          by the decision procedures to be used for further
          simplification.  The formula is only recorded if it does not
          contain top-level Boolean connectives or conditionals.
 REWRITE?: If T, the installed rewrite rules are applied but no
          simplification is done except on the right-hand side.
          Full-blown simplify is used to simplify the right-hand side
          instance of the rewrite, the TCCs, and the conditions of
          conditional rewrite rules.
 If  REWRITE? is NIL the formula is simplified so that
    1. arithmetic expressions are put into a sum-of-products form.
    2. lambda, tuple, record, datatype, and update redexes are reduced.
    3. decision procedures are used to determine whether boolean
       expressions are TRUE/FALSE in the context in which they appear.
    3. Boolean/conditional expressions are simplified to eliminate
       TRUE/FALSE.
 REWRITE-FLAG: If RL(LR) then only lhs(rhs) is simplified.
 FLUSH?: If T, then the current asserted facts are deleted for
         efficiency.
 LINEAR?: If T, then multiplication and division are uninterpreted.
 CASES-REWRITE: If T, then the selections and else parts of a
         CASES expression are simplified, otherwise, they are only
         simplified when simplification selects a case.
 TYPE-CONSTRAINTS?: IF T (the default) asserts subtype constraints of each
         sub-expression to the ground prover data-structures.
 IGNORE-PROVER-OUTPUT?: The ground prover returns a disjunction of literals
         equivalent to the asserted formula.  At the end of a SIMPLIFY with
         RECORD? set to T, PVS tries to show that the conjunction of these
         disjunctions is unsatisfiable using the ground prover.  This step
         can sometimes be expensive and fruitless, and setting
         IGNORE-PROVER-OUTPUT? to T, cases this step to be skipped." 
	 "~%Simplifying with decision procedures,")

(addrule 'auto-rewrite () (&rest names) (auto-rewrite-step names)
	 "Installs automatic rewrite rules given in the NAMES list.
The rewrites are applied by the ASSERT and DO-REWRITE commands.
Each entry in the list NAMES is either an antecedent formula number or
names a definition, assumption or
lemma/theorem/formula/proposition/conjecture, or a list of such
to indicate eager and macro rewrites (as explained below).
In (AUTO-REWRITE A (B C) D ((E F))), B and C are eager rewrites,
E and F are macro rewrites, and A and D are lazy rewrites. 
Rewrites only take effect if relevant conditions and TCCs simplify to T.
For lazy rewrites, if there is an IF or CASES at the outermost part of the
righthand-side, then it is treated as a condition.  When a function
definition is curried, lazy and eager rewrites only match when
the most applied form of the function is used, whereas macros
always match any occurrence of the function. 
  E.g.,
  (auto-rewrite \"assoc\" (\"delete\" \"union\") -3 (-4 -5))
  (auto-rewrite :names (\"assoc\" (\"delete\" \"union\"))). "
	 "~%Installing automatic rewrites from: ~@{~%  ~a~}")



;(addrule 'auto-rewrite! () (&rest names)(auto-rewrite-step names T)
;	 " Similar to auto-rewrite except that the rewrites of lemmas and
;explicit (non-recursive) definitions always occur independent of the
;righthand-side."
;	 "~%Installing automatic rewrites: ~@{~%  ~a,~}")
;
;(addrule 'auto-rewrite-theory (name) (defs-only? always?)
;	 (auto-rewrite-theory name defs-only? always?)
;	 "Installs an entire theory (or only definition if DEF-ONLY? is T)
;as rewriters.  If ALWAYS? is T the rewrites are installed
;to so that any rewrite other than a recursive defn. always takes
;effect (see auto-rewrite!)."
;	 "~%Rewriting relative to the theory: ~a,")

(addrule 'stop-rewrite () (&rest names) (stop-rewrite-step names)
	 "Turns off automatic rewriting.  Disables all rewrites if no
arguments are given.  Disabled rewrites have to be enabled by
AUTO-REWRITE, AUTO-REWRITE!, or AUTO-REWRITE-THEORY. E.g.,
 (stop-rewrite \"assoc\" \"delete\"). "
 "~%Turning off ~#[all auto-rewrites~;automatic rewriting for: ~@{~%   ~a,~}~]")

;(addrule 'stop-rewrite-theory () (&rest names) (stop-rewrite-theory names)
;	 "Turns off rewriting for a theory."
;	 "~%Turning off automatic rewriting for theories: ~@{~%   ~a,~}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(addrule 'expand (function-name)
	 ((fnum *) occurrence if-simplifies assert?)
	 (expand function-name fnum occurrence if-simplifies assert?)
 "Expands (and simplifies) the definition of FUNCTION-NAME at a given
OCCURRENCE.  If no OCCURRENCE is given, then all instances of the
definition are expanded.  The OCCURRENCE is given as a number n
referring to the nth occurrence of the function symbol counting
from the left, or as a list of such numbers.  If the IF-SIMPLIFIES
flag is T, then any definition expansion occurs only if the RHS
instance simplifies (using the decision procedures).  Note that the
EXPAND step also applies simplification with decision procedures
(i.e. SIMPLIFY with default options) to any sequent formulas where
an expansion has occurred.  (In Release 1.x, ASSERT was applied to
any formula affected by EXPAND, but this has changed in Release 2.0.
To regain compatibility, the ASSERT? flag can be set to T.)
ASSERT? can be either NONE (meaning no simplification),
NIL (meaning simplify using SIMPLIFY), or T (meaning simplify using
ASSERT).  Another change is that the HASH-REWRITES? flag has also been
removed since all rewrites are now hashed for efficiency.)"
 "~%Expanding the definition of ~a,")


(addrule 'same-name (name1 name2)
	 (type)
	 (same-name name1 name2 type)
	 "Assume given constants are identical if their actuals are equal.
This is used to indicate that names are equal even if their actuals are
not syntactically equal.  TYPE can be given to disambiguate NAME1 and
NAME2.
Example: (same-name \"bvec0[i + j]\" \"bvec0[j + i]\")."
	 "By checking name equality between  ~a and ~a")
	 

(defun same-name (name1 name2 &optional type)
  #'(lambda (ps)
      (let* ((type (when type
		     (typecheck (pc-parse type 'type-expr)
		       :tccs 'ALL)))
	     (name1 (internal-pc-typecheck (pc-parse name1 'expr)
			  :expected type
			  :tccs 'ALL))
	     (name2 (internal-pc-typecheck (pc-parse name2 'expr)
			  :expected type
			  :tccs 'ALL)))
	(cond ((not (name-expr? name1))
	       (error-format-if "~%Argument ~a is not a name." name1)
	       (values 'X nil nil))
	      ((not (name-expr? name2))
	       (error-format-if "~%Argument ~a is not a name." name2)
	       (values 'X nil nil))
	      ((null (type name1))
	       (error-format-if "~%Argument ~a does not typecheck uniquely."
			  name1)
	       (values 'X nil nil))
	      ((null (type name2))
	       (error-format-if "~%Argument ~a does not typecheck uniquely."
			  name2)
	       (values 'X nil nil))
	      ((null (actuals name1))
	       (error-format-if "~%Argument ~a must have actuals." name1)
	       (values 'X nil nil))
	      ((null (actuals name2))
	       (error-format-if "~%Argument ~a must have actuals." name2)
	       (values 'X nil nil))
	      ((eq (id name1)(id name2))
	       (mapcar #'(lambda (x)
			   (mapcar #'(lambda (y) (push y *tccforms*))
				   x))
		       (check-actuals-equality name1 name2))
	       (let ((new-subgoal (lcopy (current-goal ps)
				    's-forms
				    (cons (make-instance 's-formula
					    'formula
					    (make-negation
					     (make-equality name1 name2)))
					  (s-forms (current-goal ps))))))
		 (values '? (list new-subgoal))))
	      (t (error-format-if "Arguments ~a and ~a must have identical ~
identifiers" name1 name2)
	       (values 'X nil nil))))))

(addrule 'label (label fnums) (push?)  (label-step label fnums push?)
	 "Labels a collection of formulas given by FNUMS by the
string  LABEL.  If PUSH? is T, then the new label is added to any existing
ones.  Otherwise, the new labels replaces all existing ones."
	 "Labelling formulas ~a by ~a")

(addrule 'just-install-proof (proof) ()
	 #'(lambda (ps)
	     (just-install-proof-step proof ps))
	 "Installs an edited PROOF without actually checking it,
declares the subgoal as finished, but then marks the proof as
unfinished."
	 "Installing without checking, the proof ~a")

(addrule 'comment (string) () (comment-step string)
	 "Adds a comment to the sequent."
	 "Adding comment: ~a")

(addrule 'flatten-disjunct () (fnums depth) (flatten fnums depth)
 "Disjunctively simplifies chosen formulas.  It simplifies 
top-level antecedent conjunctions, equivalences, and negations, and
succedent disjunctions, implications, and negations from the sequent.
The DEPTH argument can either be a non-negative integer indicating
the nesting of top-level disjunctions to be elimnated, or NIL
which eliminates all top-level disjuncts in the indicated FNUMS."
 "~%Applying disjunctive simplification to flatten sequent,")
