;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; makes.lisp -- 
;; Author          : Harald Ruess
;; Created On      : Tue Jan  4 23:17:39 1999
;; Last Modified By: Harald Ruess
;; Last Modified On: Thu Nov  5 15:11:36 2001
;; Update Count    : 27
;; Status          : Unknown, Use with caution!
;; 
;; HISTORY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :pvs)

;; Translation of PVS formulas to deterministic finite automata;

; Messages

(defmacro ws1s-msg (str &rest args)
  `(locally (declare (special *verbose*))
      (when *verbose*
        (format t ,str ,@args))))

;; WS1S type declarations

(defun ws1s-types ()
  (list *boolean* *naturalnumber* (fset-of-nats)))
  
(defun ws1s-type? (type)
  (member type (ws1s-types) :test #'tc-eq))

(defun first-order? (expr)
  (some #'(lambda (type)
	    (subtype-of? type *naturalnumber*))
	(judgement-types+ expr)))

(defun second-order? (expr)
  (some #'(lambda (type)
	    (subtype-of? type (fset-of-nats)))
	(judgement-types+ expr)))

(defun level (expr)
  (cond ((tc-eq (type expr) *boolean*) 0)
	((first-order? expr) 1)
	((second-order? expr) 2)))


;; Generating new indices

(let ((*index* 0))

  (defun fresh-index ()
    (setf *index* (1+ *index*)))

  (defun reset-index ()
    (setf *index* 0)))

;; Lookup from substitutions for both bound and free variables

(defun lookup (expr free)
  (declare (special *boundvars*))
  (cdr (or (assoc expr *boundvars* :test #'tc-eq)
	   (assoc expr free :test #'tc-eq))))

(defun var1? (expr free)
  (and (first-order? expr)
       (or (lookup expr free)
	   (name-expr? expr))))

(defun lookup-var1 (expr free)
  (let ((index (lookup expr free)))
    (if index
	(values index free)
      (let ((index (fresh-index)))
	(values index (acons expr index free))))))

(defun var2? (expr free)
  (and (second-order? expr)
       (or (lookup expr free)
	   (name-expr? expr))))

(defun lookup-var2 (expr free)
  (let ((index (lookup expr free)))
    (if index
	(values index free)
      (let ((index (fresh-index)))
	(values index (acons expr index free))))))


;; Translation of formulas has a formula argument, the currently set of bound variables,
;; and the current symbol table; the result is an automaton or nil if the formula is not
;; a translatable formula.

(defun fmla-to-dfa (fml)
  (catch 'not-ws1s-translatable
    (progn 
      (multiple-value-bind (dfa free)
	  (let ((*boundvars* nil))
	    (declare (special *boundvars*))
	    (fmla-to-dfa* fml nil))
	(values (dfa-unrestrict dfa) free)))))
       
(defmethod fmla-to-dfa* ((fml expr) free)
  (atom-to-dfa* fml free))

(defmethod fmla-to-dfa* ((fml name-expr) free)
  (cond ((tc-eq fml *true*)
	 (values (dfa-true) free))
	((tc-eq fml *false*)
	 (values (dfa-false) free))
	(t
	 (call-next-method))))

(defmethod fmla-to-dfa* ((fml negation) free)
  (multiple-value-bind (dfa new-free)
      (fmla-to-dfa* (args1 fml) free)
    (values (dfa-negation dfa) new-free)))

(defmethod fmla-to-dfa* ((fml conjunction) free)
   (fmla-binary-connective-to-dfa* fml #'dfa-conjunction free))

(defmethod fmla-to-dfa* ((fml disjunction) free)
   (fmla-binary-connective-to-dfa* fml #'dfa-disjunction free))

(defmethod fmla-to-dfa* ((fml implication) free)
   (fmla-binary-connective-to-dfa* fml #'dfa-implication free))

(defmethod fmla-to-dfa* ((fml iff-or-boolean-equation) free)
   (fmla-binary-connective-to-dfa* fml #'dfa-iff free))

(defun fmla-binary-connective-to-dfa* (fml operator free)
  (multiple-value-bind (dfa1 free1)
      (fmla-to-dfa* (args1 fml) free)
    (multiple-value-bind (dfa2 free2)
	(fmla-to-dfa* (args2 fml) free1)
      (values (funcall operator dfa1 dfa2) free2))))

(defmethod fmla-to-dfa* ((fml disequation) free)
  (fmla-to-dfa*
   (make!-negation (make!-equation (args1 fml) (args2 fml)))
   free))

(defmethod fmla-to-dfa* ((fml forall-expr) free)
  (fmla-to-dfa*
   (make!-negation
    (make!-exists-expr (bindings fml)
		       (make!-negation (expression fml))))
   free))

(defmethod fmla-to-dfa* ((fml exists-expr) free)
  (declare (special *boundvars*))
  (multiple-value-bind (vars types preds)
      (destructure-bindings (bindings fml) :exclude (ws1s-types))
    (if (some #'(lambda (type)
		   (not (member type (ws1s-types) :test #'tc-eq)))
	       types)
	(call-next-method)
      (let ((indices (loop for var in vars collect (fresh-index)))
	    (levels (loop for type in types
			  collect (cond ((tc-eq type *boolean*) 0)
					((tc-eq type *naturalnumber*) 1)
					((tc-eq type (fset-of-nats)) 2)))))
	(setf *boundvars* (append (pairlis vars indices) *boundvars*))
	(multiple-value-bind (dfa-body new-free)
	    (fmla-to-dfa* (make!-conjunction (make!-conjunction* preds)
					     (expression fml))
			  free)
	  (values (dfa-exists* levels indices dfa-body)
		  new-free))))))

; Each atom is translated by first translating its arguments. Translation
; of an arithmetic arguments yields an index, a set of variables to be
; quantified existentially, a set of constraints, and a set of new substitutions.

(defmethod atom-to-dfa* ((atom expr) free)
  (declare (ignore free))
  (throw 'not-ws1s-translatable nil))

(defmethod atom-to-dfa* ((atom name-expr) free)
  (let ((index (lookup atom free)))
    (if index
	(values (dfa-var0 index) free)
      (let ((index (fresh-index)))
	(values (dfa-var0 index)
		(acons atom index free))))))

(defmethod atom-to-dfa* ((atom equation) free)
  (let ((lhs (args1 atom))
	(rhs (args2 atom)))
    (cond ((var1? lhs free)
	   (multiple-value-bind (i new-free)
	       (lookup-var1 lhs free)
	     (var1-eq-term1-to-dfa* i rhs new-free)))
	  ((var1? rhs free)
	   (multiple-value-bind (i new-free)
	       (lookup-var1 rhs free)
	     (var1-eq-term1-to-dfa* i lhs new-free)))
	  ((var2? lhs free)
	   (multiple-value-bind (i new-free)
	       (lookup-var2 lhs free)
	     (var2-eq-term2-to-dfa* i rhs new-free)))
	  ((var2? rhs free)
	   (multiple-value-bind (i new-free)
	       (lookup-var2 rhs free)
	     (var2-eq-term2-to-dfa* i lhs new-free)))
	  (t
	   (call-next-method)))))

(defun var1-eq-term1-to-dfa* (i term1 free)
  (cond ((natural-number-expr? term1)                       ; p_i = n
	 (values (dfa-const (number term1) i) free))
	((var1? term1 free)                                 ; p_i = p_j
	 (multiple-value-bind (j new-free)
	     (lookup-var1 term1 free)
	   (values (dfa-eq1 i j) new-free)))
	((and (application? term1)                          ; p_i = p_j + n
              (tc-eq (operator term1) (plus-operator))    
	      (var1? (args1 term1) free)
	      (natural-number-expr? (args2 term1)))
	 (multiple-value-bind (j new-free)
	     (lookup-var1 (args1 term1) free)
	   (values (dfa-plus1 i j (number (args2 term1))) new-free)))
	((and (application? term1)
              (tc-eq (operator term1) (plus-operator))      ; p_i = n + p_j
	      (var1? (args2 term1) free)
	      (natural-number-expr? (args1 term1)))
	 (multiple-value-bind (j new-free)
	     (lookup-var1 (args2 term1) free)
	   (values (dfa-plus1 i j (number (args1 term1))) new-free)))
	((and (application? term1)
              (tc-eq (operator term1) (minus-operator))     ; p_i = p_j - n
	      (var1? (args1 term1) free)
	      (natural-number-expr? (args2 term1)))
	 (multiple-value-bind (j new-free)
	     (lookup-var1 (args1 term1) free)
	   (values (dfa-minus1 i j (number (args2 term1))) new-free)))
	(t
	 (throw 'not-ws1s-translatable nil))))
  
  
(defun var2-eq-term2-to-dfa* (i term2 free)
  (cond ((tc-eq (emptyset-operator) term2)                    ; P_i = emptyset
	 (values (dfa-empty i) free))
	((var2? term2 free)                                   ; P_i = P_j
	 (multiple-value-bind (j new-free)
	     (lookup-var2 term2 free)
	   (values (dfa-eq2 i j) new-free)))
	((and (application? term2)
	      (tc-eq (union-operator) (operator term2)))      
	 (let ((lhs (args1 term2))
	       (rhs (args2 term2)))
	   (cond ((and (tc-eq (emptyset-operator) lhs)         ; P_i = empty union empty
		       (tc-eq (emptyset-operator) rhs))
		  (values (dfa-empty i) free))
		 ((and (tc-eq (emptyset-operator) lhs)         ; P_i = empty union P_k
		       (var2? rhs free))
		  (multiple-value-bind (k new-free)
		      (lookup-var2 rhs free)
		    (values (dfa-eq2 i k) new-free)))
		 ((and (tc-eq (emptyset-operator) rhs)         ; P_i = P_j union empty
		       (var2? lhs free))
		  (multiple-value-bind (j new-free)
		      (lookup-var2 lhs free)
		    (values (dfa-eq2 i j) new-free)))
		 ((and (var2? lhs free)                        ; P_i = P_j union P_k
		       (var2? rhs free))
		  (multiple-value-bind (j new-free)                    
		      (lookup-var2 lhs free)
		    (multiple-value-bind (k new-new-free)
			(lookup-var2 rhs new-free)
		      (values (dfa-union i j k) new-new-free))))
		 (t
		  (throw 'not-ws1s-translatable nil)))))
	((and (application? term2)
	      (tc-eq (intersection-operator) (operator term2)))
	 (let ((lhs (args1 term2))
	       (rhs (args2 term2)))
	   (cond ((or (tc-eq (emptyset-operator) lhs)       ; P_i = _ inter empty, P_i = empty inter _  
		      (tc-eq (emptyset-operator) rhs)) 
		  (values (dfa-empty i) free))
		 ((and (var2? (args1 term2) free)           ; P_i = P_j inter P_k
		       (var2? (args2 term2) free))
		  (multiple-value-bind (j new-free)
		      (lookup-var2 (args1 term2) free)
		    (multiple-value-bind (k new-new-free)
			(lookup-var2 (args2 term2) new-free)
		      (values (dfa-intersection i j k) new-new-free))))
		 (t
		  (throw 'not-ws1s-translatable nil)))))
	(t
	 (throw 'not-ws1s-translatable nil))))

(defmethod atom-to-dfa* ((fml application) free)
  (let ((op (operator fml))
	(args (arguments fml)))
    (cond ((= (length args) 1)                                  ; P_j(p_i)
	   (term1-in-term2-to-dfa* (first args) op free))
	  ((tc-eq op (less-operator))                           ; p_i < p_j
	   (term1-binrel-term1-to-dfa* (args1 fml) (args2 fml) #'dfa-less free))
	  ((tc-eq op (lesseq-operator))                         ; p_i <= p_j
	   (term1-binrel-term1-to-dfa* (args1 fml) (args2 fml) #'dfa-lesseq free))
	  ((tc-eq op (greater-operator))                        ; p_i > p_j
	   (term1-binrel-term1-to-dfa* (args1 fml) (args2 fml) #'dfa-greater free))
	  ((tc-eq op (greatereq-operator))                      ; p_i >= p_j
	   (term1-binrel-term1-to-dfa* (args1 fml) (args2 fml) #'dfa-greatereq free)) 
	  (t
	   (call-next-method)))))

(defun term1-in-term2-to-dfa* (var1 var2 free)
  (cond ((tc-eq (emptyset-operator) var2)                ; x in emptyset
	 (values (dfa-false) free))
	((tc-eq (fullset-operator) var2)                 ; x in fullset
	 (values (dfa-true) free))
        ((and (natural-number-expr? var1)                ; n in P_j
	      (var2? var2 free))
	 (multiple-value-bind (j new-free)
	     (lookup-var2 var2 free)
	   (let* ((i (fresh-index))
		  (dfa (dfa-exists1 i                    ; exists1 p_i. p_i = n & p_i in P_j
			(dfa-conjunction
			 (dfa-const (number var1) i)
			 (dfa-in i j)))))
	     (values dfa new-free))))
	((and (application? var1)
	      (tc-eq (plus-operator) (operator var1))    ; (p_i + n) in P_j
	      (var1? (args1 var1) free)
	      (natural-number-expr? (args2 var1))
	      (var2? var2 free))
	 (multiple-value-bind (i new-free)
	     (lookup-var1 (args1 var1) free)
	   (multiple-value-bind (j new-new-free)
	       (lookup-var2 var2 new-free)
	     (let* ((k (fresh-index))                    ; exists1 p_k. p_k = p_i + n & p_k in P_j
		    (dfa (dfa-exists1 k
				      (dfa-conjunction
				       (dfa-plus1 k i (number (args2 var1)))
				       (dfa-in k j)))))
	       (values dfa new-new-free)))))
	((and (application? var1)
	      (tc-eq (plus-operator) (operator var1))    ; (n + p_i) in P_j
	      (var1? (args2 var1) free)
	      (natural-number-expr? (args1 var1))
	      (var2? var2 free))
	 (multiple-value-bind (i new-free)
	     (lookup-var1 (args2 var1) free)
	   (multiple-value-bind (j new-new-free)
	       (lookup-var2 var2 new-free)
	     (let* ((k (fresh-index))
		    (dfa (dfa-exists1 k
				      (dfa-conjunction
				       (dfa-plus1 k i (number (args1 var1)))
				       (dfa-in k j)))))
	       (values dfa new-new-free)))))
        ((and (var2? var2 free)                           ; p_i in P_j
	      (var1? var1 free))
	 (multiple-value-bind (i new-free)
	     (lookup-var1 var1 free)
	   (multiple-value-bind (j new-new-free)
	       (lookup-var2 var2 new-free)
	     (values (dfa-in i j) new-new-free))))
	(t
	 (throw 'not-ws1s-translatable nil))))

(defun term1-binrel-term1-to-dfa* (arg1 arg2 binrel free)
  (cond ((and (natural-number-expr? arg1)                               ; n binrel p_j
	      (var1? arg2 free))
	 (multiple-value-bind (j new-free)
	     (lookup-var1 arg2 free)       
	   (let* ((i (fresh-index))          ; exists1 p_i. p_i = n & p_i binrel p_j
		  (dfa (dfa-exists1 i
				    (dfa-conjunction (dfa-const (number arg1) i)
						     (funcall binrel i j)))))
	     (values dfa new-free))))
	((and (natural-number-expr? arg2)                               ; p_j binrel n
	      (var1? arg1 free))
	 (multiple-value-bind (j new-free)
	     (lookup-var1 arg1 free)
	   (let* ((i (fresh-index))        ; exists1 p_i. p_i = n & p_j binrel p_i
		  (dfa (dfa-exists1 i
				    (dfa-conjunction (dfa-const (number arg2) i)
						     (funcall binrel j i)))))
	     (values dfa new-free))))
        ((and (var1? arg1 free)                                         ; p_i binrel p_j
	      (var1? arg2 free))
	 (multiple-value-bind (i new-free)
	     (lookup-var1 arg1 free)
	   (multiple-value-bind (j new-new-free)
	       (lookup-var1 arg2 new-free)
	     (values (funcall binrel i j) new-new-free))))
	(t
	 (throw 'not-ws1s-translatable nil))))







