;;; -*- Mode: LISP; Syntax: Common-lisp; Package: VERSE -*-

; process module for decision procedure         (Author: Rob Shostak, June 84)

; process.lsp (this file) incorporates tuples.

; -- Allen Van Gelder, Sep 10, 1984.

;;; The code here contains modifications
;;; to previous functions to implement beta-reduction during skolemization.
;;; The variable *canon-beta-reduce-on* controls whether beta-reduction
;;; is performed during canonization of formulas.

;;; BUGS
;;; Normally conditional expressions and boolean propositional structure
;;; is lifted to the outermost level during the last phase of skolemization
;;; (see DOREDUCTION, et. al.).  However, this structure cannot be lifted
;;; outside of lambda at that point.
;;; The result of a beta reduction may result in a formula involving
;;; embedded conditionals (i.e. if) and propositional boolean structure.
;;; There is code here to lift that structure out, so that it can be further
;;; processed by *****.
;;; There may be a problem of getting into an infinite loop which is not
;;; handled by this code (it has never happened in practice).  The problem
;;; in general may be difficult to solve.  
;;;
;;; fix up the protecting stuff (e.g. remove).
;;;

(defmacro conv-lambda-body (exp)
  `(cadr ,exp))

;;;
;;; apply expressions (apply expressions without type argument)
;;;

(defmacro is-skolemized-apply-expr (exp)
  `(memq (funsym ,exp) applysymlist))

(defmacro apply-operator (exp)
  `(second ,exp))

(defvar *rational-pred* nil)
(defvar *real-pred* nil)
(defvar *integer-pred* nil)

(defvar *canon-beta-reduce-on* t)

;;; list of already applied lambda bodies.  Used by
;;; canon-beta-reduce to avoid infinite recursion.

(defvar *already-applied* nil)

(defvar *lambda-reduced* nil)  ;flags whether a reduction was performed.

;;; this version of canon needed only for protecting applies.

(defvar *protecting-applications* nil) ; rebound only by canon.

; ------------------------------------------------------------------------
; prover initialization function 

(defun initprover()
 ;;; (terpri) (princ " Process.Lsp with tuples, Sep 10, 1984")
  (setq  typealist primtypealist )
  (setq  sigalist nil )
  (setq  findalist nil )
  (setq  usealist nil )
  (setq  applysymlist nil )

  (process '(NOT (EQUAL TRUE FALSE)))
)


; ------------------------------------------------------------------------
; process
;
; Argument to process is one literal: an atomic formula (atf) or a negated atf.
; Return is:
;     If lit resolves to (TRUE), return TRUE.
;     If lit resolves to (FALSE), *throw FALSE via (RETFALSE).
;     Otherwise, return a list of uninterpreted predicates (frequently nil),
;         as returned by process1.
; Side effects, accomplished via process1, take care of interpreted
; predicates, such as =, <, etc.

(defun process(lit)
   (prog(s)
     (cond ( (and (consp lit) (eq (funsym lit) 'NOT))
	     (setq s (nsolvecan (arg1 lit)))
	   )
	   ((or (and (consp lit) (eq (car lit) 'TRUE))
		(eq lit 'TRUE))
	    (return 'TRUE))
	   ((or (and (consp lit) (eq (car lit) 'FALSE))
		(eq lit 'FALSE))
	    (RETFALSE))
	   ( t
	     (setq s (solvecan lit))
	   )
     )
     (cond ( (equal s '(TRUE))  (return 'TRUE))
	   ( (equal s '(FALSE)) (RETFALSE))
	   ( t                  (return (process1 s)))
     )
   )
)

(defun invoke-process (lit)
  (catch 'context
    (let ((canlit (canon lit 'dont-add-use)))
      (process canlit))))

;;; DAC 6/6/95: process-no-canon is like canon, but does not
;;; canonize its input. It is called mainly from the array code
;;; (but could be called elsewhwere) where it is known that
;;; subterms have already been canonized.

(defun process-no-canon (lit)
  (prog(s)
     (cond ( (and (consp lit) (eq (funsym lit) 'NOT))
	     (setq s (nsolve (arg1 lit)))
	   )
	   ((or (and (consp lit) (eq (car lit) 'TRUE))
		(eq lit 'TRUE))
	    (return 'TRUE))
	   ((or (and (consp lit) (eq (car lit) 'FALSE))
		(eq lit 'FALSE))
	    (RETFALSE))
	   ( t
	     (setq s (solve lit))
	   )
     )
     (cond ( (equal s '(TRUE))  (return 'TRUE))
	   ( (equal s '(FALSE)) (RETFALSE))
	   ( t                  (return (process1 s)))
     )
   )
  )


(defun solvecan(atf)
  (cond ((and (consp atf) (eq (funsym atf) 'EQUAL))
	 (let ((lside (canon (lside atf)))
	       (rside (canon (rside atf))))
	   (if (subtermof lside rside)
	       (solve `(equal ,rside ,lside))
	       (solve `(equal ,lside ,rside)))))
	(t (solve
	    (canon atf)))))


(defun nsolvecan(atf)
  (cond ((and (consp atf) (eq (funsym atf) 'EQUAL))
	 (let ((lside (canon (lside atf)))
	       (rside (canon (rside atf))))
	   (if (subtermof lside rside)
	       (nsolve `(equal ,rside ,lside))
	       (nsolve `(equal ,lside ,rside)))))
	(t (nsolve (canon atf)))))

; -----------------------------------------------------------------
; process1
;
; Argument is a list of canonized atfs.
; The interpreted ones are processed via side-effects.
; TRUE is skipped over.
; FALSE causes *throw via RETFALSE.
; Returns: a list of uninterpreted predicates (frequently nil).
;
; The called procedures can insert more atfs at the front of the list "s"
; by accessing it non-locally.  See merge and addineq (and others?).

(defun process1(s)
  (when (and *development-mode* (not (consp s))) (break))
  (prog(bools exp)
    (loop while s do
	   (setq exp (pop s))
	   (cond
	    ((eq exp 'TRUE))
	    ((eq exp 'FALSE) (RETFALSE))
	    (t 
	     (case (funsym exp)
	       (EQUAL       (pr-merge (lside exp) (rside exp)))
	       (NEQUAL      (addneq exp))
	       (LESSEQP     (addineq exp))
	       (LESSP       (addineq exp))
	       (GREATEREQP  (addineq exp))
	       (GREATERP    (addineq exp))
	       (t           (push exp bools))
	       )
	     )
	    )
	   )
    (return bools)
    )
  )


; ------------------------------------------------------------------------
; disposition of arith-relational-op terms:
;     pr-merge   for equations,
;     addneq  for nequations (not ='s),
;     addineq for inequalities

; addineq not in this file:  see arith.lsp

;;;DAC: 10/30/92: modified to check if inequality can refine bounds on terms.
(defun addneq(neqn)
   (prog(fnsym term1 term2 number_ineq t1>t2 t2>t1)
     (setq term1 (lside neqn))
     (setq term2 (rside neqn))
     (setq number_ineq (member (or (prtype term1) (prtype term2))
			       '(integer number)))
     (when number_ineq
       (setq t1>t2 (newcontext (process `(GREATEREQP ,term1 ,term2))))
       (setq t2>t1 (newcontext (process `(GREATEREQP ,term2 ,term1)))))
     ;(setq t1>t2 (or (equal (pr-find `(GREATEREQP ,term1 ,term2)) 'TRUE)
     ;                (equal (pr-find `(LESSEQP ,term2 ,term1)) 'TRUE)))
     ;(setq t2>t1 (or (equal (pr-find `(GREATEREQP ,term2 ,term1)) 'TRUE)
     ;                (equal (pr-find `(LESSEQP ,term1 ,term2)) 'TRUE)))
     (when number_ineq
       (cond ((AND
	       (equal t1>t2 'TRUE)
	       (equal t2>t1 'TRUE)) (RETFALSE))
	     ((equal t1>t2 'TRUE)
	      (setq s (append (solve `(GREATERP ,term1 ,term2)) s)))
	     ((equal t2>t1 'TRUE)
	      (setq s (append (solve `(GREATERP ,term2 ,term1)) s)))))
     (setq fnsym (cons term1 term2))
     (adduse (list fnsym term1) term1)
     (adduse (list fnsym term2) term2)))

 
;;; 11-AUG-90 DAC: Modified from process.lisp to make apply of updates and apply
;;; of lambdas interpreted.

;;; 13-AUG-90 DAC: Modified to check whether newsig is interpretted or uninterpretted.
;;; This is necessary due to the simplification of applies of lambdas and
;;; applies of updates, which can make "u" uninterped, but newsig interped.

(defun pr-merge(t1 t2)
  (prog(use2 vptr newsig t2-is-lambda)
    (setq t1 (pr-find t1)
	  t2 (pr-find t2)
	  ;use2 (copy-list (use t2))    ; nil added by JMR 6/9/85 to fix  (set this value later  MES 6/22/88)
	  )				; bug (append without nil is
					; surely useless)
    (cond
     ((equal t1 t2) (return nil))
     ((and (consp t1) (consp (car t1)))    ;t1, t2 known to be unequal	
      (RETFALSE) ))
    (cond ((and (consp t1) (is-lambda-expr t1))  ; (SJ 5/13/86) added:
	   (setq t2 (prog1 t1 (setq t1 t2)))     ; swap to make lambda expr the find.
	   (setq t2-is-lambda t))
	  ((and (consp t2) (is-lambda-expr t2))  ; JMR 5/30/90 FIXME ??
	   (setq t2-is-lambda t)))	   
    (if (and t2-is-lambda		;DAC: 5/6/91 added check so to fix Butler's loop:
	     (atom t1)			; f = lambda x. f(x) so that it orients it:
	     (function-in t1 t2))	; lambda x. f(x) = f.
	(pr-union t2 t1)
      (pr-union t1 t2))			;t2 is now pr-find(t1)
    (loop for u in (use t1)
	 when (or (and (numberp t2) (not (zerop t2))) ; 8-28-91 dac: Don't replace part of
		  (not (eq (funsym u) 'quo))) do ; quo with a non-number.
      ; This check is necessary since the pr-find of t1 is 1 in some case. (is this ok?)
	 (setq newsig
	       (cons
		(funsym u)
		(loop for arg in (argsof (sig u)) collect
		     (cond ((equal arg t1) t2) (t arg)) )))	       
	 (cond
	  ;; (SJ 5/13/86) added:
	  ;; checks if newsig will be a reducible applciation;
	  ;; if so, treat as an interpreted expression.
	  ((and t2-is-lambda
		(consp u)
		(is-skolemized-apply-expr u)
		(eq (apply-operator u) t1))
	   (setq newsig
		 (sigma newsig))
	   (setq s (append (solve `(EQUAL ,(pr-find u) ,(canonsig newsig))) s))
	   )
	  ((uninterp newsig)		; SO 9/28/90 was u - is now newsig
	   (putsig newsig u)
	   (SETQ USE2 (COPY-LIST (USE T2))) ; MES 6/22/88 (CANONSIG call in interpreted term case below can add to (USE T2))
	   (setq vptr (push u use2)) ;;;DAC 2/15/94: Changed (push u use2) to (push newsig use2) since u would not contain t2.
	   ;;; DAC 2/28/94: Undid previous change: It is ok for u to not
	   ;;; contain t2 as long as sig(u) does.
	   (loop while (cdr vptr) do
		  (cond
		   ((equal newsig (sig (cadr vptr)))
		    (or (equal u (cadr vptr))
			(setq s 
			      (append
			       (solve
				`(EQUAL ,(pr-find u) 
					,(pr-find (cadr vptr))))
			       s )))

					;(checkusealist "merge - before rplacd")
					;(break "count")

		    (rplacd vptr (cddr vptr))

					;(checkusealist "merge - after rplacd")
		    )
		   (t (pop vptr)) ))

	   (putuse use2 t2) )
	  ((boolp (funsym u))
	   (cond
	    ((equal (pr-find u) (pr-find 'true)) ;;NSH(5/92): asserts
						 ;;a=b if a<=b and a>=b.
						 ;;NSA's David Ritch
						 ;;detected this anomaly.
	     (let* ((args (loop for arg in (argsof u) collect
					   (if (equal arg t1) t2 arg)))
		    (solvelist (solve
				(cons (funsym u) args))))
	       (cond ((and (memq (funsym u) '(GREATEREQP LESSEQP))
			   (equal solvelist '(TRUE)))
		      (if (equal
			   (catch 'context
			       (solve
				(cons (if (eq (funsym u) 'GREATEREQP)
					  'LESSEQP
					  'GREATEREQP)
				      args)))
			     
			   '(TRUE))
			  (setq s (append (solvecan `(EQUAL ,@args)) s))
			  (setq s (append solvelist s))))
		     (t (setq s (append solvelist s))))))
	    ((or (isapplyupdate newsig) (isapplylambda newsig))
					; DAC 13-AUG-90: This case is necessary
					; since apply-bool of updates or lambdas
					; are both interpreted as bools
					; and as apply`s of updates and lambdas.
	     (setq newsig
		   (sigma newsig))
	     (push `(EQUAL ,u ,(canonsig newsig)) s))

	    ((equal (pr-find u) (pr-find 'false))
	     (print "msg from merge - this should not have occurred
		       according to Rob Shostak ") )))
	  ((find1 u))
	  (t				; interpreted term
	   ;(setq newsig
		; (sigma newsig))
	   ; 7-24-91: dac changed above sigma no longer needed due to change in canonsig.
	   ; bug manifested itself in needing recursive call for sigupdate.
	   (push `(EQUAL ,u ,(canonsig newsig)) s))) ))) 

; ------------------------------------------------------------------------

;;; Is *protcting-applications* ever non-nil???
;;; Can't the original canon be used? FIXME JMR 5/31/90

(defvar *hash-canon-p* t)

(defvar *canon-hash* (make-hash-table :test #'eq))

(defun canon (term &optional (dont-add-use nil))
  (when *hash-canon-p* (clrhash *canon-hash*))
  (canon* term dont-add-use))

(defun canon* (term &optional (dont-add-use nil))
  (if *hash-canon-p*
      (canon-hash term dont-add-use)
      (canon-no-hash term dont-add-use)))

(defun canon-no-hash (term &optional (dont-add-use nil))
  (cond
   ((and (not *protecting-applications*)
	 (consp term)
	 (eq (funsym term) 'PROTECT))
    (let ((*protecting-applications* t))
      (canonsig (signature term dont-add-use) dont-add-use)))
   (t (canonsig (signature term dont-add-use) dont-add-use))))

(defun canon-hash (term &optional (dont-add-use nil))
  (let ((hash (gethash term *canon-hash*)))
    (if hash hash
	(let ((result (canon-no-hash term dont-add-use)))
	  (setf (gethash term *canon-hash*) result)
	  result))))

(defun canon-beta-reduce (term)
  (let ((lambda-body (conv-lambda-body (apply-operator term)))
	(*already-applied* *already-applied*))
    (declare (special *already-applied*))
    (cond ;;; can the following be simplified?? FIXME 5/31/90
      ((or *protecting-applications* (member lambda-body *already-applied*))
       term)
      (t
       (setq *lambda-reduced* t)
       (push lambda-body *already-applied*)
       (canon (lambdareduce term))))))

(defun canonsig(s &optional (dont-add-use nil))
   (catch 'found
     (cond
      ((symbolp s) (pr-find s))
      ((integerp s) s)
      (t
       (cond
         ( (interp s)
           (setq s (sigma ;;; 7-24-91: dac Added this sigma so that interpretted
		          ;;; terms are put in canonical form.
	                  ;;; bug manifested itself in needing recursive call for sigupdate.
		    (cons (funsym s)
			  (loop for arg in (argsof s) collect
				(canonsig arg dont-add-use)))
		   )
           )
         )
       )
       (when (consp s) ;;; 7-26-91: dac sigma might have reduced s to a non list.
	 (loop for u in (use (arg1 s))
	       do (and (equal s (sig u)) (throw 'found (pr-find u)))
	       )
	 (unless dont-add-use
	   (loop for arg in (argsof s) do (adduse s arg))))
       s
      )
     )
   )
)


; returns semantic signature of term

(defun signature(term &optional (dont-add-use nil))
   (cond
    ((atom term) term)
    ((and (null (argsof term)) (uninterp term)) (funsym term))
    (t 
     (sigma
      (cons
       (funsym term)
       (loop for arg in (argsof term) collect (canon* arg dont-add-use))
      )
     )
    )
   )
)


;;; if *canon-beta-reduce-on* is non-nil then sigma attempts to 
;;; perform beta-reduction.

(defun sigma (term)
  (cond
   ((symbolp term) term)
   ((qnumberp term) term)
   ;; (SJ 5/14/86) added following clause.
   ((and *canon-beta-reduce-on* (isapplylambda term))
    (canon-beta-reduce term))
   ;; JMR 5/30/90.  Why was following clause missing from Stan's code? FIXME
   ((and (boolp term)
	 (is-apply-n-x (funsym term))
	 (memq (arg1 term)
	       (append *rational-pred*
		       *real-pred*
		       *integer-pred*)))
    term)
   ((is-apply-n-x (funsym term)) (sigapply term))
   ((is-tupsel-n (funsym term)) (sigtupsel term))
   (t (case (funsym term)
	(PLUS       (sigplus term))
	(TIMES      (sigtimes term))
	(DIVIDE     (sigdivide term))
	(MINUS      (sigminus term))
	(DIFFERENCE (sigdifference term))
;	(TUPSEL     (sigtupsel term))
;	(ARRAYSEL   (sigapply term))
	(UPDATE     (sigupdate term))
;	(ARRAYREST  (sigarrayrest term))
	(FLOOR      (sigfloor term))
	(t          term)
      ))))

; ------------------------------------------------------------------------

; solve:  solver function for positive atomic formula (atf)
;
; Argument is an atomic formula (atf).  E.g., p(x, y), x=y+2, x<y+2, etc.
; Returns a list of atfs.
;
; "needed-if*" is checked to see if atf has if*. If so, if*'s are
; lifted to the top and the result is returned as a singleton list.
;
; called functions may do a *throw instead of returning, via RETFALSE.

;;; 7/25/94: DAC added *split-on-if* flag so that in pvs array solver
;;; would do less work

(defvar *split-on-if-in-solve* nil)

(defun solve (atf)
  (let ((atf (if (and *lift-if-in-solve* needed-if*)
		 (liftif* atf)
		 atf)))
    (cond
     ((atom atf)
      (ncons (case atf
	       (TRUE  'TRUE)
	       (FALSE 'FALSE)
	       (t     `(EQUAL ,atf TRUE))
	       )))
     ((and *lift-if-in-solve*
	   *lambda-reduced* (needs-bool-lifting atf))	; added for bool lifting (sj).
      (cond
       (needed-if*
	(ncons (lift-bools (liftif atf))))
       (t (ncons (lift-bools atf))))) 
     ((memq (funsym atf) '(IF IF*))
      (if *split-on-if-in-solve*
	  (let ((leftsolve (catch 'context (solve (arg2 atf))))
		(rightsolve (catch 'context (solve (arg3 atf)))))
	    (if (equal leftsolve rightsolve)
		(if (member leftsolve '(FALSE TRUE))
					; Sept 14, 1990: DAC
					; solve should always return a list
					; but catching 'context might not.
		    (ncons leftsolve)
		  leftsolve)
	      (ncons atf)))
	(if (equal (arg2 atf) (arg3 atf))
	    (solve (arg2 atf))
	  (ncons atf))))
     ((memq (funsym atf) '(LESSP LESSEQP GREATERP GREATEREQP))
      (arithsolve atf))
     (t
      ;; KLUDGE -- look at arg2 if arg1 is nil
      (case (if (eq (prtype (arg1 atf)) 'functional)
		(or (prtype (arg2 atf)) 'functional)
		(or (prtype (arg1 atf)) (prtype (arg2 atf))))
	((nil 
	  functional
	  bool )
	 (ncons (case (funsym atf)		
		  (EQUAL  (cond ((equal (arg1 atf) (arg2 atf)) 'TRUE)
				((and (memq (arg1 atf) '(true false))
				      (not (memq (arg2 atf) '(true false))))
				 `(EQUAL ,(arg2 atf) ,(arg1 atf)))
				(t atf)
				))
		  ;;		   ((LESSP NEQUAL LESSEQP GREATERP GREATEREQP) atf) ;NSH
		  (t      `(EQUAL ,atf TRUE)) )))
	(number  (arithsolve atf))
	(integer (arithsolve atf))
;	(set     (setsolve atf))
	(tuple   (tupsolve atf))
	(array   (arraysolve atf))
	(t       (error "No solver for type " (prtype (arg1 atf))))
	)))))

; ------------------------------------------------------------------
; nsolve:  solver function for negative atomic formula (NOT has been removed)
;
; Argument is an atomic formula (atf).  E.g., p(x, y), x=y+2, x<y+2, etc.
; Returns a list of atfs.
;
; "needed-if*" is checked to see if atf has if*. If so, if*'s are
; lifted to the top and the negated result is returned as a singleton list.
;
; nsolve may do a *throw instead of returning, via RETFALSE.
; called functions also may do this.

(defun nsolve (atf)
  (let* ((atf (if (and *lift-if-in-solve* needed-if*)
		  (liftif* atf)
		  atf)))
    (cond
     ((atom atf)
      (ncons (case atf
	       (TRUE  'FALSE)
	       (FALSE 'TRUE)
	       (t     `(EQUAL ,atf FALSE)) )))
     ((and *lift-if-in-solve*
	   *lambda-reduced* (needs-bool-lifting atf)) ; added for bool lifting (sj).
      (cond
       (needed-if*
	(ncons (list 'NOT (lift-bools (liftif atf)))))
       (t (ncons (list 'NOT (lift-bools atf))))))
     ((memq (funsym atf) '(if if*))
      (if *split-on-if-in-solve*
	  (let ((leftnsolve (catch 'context (nsolve (arg2 atf))))
		(rightnsolve (catch 'context (nsolve (arg3 atf)))))
	    (if (equal leftnsolve rightnsolve)
		(if (member leftnsolve '(FALSE TRUE))
					; Sept 14, 1990: DAC
					; nsolve should always return a list
					; but catching 'context might not.
		    (ncons leftnsolve)
		  leftnsolve)
	      (ncons (list 'NOT (liftif* atf)))))
	(if (equal (arg2 atf) (arg3 atf))
	    (nsolve (arg2 atf))
	  (ncons (list 'NOT (liftif* atf))))))
     ((memq (funsym atf) '(LESSP LESSEQP GREATERP GREATEREQP))
      (arithnsolve atf))
     (t
					; KLUDGE -- look at arg2 if arg1 is nil
      (case (if (eq (prtype (arg1 atf)) 'functional)
		(or (prtype (arg2 atf)) 'functional)
		(or (prtype (arg1 atf)) (prtype (arg2 atf))))
	((bool				; uninterpreted negative literal
	  nil
	  functional ) 
	 (ncons (case (funsym atf)		
		  (EQUAL  (cond
			   ((equal (arg1 atf) (arg2 atf)) 'FALSE)
			   (t
			    (prog (result)
			      (setq result
				    (newcontext (process1 (ncons atf)))
				    )
			      (return
			       (cond ((eq result 'TRUE) (RETFALSE))
				     ((eq result 'FALSE) 'TRUE)
				     (t  `(NEQUAL ,(arg1 atf)
						  ,(arg2 atf)
						  ))))))))
		  (NEQUAL (cond ((equal (arg1 atf)(arg2 atf)) 'TRUE)
				(t `(EQUAL ,(arg1 atf) ,(arg2 atf)))))
		  ((LESSP LESSEQP GREATERP GREATEREQP) (negineq atf)) ;NSH
		  (t      `(EQUAL ,atf FALSE)) )))
	(number  (arithnsolve atf))
	(integer (arithnsolve atf))
;	(set     (setnsolve atf))
	(tuple   (tupnsolve atf))
	(array   (arraynsolve atf))
	(t       (error "No nsolve for type "
			(or (prtype (arg1 atf)) (prtype (arg2 atf))) ))
	)))))

; ------------------------------------------------------------------------

(defun pr-union(t1 t2)
   (push (cons t1 t2) findalist)
)

(defun pr-find(v)
   (do ((u (find1 v) (find1 u))) ((null u) v) (setq v u))
)

(defun find1(v)          ;finds t's immediate ancestor
   (cdr (assoc v findalist :test #'equal))
)

(defun sig(v)
   (or (cdr (assoc v sigalist :test #'equal)) v)
)

(defun putsig(sg v)
   (push (cons v sg) sigalist)
)

(defun checkusealist (n)
  (loop for x in usealist do
       (cond ((and (not (member$ (cadr x) (cdr (assoc (car x) usealist :test #'equal))))
		   (not (some #'(lambda (y) (and (consp (car y))
						 (equal (car y) (caadr x))))
			      (cdr (assoc (car x) usealist :test #'equal)))
;			(loop for y in (cdr (assoc (car x) usealist :test #'equal))
;			    when (consp (car y))			
;			    thereis (equal (car y) (caadr x)))
			))
	      (terpri)
	      (pprint usealist)						
	      (terpri)(princ n)(terpri)
	      (break "eh?")))))

(defun use(v)
;  (checkusealist "use")
   (cdr (assoc v usealist :test #'equal))
)

(defun putuse(ul v)
   (push (cons v ul) usealist)
;  (checkusealist "putuse")
)


;;;DAC 2/15/94 added check for equal if if* so as not to put funny things on usealist.
(defun adduse(u v)
  (unless (and (consp u)
	       (or (equal (car u) 'equal)
		   (equal (car u) 'IF)
		   (equal (car u) 'IF*)))
    (prog(ul)
       (or (member u (setq ul (use v)) :test #'equal)
	   (push (cons v (cons u ul)) usealist)
	   )
	;  (checkusealist "adduse")
       )
    )
)



; ------------------------------------------------------------------------
; Various utility defuns


(defun isapplyupdate (exp)
  (and (consp exp)
       (is-apply-n-x (funsym exp))
       (listp (arg1 exp))
       (eq (funsym (arg1 exp)) 'UPDATE)))

;;; 13-AUG-90 DAC: made applies of updates and applies of lambdas interpreted.

(defun interp(term)
   (or (qnumberp term)
       (and (consp term)
	    (or (eq *printerpdivide* 'yes)
		(not (eq (funsym term) 'divide)))
	    (memq (funsym term) interpsyms)
       )
       (is-tupsel term)
       (isapplylambda term)
       (isapplyupdate term)
   )
)

(defun uninterp(term)
  (not (interp term))
)

; returns the type of a term
;
; The polymorphic if* takes the type of its second arg (the first arg
; is a boolean condition).  For robustness, if the second arg has
; type nil, it takes the type of the third arg.
;
; (if* b s t) means "if (b) then s else t".
; This is used for theories of arrays, monadic sets, and possibly others.

(defun prtype(term)
  (cond
   ((symbolp term) (getq term typealist))
   ((integerp term) 'integer)
   ((atom term) nil)
   ((eq (funsym term) 'if*) (or (prtype (arg2 term)) (prtype (arg3 term))))
   ((memq (funsym term) '(plus times difference minus))
    (if (loop for arg in (argsof term) always (eq (prtype arg) 'integer))
	'integer
	'number))
   ((symbolp (funsym term)) (getq (funsym term) typealist))
  )
)

(defun boolp(u) (eq (prtype u) 'BOOL))


; ------------------------------------------------------------------------
; More utility defuns

; "liftif" in effect continually rewrites "term" until all if*'s are
; at the top.  Thus (f a1 a2 (if* boolexp a31 a32) a4 a5) is rewritten
; as (if* boolexp (f a1 a2 a31 a4 a5) (f a1 a2 a32 a4 a5)).

(defun liftif (term)
  (cond ( (consp term)
	  (pushf (cons (funsym term)
		       (loop for arg in (argsof term) collect (liftif arg))
		 )
	  )
	)
	( t term)
  )
)

(defun pushf (term)
  (cond ( (consp term)
	  (cond ( (eq (funsym term) 'if*)  term)
		( t
		  (pushf1 term)
		)
	  )
	)
	(t term)
  )
)

; (pushf1 term) lifts the first if* that occurs at top level in an arg of
; term, then applies itself to the new 2nd and 3rd args of the lifted if*.
; Thus (pushf1 '(f a b (if* cond1 t1 t2) d (if* cond3 t3 t4)))
; returns
; '(if* cond1 (if* cond3 (f a b t1 d t3) (f a b t1 d t4))
;	      (if* cond3 (f a b t2 d t3) (f a b t2 d t4))
;  )


(defun pushf1 (term)
  (prog (firstif newterm)
    (do ( (rem (argsof term))
	  (rev (ncons (funsym term)))
	)
	( (null rem)
	  (setq newterm term) ; Exit the prog. No arg has if*.
	)
      (setq firstif (pop rem))
      (cond ( (and (consp firstif) (eq (funsym firstif) 'if*))
	      (setq newterm (list
			      'if*
			      (arg1 firstif)
			      (pushf1 (unwind rev (cons (arg2 firstif) rem)))
			      (pushf1 (unwind rev (cons (arg3 firstif) rem)))
			    )
	      )
	      (return newterm) ; Exit do. newterm's funsym pushed thru all if*s
	    )
	    ( t (push firstif rev))
      )
    )
    (return newterm)
  )
)

; (unwind '(c b a) '(d e f)) returns '(a b c d e f), etc.
; usage is local to pushf1.

(defun unwind (rev rem)
  (cond ( rev (unwind (cdr rev) (cons (car rev) rem)))
	( t rem)
  )
)


; ------------------------------------------------------------------------
; More utility defuns

; subtermof returns non-nil if the first arg is eq a proper subterm of
; the second.  This may duplicate the use defun.  The args should be
; canonized so the eq makes sense  for non-atom 1st arg.
; Note that (subtermof '(f a) (list 'g '(f a))) returns nil, but
; (subtermof (setq h '(f a)) (list 'g h)) returns ((f a)).

(defun subtermof (subterm term)
  (and (consp term)
       (or (member subterm term :test #'equal)
	   (loop for a in term thereis (subtermof subterm a))
       )
  )
)

(defun function-in (function term)
  (and (consp term)
       (or (and (is-apply-n-x (funsym term))
		(or (eq (arg1 term) function)
		    (and (listp (arg3 term))
			 (member function (arg3 term)))))
	   (loop for a in term thereis (function-in function a)))))

;_____________________________________________________________________________
;NSH(4/90): liftif redone as liftif* to simplify if-expressions.
;first, collect all the conditionals
;then simplify the expression accordingly.


; 1-AUG-90 dac: added check to not lift condidtionals of bound
; lambda variables.
; also checked for IF as well as IF*

; 13-AUG-90 dac: added flag in-prover so that when liftif* is called
; internal to the prover IF's and IF*`s become IF*'s,
; but when liftif* is called in makeimplication (in place of the old expandbools)
; IF's remain IF's
; 14-AUG-90, It seems that above flag may not be necessary.
; I am leaving it in, but calling it from makeimplication without setting it to nil
; to see if it still works correctly when IFs become IF*'s there.

(defun liftif* (exp &optional (in-prover t))
  (make-if*-exp exp (collect-conditionals exp NIL T) NIL in-prover))

(defun lamvar-in-exp? (exp)
  (cond
   ((consp exp) (loop for e in exp do
		      (if (lamvar-in-exp? e) (return t))))
   (t (lamvar? exp))))

(defun unbound-lamvar-in-exp? (exp &optional (arity-sum 0))
  (if (consp exp)
      (if (eq (funsym exp) 'LAMBDA)
	  (unbound-lamvar-in-exp? (caddr exp) (+ arity-sum (cadr exp)))
	(loop for e in exp do
	      (if (unbound-lamvar-in-exp? e arity-sum) (return t))))
    (and (lamvar? exp) (> (lamvar-index exp) arity-sum))))


(defun collect-conditionals (exp conds flg)
  (if (eq flg t)
      (if (consp exp)
	  (case (funsym exp)
	    ((if* if)
	     (collect-conditionals
	      (arg3 exp)
	      (collect-conditionals (arg2 exp)
				    (if (unbound-lamvar-in-exp? (arg1 exp))
					conds
				      (pushnew (arg1 exp) conds :test #'equal))
				    t)
	      t))
	    (t (collect-conditionals (argsof exp) conds NIL)))
	conds)
    (if (consp exp)
	(collect-conditionals (cdr exp)
			      (collect-conditionals (car exp) conds t) NIL)
      conds)))

(defun make-if*-exp (exp conds alist in-prover)
  (if (consp conds)
      `(,(if in-prover
	     'IF*
	   'IF)
	,(liftif* (car conds)) ;; 6-Dec-90: DAC added lifitif* to lift ifs from conditional.
	,(make-if*-exp exp (cdr conds)
		       (cons (cons (car conds) 'TRUE) alist) in-prover)
	,(make-if*-exp exp (cdr conds)
		       (cons (cons (car conds) 'FALSE) alist) in-prover))
    (if (consp exp)
	(case (funsym exp)
	  ((if* if)
	   (cond
	    ((eq (cdr (assoc (arg1 exp) alist :test #'equal))
		 'TRUE)
	     (make-if*-exp (arg2 exp) conds alist in-prover))
	    ((eq (cdr (assoc (arg1 exp) alist :test #'equal))
		 'FALSE)
	     (make-if*-exp (arg3 exp) conds alist in-prover))
	    (t (cons (funsym exp)
		     (loop for e in (argsof exp) collect
			   (make-if*-exp e conds alist in-prover))))))
	  (t (cons (funsym exp)
		   (loop for e in (argsof exp) collect
			 (make-if*-exp e NIL alist in-prover)))))
      exp)))

;;NSH(12/17):  newexpandbools only lifts IFs up to the top-level 
;;propositional connective.

;(defun newexpandbools (exp)
;  (cond ((atom exp) exp)
;        (t (case (funsym exp)
;	  ((and or implies not iff)
;	   (cons (funsym exp)
;		 (mapcar #'newexpandbools (cdr exp))))
;	  (t (liftif* exp))))))


(defvar *conditionals* nil)

(defun newexpandbools1 (exp flg)
  (if (eq flg t)
      (cond ((atom exp) exp)
	    (t (case (funsym exp)
		 ((and or implies not iff)
		  (cons (funsym exp)
			(newexpandbools1 (cdr exp)  nil)))
		 (t (let ((expconds (collect-conditionals exp nil t)))
		      (setq *conditionals*
			    (append expconds *conditionals*))
		      (make-if*-exp exp expconds nil nil)
		      )))))
    (if (consp exp)
	(cons (newexpandbools1 (car exp)  t)
	      (newexpandbools1 (cdr exp)  nil))
      nil)))

(defvar *numconds* 3)

(defun newexpandbools (exp)
  (let* ((*conditionals* nil)
	 (newexp
	  (newexpandbools1 exp  t)))
    (make-if*-exp newexp (frequent-conds *conditionals* *numconds*) nil nil)))

(defun frequent-conds (conds num)
  (remove-duplicates
   (loop for x in conds
	 when (>= (count x conds :test #'equal) num)
	 collect x)
   :test #'equal))


;;; check if expression has any boolean operations that are not enclosed in
;;; a lambda expression.

;;; Shankar wonders if this stuff is right.  FIXME JMR 5/31/90

(defun needs-bool-lifting (exp)
  (catch 'bool-lifting (needs-bool-lifting1 exp)))

(defun needs-bool-lifting1 (exp)
  (cond
    ((atom exp) nil)
    ((memq (funsym exp) '(AND OR IMPLIES NOT IF IFF))
     (throw 'bool-lifting t))
    ;; the next case probably wont occur -  need to check ***
    ((and (eq (funsym exp) 'EQUAL) (eq (prtype (arg1 exp)) 'bool))
     (throw 'bool-lifting t))
    ((eq (funsym exp) 'LAMBDA) nil)
    (t (loop for subexp in (argsof exp) thereis (needs-bool-lifting1 subexp)))))
				    

;;; like expandbools but doesnt go inside lambda expressions.

(defvar *max-lift-bools* 6)
;; 12/13/94: DAC added *max-lift-bools* flag
;; to limit exponential expansion of lift-bools.
;; value of -1 is unlimited expansion.
;; value of 14 results in infinite computation in at least one example.

(defun lift-bools (f &optional (bool-level 0))
  (cond
   ((= bool-level *max-lift-bools*) f)
   ((symbolp f) f)
   (t (case (funsym f)
	((and or implies not if iff)  ; recurse into top-level prop structure
	 (cons (funsym f)
	       (loop for arg in (argsof f)
		     collect (lift-bools arg (1+ bool-level)))))
	(equal
	 (cond
	  ((eq (prtype (arg1 f)) 'bool)
	   `(iff ,(lift-bools (arg1 f) (1+ bool-level))
		 ,(lift-bools (arg2 f) (1+ bool-level))))
	  (t (lift-embedded-bools f bool-level))))
	;; dont go inside lambdas.
	(lambda f)
	(t
	 (lift-embedded-bools f bool-level))))))

(defun lift-embedded-bools (embeddedf bool-level)
  (catch 'lift-embedded
    (cons (funsym embeddedf)
	  (loop for arg in (argsof embeddedf)
		collect (lift-embedded-bools1 arg embeddedf bool-level)))))

(defun lift-embedded-bools1 (f embeddedf bool-level)
  (cond
   ((or (equal f 'TRUE) (equal f 'FALSE))
    f)
   ;; dont go inside lambdas.
   ((and (consp f) (eq (funsym f) 'LAMBDA))
    f)
   ((eq (prtype f) 'bool)
    (throw 'lift-embedded  
      (lift-bools
       `(IF ,f ,
	    (subst-expr 'TRUE f embeddedf)
	    ,(subst-expr 'FALSE f embeddedf))
       bool-level)))
   ((qnumberp f) f)
   ((symbolp f) f)
   ((eq (funsym f) 'IF)
    (throw 'lift-embedded
      (lift-bools
      `(IF ,(arg1 f)
	   ,(subst-expr (arg2 f) f embeddedf)
	   ,(subst-expr (arg3 f) f embeddedf))
      bool-level)))
   (t
    (cons (funsym f)
	  (loop for arg in (argsof f)
		collect (lift-embedded-bools1 arg embeddedf bool-level))))))

