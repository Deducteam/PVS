;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; tc-unify.lisp -- Matches terms to get bindings for formal parameters
;; Author          : Sam Owre
;; Created On      : Fri Dec 17 02:44:21 1993
;; Last Modified By: Sam Owre
;; Last Modified On: Fri Oct 30 17:05:57 1998
;; Update Count    : 10
;; Status          : Stable
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Copyright (c) 2002 SRI International, Menlo Park, CA 94025, USA.

(in-package :pvs)

;;; Find-compatible-bindings takes a set of arguments (all of whose
;;; types slot is set to the possible types), a set of formal types
;;; to the given constant declaration, and a binding of the form
;;; ((fid1) (fid2) ... ) where each fid is the formal parameter
;;; identifier for the module containing the constant declaration.  The
;;; result of this function is a set of bindings of the form
;;; (((fid1 . v1) (fid2 . v2) ...) ((fid1 . v1') (fid2 . v2') ...) ...)
;;; Not all of the vi's will necessarily be found; incomplete bindings
;;; will be weeded out in resolve.lisp - see create-compatible-modinsts.

(defun find-compatible-bindings (arguments formals binding)
  (let* ((args-types (mapcar #'get-compatible-binding-types arguments))
	 (types-lists (cartesian-product args-types)))
    (find-compatible-bindings* types-lists formals binding nil)))

(defun get-compatible-binding-types (obj)
  (if (type obj)
      (list (lift-constructor-type obj))
      (lift-constructor-types obj)))

(defmethod lift-constructor-type ((obj constructor-name-expr))
  (supertype (type obj)))

(defmethod lift-constructor-type ((obj application))
  (if (constructor-name-expr? (operator obj))
      (supertype (type obj))
      (type obj)))

(defmethod lift-constructor-type (obj)
  (type obj))

(defmethod lift-constructor-types ((obj name-expr))
  (let ((creses (remove-if (complement #'no-argument-constructor-resolution?)
		  (resolutions obj))))
    (if creses
	(delete-duplicates
	 (nconc (mapcar #'(lambda (r) (supertype (type r))) creses)
		(remove-if #'(lambda (ty)
			       (some #'(lambda (r) (tc-eq ty (type r)))
				     creses))
		  (types obj)))
	 :test #'tc-eq)
	(types obj))))

(defmethod lift-constructor-types ((obj application))
  (if (name-expr? (operator obj))
      (let* ((creses (remove-if (complement #'constructor-resolution?)
		       (resolutions (operator obj))))
	     (rem-types (when creses
			  (remove-if
			      #'(lambda (ty)
				  (member ty
					  (resolutions (operator obj))
					  :test #'tc-eq
					  :key #'(lambda (r)
						   (range (type r)))))
			    (types obj)))))
	(if creses
	    (delete-duplicates
	     (nconc (mapcar #'(lambda (r) (supertype (range (type r))))
		      creses)
		    (mapcan #'(lambda (r)
				(unless (memq r creses)
				  (list (range (type r)))))
		      (resolutions (operator obj)))
		    rem-types)
	     :test #'tc-eq)
	    (types obj)))
      (types obj)))

(defmethod lift-constructor-types (obj)
  (types obj))

(defun constructor-resolution? (res)
  (adt-constructor-decl? (declaration res)))

(defun no-argument-constructor-resolution? (res)
  (and (adt-constructor-decl? (declaration res))
       (not (funtype? (type res)))))

(defun find-compatible-bindings* (types-lists formals binding result)
  (if (null types-lists)
      result
      (let* ((nbinding (copy-tree binding))
	     (nbind (find-compatible-binding (car types-lists) formals
					     nbinding)))
	(find-compatible-bindings* (cdr types-lists) formals binding
				   (if nbind (cons nbind result) result)))))

(defvar *tc-match-strictly* nil)

(defvar *tc-strict-matches* nil)

(defvar *formals-theory* nil)

(defvar *tc-match-boundvars* nil) ;;NSH: see below.

(defun find-compatible-binding (types formals binding)
  (let ((*formals-theory* (module (caar binding)))
	(*tc-strict-matches* nil))
    (find-compatible-binding* types formals binding)))

(defun find-compatible-binding* (types formals binding)
  (if (or (null types) (null binding))
      binding
      (let* ((*tc-match-strictly* nil)
	     (nbinding (tc-match* (car types) (car formals) binding)))
	(find-compatible-binding* (cdr types) (cdr formals) nbinding))))

;;; A marker to keep track of when an exact match is found; i.e., when a
;;; name provides all the actuals.  This is to stop tc-match from using
;;; compatible-type, since at this point the actuals are completely
;;; specified.

(defun tc-unify (t1 t2 bindings)
  (tc-match t1 t2 bindings))

(defun tc-match (t1 t2 bindings &optional strict-matches)
  #+pvsdebug (assert (every #'(lambda (b) (typep (car b) 'formal-decl))
			    bindings)
		     () "tc-match: bindings must be formal declarations")
  (let* ((*formals-theory* (module (caar bindings)))
	 (*tc-strict-matches* strict-matches))
    (values (tc-match* t1 t2 bindings)
	    *tc-strict-matches*)))

(defmethod tc-match* (t1 t2 bindings)
  (declare (ignore t1 t2 bindings))
  #+pvsdebug (when #+scl (eq (type-of t1) (type-of t2))
		   #-scl (eq (class-of t1) (class-of t2))
		   (break "Match should handle ~a types"
			  #+scl (type-of t1)
			  #-scl (class-of t1)))
  nil)

(defmethod tc-match* ((args list) (fargs list) bindings)
  (cond ((or (null bindings) (null args))
	 bindings)
	((and (singleton? args)
	      (typep (car args) 'tupletype)
	      (not (singleton? fargs)))
	 (tc-match* (types (car args)) fargs bindings))
	((and (singleton? fargs)
	      (typep (car fargs) 'tupletype))
	 (tc-match* args (types (car fargs)) bindings))
	(t (tc-match* (cdr args) (cdr fargs)
		      (tc-match* (car args) (car fargs) bindings)))))

(defmethod tc-match* :around ((arg type-expr) farg bindings)
  (with-slots (print-type) arg
    (when bindings
      (if (tc-eq arg farg)
	  bindings
	  (let ((nbindings (call-next-method)))
	    (when nbindings
	      (tc-match-print-type print-type farg nbindings)))))))

(defmethod tc-match-print-type ((ptype name) farg nbindings)
  (declare (ignore farg))
  (let* ((res (car (resolutions ptype)))
	 (acts (actuals (module-instance res))))
    (or (and acts
	     (eq (module (declaration res)) *formals-theory*)
	     (let ((formals (formals-sans-usings (module (declaration res)))))
	       (tc-match-actuals acts formals nbindings)))
	nbindings)))

(defmethod tc-match-print-type ((ptype type-application) farg nbindings)
  (or (tc-match* ptype
		 (or (when (type-expr? farg)
		       (print-type farg))
		     farg)
		 nbindings)
      nbindings))

(defmethod tc-match-print-type (ptype farg nbindings)
  (declare (ignore ptype farg))
  nbindings)

(defmethod tc-match* ((arg type-expr) (farg type-name) bindings)
  (let ((binding (assq (declaration farg) bindings)))
    (cond ((null binding)
	   nil)
	  ((null (cdr binding))
	   (unless (dependent-type? arg)
	     (when *tc-match-strictly*
	       (push arg *tc-strict-matches*))
	     (setf (cdr binding) arg))
	   bindings)
	  (t (set-tc-match-binding binding arg bindings)))))

(defun set-tc-match-binding (binding arg bindings &optional (last-attempt? t))
  (let ((type (compatible-type (cdr binding) arg)))
    (cond (type
	   (unless (or (and (dependent-type? type)
			    (not (has-type-vars? (cdr binding))))
		       (and (member (cdr binding) *tc-strict-matches*
				    :test #'tc-eq)
			    (or (fully-instantiated? (cdr binding))
				(not (fully-instantiated? arg)))))
	     (cond (*tc-match-strictly*
		    (push arg *tc-strict-matches*)
		    (setf (cdr binding) arg))
		   (t (setf (cdr binding) type))))
	   bindings)
	  (t (when last-attempt?
	       (tc-match-last-attempt (cdr binding) arg binding bindings))))))

(defun tc-match-last-attempt (arg1 arg2 binding bindings)
  (if (fully-instantiated? arg1)
      (unless (fully-instantiated? arg2)
	(tc-match-last-attempt* arg1 arg2 binding bindings))
      (when (fully-instantiated? arg2)
	(tc-match-last-attempt* arg2 arg1 binding bindings))))

(defun tc-match-last-attempt* (arg1 arg2 binding bindings)
  (let ((nbindings (tc-match arg1 arg2 (mapcar #'list (free-params arg2)))))
    (when (and nbindings (every #'cdr nbindings))
      (setf (cdr binding) arg1)
      bindings)))

(defun dependent-type? (type)
  (some #'(lambda (fv)
	    (and (typep (declaration fv) 'dep-binding)
		 (not (member fv *bound-variables*
			      :test #'same-declaration))))
	(freevars type)))

;(defmethod tc-match-formal-subtype-check ((farg formal-subtype-decl) arg
;					  bindings)
;  )

;(defmethod tc-match-formal-subtype-check ((farg formal-type-decl) arg
;					  bindings)
;  )


(defmethod tc-match* ((arg type-name) (farg type-name) bindings)
  (unless (null bindings)
    (or (call-next-method)
	(if (tc-eq arg farg)
	    bindings
	    (let ((a1 (actuals arg))
		  (a2 (actuals farg)))
	      (if (eq (id arg) (id farg))
		  (or (cond ((and a1 a2)
			     (or (tc-match* a1 a2 bindings)
				 bindings))
			    (a1
			     (tc-match-acts1
			      a1 (formals-sans-usings
				  (module (declaration (resolution farg))))
			      bindings))
			    (a2
			     (tc-match-acts1
			      a2 (formals-sans-usings
				  (module (declaration (resolution arg))))
			      bindings))
			    (t (tc-match-names arg farg bindings)))
		      (or (and (formal-type-decl? (declaration farg))
			       (not (assq (declaration farg) bindings))
			       bindings)
			  (tc-match-names arg farg bindings)))))))))

(defmethod tc-match* ((arg type-application) (farg type-application) bindings)
  (unless (null bindings)
    (or (call-next-method)
	(and (tc-eq (type arg) (type farg))
	     (tc-match* (parameters arg) (parameters farg) bindings))
	bindings)))

;;; Called by match* (modname modname)
(defun tc-match-acts (acts formals bindings)
  (let ((*tc-match-strictly* t)
	(*tc-strict-matches* nil))
    (tc-match-acts1 acts formals bindings)))

(defun tc-match-acts1 (acts formals bindings)
  (when (length= acts formals)
    (tc-match-acts* acts formals bindings)))

(defun tc-match-acts* (acts formals bindings)
  (cond ((null bindings)
	 nil)
	((null acts)
	 bindings)
	(t (tc-match-acts* (cdr acts) (cdr formals)
			   (tc-match-act (car acts) (car formals) bindings)))))

(defun tc-match-act (act formal bindings)
  (typecase formal
    (formal-subtype-decl
     (when (type-value act)
       (let ((binding (assq (declaration formal) bindings)))
	 (if (and *tc-match-exact* (cdr binding))
	     (when (tc-eq (type-value act) (cdr binding)) bindings)
	     (tc-match* (type-value act) (type-value formal) bindings)))))
    (formal-type-decl
     (when (type-value act)
       (let ((binding (assq (declaration formal) bindings)))
	 (if (and *tc-match-exact* (cdr binding))
	     (when (tc-eq (type-value act) (cdr binding)) bindings)
	     (tc-match* (type-value act) (type formal) bindings)))))
    (formal-const-decl
     (let ((binding (assq (declaration formal) bindings)))
       (cond ((null binding)
	      (tc-match* (expr act) formal bindings))
	     ((null (cdr binding))
	      (setf (cdr binding) (expr act))
	      bindings)
	     ((tc-eq (expr act) (cdr binding))
	      bindings)
	     (t (tc-match* (expr act) formal bindings)))))
    (t (break "Modules not yet supported"))))

(defmethod tc-match* (arg (farg dep-binding) bindings)
  (tc-match* arg (type farg) bindings))

(defmethod tc-match* ((arg dep-binding) farg bindings)
  (tc-match* (type arg) farg bindings))

(defmethod tc-match* ((arg subtype) farg bindings)
  (when bindings
    (or (call-next-method)
	(tc-match* (supertype arg) farg bindings))))

(defmethod tc-match* ((arg datatype-subtype) farg bindings)
  (when bindings
    (let ((nbindings
	   (if (and (typep farg 'type-name)
		    (let ((bind (cdr (assq (declaration farg)
					   bindings))))
		      (and bind
			   (fully-instantiated? bind))))
	       (let ((binding (assq (declaration farg) bindings)))
		 (set-tc-match-binding binding arg bindings))
	       (tc-match* (declared-type arg) farg bindings))))
      (when nbindings
	(mapc #'(lambda (b)
		  (let ((cdrb (gensubst (cdr b)
				#'(lambda (ex) (declare (ignore ex)) arg)
				#'(lambda (ex) (eq ex (declared-type arg))))))
		    (unless (eq cdrb (cdr b))
		      (setf (cdr b) cdrb))))
	      nbindings)
	nbindings))))

(defmethod tc-match* (arg (farg subtype) bindings)
  (when bindings
    (let ((fsubtype-binding
	   (assoc farg bindings
		  :test #'(lambda (x y)
			    (and (typep y 'formal-subtype-decl)
				 (tc-eq x (type-value y)))))))
      (cond ((null fsubtype-binding)
	     (or (call-next-method)
		 (tc-match* arg (supertype farg) bindings)))
	    ((null (cdr fsubtype-binding))
	     (when *tc-match-strictly*
	       (push arg *tc-strict-matches*))
	     (setf (cdr fsubtype-binding) arg)
	     bindings)
	    ((tc-eq arg (cdr fsubtype-binding))
	     bindings)))))

(defmethod tc-match* ((arg subtype) (farg subtype) bindings)
  ;; This will only check for the predicates being tc-eq, not provably equal
  (unless (null bindings)
    (let ((binding (assoc farg bindings
			  :test #'(lambda (x y)
				    (and (typep y 'formal-subtype-decl)
					 (tc-eq x (type-value y)))))))
      (if binding
	  (cond ((null (cdr binding))
		 (when *tc-match-strictly*
		   (push arg *tc-strict-matches*))
		 (setf (cdr binding) arg)
		 bindings)
		(t (set-tc-match-binding binding arg bindings nil)))
	  (or (let ((nbind (tc-match* (supertype arg) (supertype farg)
				      (tc-match* (predicate arg)
						 (predicate farg)
						 bindings))))
		(completed-tc-match-bindings nbind))
	      (let ((nbind (tc-match* arg (supertype farg) bindings)))
		(completed-tc-match-bindings nbind))
	      (tc-match* (supertype arg) farg bindings))))))

(defun completed-tc-match-bindings (nbind)
  (when (every #'cdr nbind)
    nbind))

(defmethod tc-match* ((arg funtype) (farg funtype) bindings)
  (unless (null bindings)
    (tc-match* (range arg) (range farg)
	       (let ((*tc-match-strictly* t))
		 (tc-match* (domain arg) (domain farg) bindings)))))

(defmethod tc-match* ((arg tupletype) (farg tupletype) bindings)
  (tc-match* (types arg) (types farg) bindings))

(defmethod tc-match* ((arg cotupletype) (farg cotupletype) bindings)
  (tc-match* (types arg) (types farg) bindings))

(defmethod tc-match* ((arg recordtype) (farg recordtype) bindings)
  ;;; CHECKME make sure the fields are sorted before this
  (tc-match* (fields arg) (fields farg) bindings))

(defmethod tc-match* ((fld field-decl) (ffld field-decl) bindings)
  (when (eq (id fld) (id ffld))
    (tc-match* (type fld) (type ffld) bindings)))

(defmethod tc-match-names ((n1 name) (n2 name) bindings)
  (if (tc-eq n1 n2)
      bindings
      (when (same-id n1 n2)
	(let* ((m1 (module-instance (resolution n1)))
	       (m2 (module-instance (resolution n2)))
	       (a1 (actuals m1))
	       (a2 (actuals m2)))
	  (cond ((and a1 a2)
		 (tc-match* a1 a2 bindings))
		(a1
		 (tc-match-acts1
		  a1 (formals-sans-usings (module (declaration n2)))
		  bindings))
		(a2
		 (tc-match-acts1
		  a2 (formals-sans-usings (module (declaration n1)))
		  bindings)))))))

(defmethod tc-match* ((a1 actual) (a2 actual) bindings)
  (if (type-value a1)
      (and (type-value a2)
	   (tc-match* (type-value a1) (type-value a2) bindings))
      (and (null (type-value a2))
	   (tc-match* (expr a1) (expr a2) bindings))))


;;; Expressions

(defmethod tc-match* ((arg number-expr) (farg number-expr) bindings)
  (when (= (number arg) (number farg))
    bindings))

(defmethod tc-match* ((A coercion) (B expr) bindings)
  (tc-match* (args1 A) B bindings))

(defmethod tc-match* ((A expr) (B coercion) bindings)
  (tc-match* A (args1 B) bindings))

(defmethod tc-match* ((A name-expr) (B coercion) bindings)
  (tc-match* A (args1 B) bindings))



(defmethod tc-match* ((arg expr) (farg name-expr) bindings)
  (let ((binding (assq (declaration farg) bindings)))
    (declare (type list binding))
    (cond ((null binding)
	   (when (and (typep arg 'name-expr)
		      (eq (declaration arg) (declaration farg))
		      (actuals (module-instance  arg))
		      (null (actuals (module-instance  farg))))
	     (mapc #'(lambda (act frm)
		       (unless (null bindings)
			 (let ((bind (assq frm bindings))
			       (type? (formal-type-decl? frm)))
			   (cond ((null bind)
				  (setq bindings nil))
				 ((null (cdr bind))
				  (setf (cdr bind)
					(if type?
					    (type-value act)
					    act)))
				 ((and type?
				       (tc-eq (cdr bind) (type-value act))))
				 ((and (not type?)
				       (tc-eq (cdr bind) act)))
				 (t (setq bindings nil))))))
		   (actuals (module-instance arg))
		   (formals-sans-usings (module (declaration arg))))
	     bindings))
	  ((null (cdr binding))
	   (setf (cdr binding) arg)
	   bindings)
	  (t (if (tc-eq arg (cdr binding)) bindings nil)))))

(defmethod tc-match* ((arg record-expr) (farg record-expr) bindings)
  (tc-match* (assignments arg) (assignments farg) bindings))

;(defmethod tc-match* ((arg coercion) (farg coercion) bindings)
;  (tc-match* (expression arg) (expression farg) bindings))

;(defmethod tc-match* ((arg intype) (farg intype) bindings)
;  (tc-match* (expression arg) (expression farg)
;	 (tc-match* (type arg) (type farg) bindings)))

(defmethod tc-match* ((arg projection-expr) (farg projection-expr) bindings)
  (when (= (index arg) (index farg))
    bindings))

(defmethod tc-match* ((arg projection-expr) (farg name-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg name-expr) (farg projection-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg injection-expr) (farg injection-expr) bindings)
  (when (= (index arg) (index farg))
    bindings))

(defmethod tc-match* ((arg injection-expr) (farg name-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg name-expr) (farg injection-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg injection?-expr) (farg injection?-expr) bindings)
  (when (= (index arg) (index farg))
    bindings))

(defmethod tc-match* ((arg injection?-expr) (farg name-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg name-expr) (farg injection?-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg extraction-expr) (farg extraction-expr) bindings)
  (when (= (index arg) (index farg))
    bindings))

(defmethod tc-match* ((arg extraction-expr) (farg name-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg name-expr) (farg extraction-expr) bindings)
  (declare (ignore bindings))
  nil)

(defmethod tc-match* ((arg projection-application)
		      (farg projection-application) bindings)
  (when (= (index arg) (index farg))
    (tc-match* (argument arg) (argument farg) bindings)))

(defmethod tc-match* ((arg injection-application)
		      (farg injection-application) bindings)
  (when (= (index arg) (index farg))
    (tc-match* (argument arg) (argument farg) bindings)))

(defmethod tc-match* ((arg injection?-application)
		      (farg injection?-application) bindings)
  (when (= (index arg) (index farg))
    (tc-match* (argument arg) (argument farg) bindings)))

(defmethod tc-match* ((arg extraction-application)
		      (farg extraction-application) bindings)
  (when (= (index arg) (index farg))
    (tc-match* (argument arg) (argument farg) bindings)))

(defmethod tc-match* ((arg field-application)
		      (farg field-application) bindings)
  (when (eq (id arg) (id farg))
    (tc-match* (argument arg) (argument farg) bindings)))

(defmethod tc-match* ((arg application) (farg application) bindings)
  (if (fully-instantiated? (operator farg))
      (if (tc-eq (operator arg) (operator farg))
	  (tc-match* (arguments arg) (arguments farg) bindings)
	  bindings)
      (tc-match* (operator arg) (operator farg)
		 (tc-match* (arguments arg) (arguments farg) bindings))))

(defmethod tc-match* ((arg binding-expr) (farg binding-expr) bindings)
  (and (eq (operator arg) (operator farg))
       (let ((bind-bindings
	      (tc-match-bindings (bindings arg) (bindings farg) bindings)))
	 (when bind-bindings
	   (let ((*tc-match-boundvars*  
		  (nconc (pairlis (bindings arg)(bindings farg))
			 *tc-match-boundvars*)))
	     (tc-match* (expression arg) (expression farg)
		       bind-bindings))))))

(defun tc-match-bindings (argbinds fargbinds bindings)
  (cond ((null bindings) nil)
	((and (null argbinds)(null fargbinds)) bindings)
	((not (or  (null argbinds)(null fargbinds)))
	 (let ((*tc-match-boundvars*
		(cons (cons (car argbinds)(car fargbinds))
		      *tc-match-boundvars*)))
	   (tc-match-bindings (cdr argbinds)(cdr fargbinds)
			      (tc-match* (type (car argbinds))
					(type (car fargbinds))
					bindings))))
	(t nil)))

(defmethod tc-match* ((arg update-expr) (farg update-expr) bindings)
  (tc-match* (expression arg) (expression farg)
	 (tc-match* (assignments arg) (assignments farg) bindings)))

(defmethod tc-match* ((n1 name-expr) (n2 name-expr) bindings)
  (if (tc-eq n1 n2)
      bindings
      (let ((bound? (assoc (declaration n1) *tc-match-boundvars*
			   :key #'declaration)))
	(cond   ;;NSH: modified to treat bound variables.
	  (bound?
	   (when (eq (declaration n2)
		     (declaration (cdr bound?)))
	     bindings))
	  ((and (null (assq (declaration n2) bindings)) ;NSH: needs this.
		(same-id n1 n2))
	   (let* ((m1 (module-instance (resolution n1)))
		  (m2 (module-instance (resolution n2)))
		  (a1 (actuals m1))
		  (a2 (actuals m2)))
	     (cond ((and a1 a2)
		    (tc-match* a1 a2 bindings))
		   (a1
		    (tc-match-actuals a1 (formals-sans-usings
					  (module (declaration n2)))
				      bindings))
		   (a2
		    (tc-match-actuals a2 (formals-sans-usings
					  (module (declaration n1)))
				      bindings)))))
	  (t (call-next-method))))))

(defun tc-match-actuals (actuals formals bindings)
  (when (length= actuals formals)
    (tc-match-actuals* actuals formals bindings)))

(defun tc-match-actuals* (actuals formals bindings)
  (if (null actuals)
      bindings
      (let ((binding (assq (car formals) bindings)))
	(cond ((null binding)
	       nil)
	      ((null (cdr binding))
	       (setf (cdr binding)
		     (or (type-value (car actuals))
			 (expr (car actuals))))
	       (tc-match-actuals* (cdr actuals) (cdr formals) bindings))
	      (t (when (if (type-value (car actuals))
			   (tc-eq (type-value (car actuals)) (cdr binding))
			   (tc-eq (expr (car actuals)) (cdr binding)))
		   (tc-match-actuals* (cdr actuals) (cdr formals) bindings)))))))

(defun collect-formals (expr)
  (let ((formals nil))
    (mapobject #'(lambda (ex)
		   (when (and (name? ex)
			      (formal-decl? (declaration ex)))
		     (pushnew (declaration ex) formals)))
	       expr)
    (mapcar #'(lambda (f) (list (id f))) formals)))
