;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pp-tex.lisp -- 
;; Author          : Sam Owre
;; Created On      : Tue Jan 12 03:25:25 1999
;; Last Modified By: Sam Owre
;; Last Modified On: Fri Jan 22 14:11:28 1999
;; Update Count    : 5
;; Status          : Unknown, Use with caution!
;; 
;; HISTORY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :pvs)

(defvar *latex-id-strings* (make-hash-table :test 'eq))

(defvar *latex-keyword-strings* (make-hash-table :test 'eq))

(defvar *latex-funsym-strings* (make-hash-table :test 'eq))

(defvar *pvs-tex-substitution-hash* (make-hash-table :test 'equal))

(defvar *tex-symbol-counters* nil)

(defvar *in-tex-math-mode* nil)

(defun pp-tex (obj stream)
  (let ((*print-pretty* t)
	(*print-escape* nil)
	(*print-right-margin* *latex-linelength*)
	(*tex-symbol-counters* nil))
    ;;(setf (slot-value *standard-output* 'excl::charpos) 0)
    (unwind-protect
	(let ((str (with-output-to-string (*standard-output*)
		     (pp-tex* obj))))
	  (write-string-with-tex-substitutions str 0 (length str) stream))
      (clrhash *latex-id-strings*)
      (clrhash *latex-keyword-strings*)
      (clrhash *latex-funsym-strings*)
      (clrhash *pvs-tex-substitution-hash*))))

(defun write-string-with-tex-substitutions (str pos len stream)
  (if (< pos len)
      (let ((char (char str pos)))
	(cond ((< (char-code (char str pos)) 127)
	       (write-char char stream)
	       (write-string-with-tex-substitutions str (1+ pos) len stream))
	      (t (let* ((npos (or (position-if #'(lambda (ch)
						   (< (char-code ch) 127))
					       str
					       :start pos :end len)
				  len))
			(trans (gethash (subseq str pos npos)
					*pvs-tex-substitution-hash*)))
		   (assert trans)
		   (write trans :stream stream)
		   (write-string-with-tex-substitutions
		    str npos len stream)))))))
  

;(defmethod pp-tex* :around ((syn syntax))
;  (call-next-method)
;  ;; need to deal with comments here
;  )

;;; Module level

(defmethod pp-tex* ((theories modules))
  (pprint-logical-block (nil theories)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (terpri) (terpri))))

;(defmethod pp-tex* ((mod datatype-or-module))
;  (call-next-method))

(defmethod pp-tex* ((mod module))
  (with-slots (id formals exporting assuming theory) mod
    (pprint-logical-block (nil nil)
      (pp-tex-id id)
      (pp-tex-theory-formals formals)
      (write-char #\:)
      (write-char #\space)
      (pprint-indent :block 2)
      (pp-tex-keyword 'THEORY)
      (pprint-indent :block 1)
      (pprint-newline :mandatory)
      (pp-tex* exporting)
      (pp-tex-keyword 'BEGIN)
      (pprint-indent :block 2)
      ;;(pprint-newline :mandatory)
      (pp-tex-assuming (if *unparse-expanded*
		       assuming
		       (remove-if #'generated-by assuming)))
      (pp-tex-theory (if *unparse-expanded*
		     theory
		     (remove-if #'generated-by theory)))
      (pprint-indent :block 1)
      (pprint-newline :mandatory)
      (pp-tex-keyword 'END)
      (write-char #\space)
      (pp-tex-id id))))

(defun pp-tex-theory-formals (formals)
  (when formals
    (let ((*pretty-printing-decl-list* t))
      (pprint-logical-block (nil formals :prefix "[" :suffix "]")
	(loop (let ((elt (pprint-pop)))
		(when (typep elt 'importing)
		  (let ((imps (list elt)))
		    (loop while (chain? (car imps))
			  do (setq elt (pprint-pop))
			  do (push elt imps))
		    (pprint-logical-block (nil (nreverse imps)
					       :prefix "(" :suffix ")")
		      (pp-tex-keyword 'IMPORTING)
		      (write #\space)
		      (pprint-indent :current 0)
		      (loop (pp-tex* (pprint-pop))
			    (pprint-exit-if-list-exhausted)
			    (write-char #\,)
			    (write-char #\space)
			    (pprint-newline :fill))))
		  (write-char #\space)
		  (setq elt (pprint-pop)))
		(pp-tex* elt)
		(pprint-exit-if-list-exhausted)
		(write-char #\,)
		(write-char #\space)
		(pprint-newline :fill)))))))

(defmethod pp-tex* ((exp exporting))
  (with-slots (kind names but-names modules) exp
    (unless (eq kind 'default)
      (pprint-logical-block (nil nil)
	(pp-tex-keyword 'EXPORTING)
	(write-char #\space)
	(pprint-indent :current 0)
	(pp-tex-exportings names but-names)
	(when (or kind modules)
	  (pprint-indent :block 4)
	  (pprint-newline :fill)
	  (pp-tex-exportingmods kind modules))))))

(defun pp-tex-exportings (names but-names)
  (pprint-logical-block (nil names)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :fill)))
  (when but-names
    (write-char #\space)
    (pp-tex-keyword 'BUT)
    (write-char #\space)
    (pprint-logical-block (nil but-names)
      (loop (pprint-indent :current 2)
	    (pp-tex* (pprint-pop))
	    (pprint-exit-if-list-exhausted)
	    (write-char #\,)
	    (write-char #\space)))))

(defun pp-tex-exportingmods (kind modules)
  (pprint-logical-block (nil modules)
    (write-char #\space)
    (pp-tex-keyword 'WITH)
    (write-char #\space)
    (if kind
	(pp-tex-keyword kind)
	(loop (pprint-indent :current 2)
	      (pp-tex* (pprint-pop))
	      (pprint-exit-if-list-exhausted)
	      (write-char #\,)
	      (write-char #\space)))))

(defmethod pp-tex* ((name expname))
  (with-slots (id kind type) name
    (pprint-logical-block (nil nil)
      (pp-tex-id id)
      (when kind
	(write-char #\:)
	(write-char #\space)
	(if (symbolp kind)
	    (pp-tex-keyword kind)
	    (pp-tex* type))))))

(defun pp-tex-assuming (assuming)
  (when assuming
    (let ((*pretty-printing-decl-list* t)
	  (last-one (car (last assuming))))
      (pprint-newline :mandatory)
      (pprint-logical-block (nil nil)
	(pp-tex-keyword 'ASSUMING)
	(pprint-indent :block 1)
	(pprint-newline :mandatory)
	(pprint-logical-block (nil (check-chained-syntax assuming))
	  (loop (let ((decl (pprint-pop)))
		  (if (typep decl 'importing)
		      (let ((imps (list decl)))
			(loop while (chain? (car imps))
			      do (setq decl (pprint-pop))
			      do (push decl imps))
			(pprint-logical-block (nil (nreverse imps))
			  (pp-tex-keyword 'IMPORTING)
			  (write #\space)
			  (pprint-indent :current 0)
			  (loop (pp-tex* (pprint-pop))
				(pprint-exit-if-list-exhausted)
				(write-char #\,)
				(write-char #\space)
				(pprint-newline :fill))))
		      (pp-tex* decl))
		  (unless (or (chain? decl)
			      (eq decl last-one))
		    (pprint-newline :mandatory)))
		(pprint-exit-if-list-exhausted)))
	(pprint-indent :block 0)
	(pprint-newline :mandatory)
	(pp-tex-keyword 'ENDASSUMING)
	(pprint-newline :mandatory)))))

(defun pp-tex-theory (theory)
  (when theory
    (let ((*pretty-printing-decl-list* t)
	  (last-one (car (last theory))))
      (pprint-newline :mandatory)
      (pprint-logical-block (nil (check-chained-syntax theory))
	(loop (let ((decl (pprint-pop)))
		(if (typep decl 'importing)
		    (let ((imps (list decl)))
		      (loop while (chain? (car imps))
			    do (setq decl (pprint-pop))
			    do (push decl imps))
		      (pprint-logical-block (nil (nreverse imps))
			(pp-tex-keyword 'IMPORTING)
			(write #\space)
			(pprint-indent :current 0)
			(loop (pp-tex* (pprint-pop))
			      (pprint-exit-if-list-exhausted)
			      (write-char #\,)
			      (write-char #\space)
			      (pprint-newline :fill))))
		    (pp-tex* decl))
		(unless (or (chain? decl)
			    (eq decl last-one))
		  (pprint-newline :mandatory)))
	      (pprint-exit-if-list-exhausted))))))

(defmethod pp-tex* ((dt datatype))
  (with-slots (id formals importings assuming constructors) dt
    (pprint-logical-block (nil nil)
      (pp-tex-id id)
      (pp-tex-theory-formals formals)
      (write-char #\:)
      (write-char #\space)
      (pprint-indent :block 2)
      (pp-tex-keyword 'DATATYPE)
      (pprint-indent :block 1)
      (when (typep dt 'datatype-with-subtypes)
	(write-char #\space)
	(pp-tex-keyword 'WITH)
	(write-char #\space)
	(pp-tex-keyword 'SUBTYPES)
	(write-char #\space)
	(pprint-logical-block (nil (subtypes dt))
	  (loop (pp-tex* (pprint-pop))
		(pprint-exit-if-list-exhausted)
		(write-char #\,)
		(write-char #\space))))
      (pprint-newline :mandatory)
      (pp-tex-keyword 'BEGIN)
      (pprint-indent :block 2)
      (pprint-newline :mandatory)
      (when importings
	(pprint-logical-block (nil importings)
	  (pp-tex-keyword 'IMPORTING)
	  (write #\space)
	  (pprint-indent :current 0)
	  (loop (pp-tex* (pprint-pop))
		(pprint-exit-if-list-exhausted)
		(write-char #\,)
		(write-char #\space)
		(pprint-newline :fill)))
	(pprint-newline :mandatory))
      (pp-tex-assuming assuming)
      (pp-tex-constructors constructors)
      (pprint-indent :block 1)
      (pprint-newline :mandatory)
      (pp-tex-keyword 'END)
      (write-char #\space)
      (pp-tex-id id))))

;;; (defmethod pp-tex* ((dt datatype-with-subtype)))

;;; (defmethod pp-tex* ((dt inline-datatype)))

;;; (defmethod pp-tex* ((dt inline-datatype-with-subtype)))

(defun pp-tex-constructors (constructors)
  (pprint-logical-block (nil constructors)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :mandatory))))

(defmethod pp-tex* ((constr adt-constructor))
  (with-slots (id arguments recognizer) constr
    (pprint-logical-block (nil nil)
      (pp-tex-id id)
      (when arguments
	(pprint-logical-block (nil arguments :prefix "(" :suffix ")")
	  (loop (pp-tex* (pprint-pop))
		(pprint-exit-if-list-exhausted)
		(write-char #\,)
		(write-char #\space)
		(pprint-newline :fill))))
      (write-char #\:)
      (write-char #\space)
      (pp-tex-id recognizer)
      (when (typep constr 'constructor-with-subtype)
	(write-char #\:)
	(write-char #\space)
	(pp-tex* (subtype constr))))))

(defmethod pp-tex* ((ad adtdecl))
  ;; The around method for declarations would have already printed the id:
  (with-slots (declared-type) ad
    (pp-tex* declared-type)))

;;; (defmethod pp-tex* ((constr simple-constructor)))

;;; (defmethod pp-tex* ((constr constructor-with-subtype)))


;;; Declarations

(defmethod pp-tex* ((imp importing))
  (with-slots (theory-name chain? semi) imp
    (unless *pretty-printing-decl-list*
      (pp-tex-keyword 'IMPORTING)
      (write-char #\space))
    (pp-tex* theory-name)))

(defmethod pp-tex* :around ((decl declaration))
  (with-slots (id module formals chain? semi) decl
    (when (or *unparse-expanded*
	      *adt*
	      (not (generated-by decl)))
      (pprint-logical-block (nil nil)
	(cond ((and chain?
		    *pretty-printing-decl-list*)
	       (pp-tex-id id)
	       (unless (typep decl 'formal-decl)
		 (write-char #\,)
		 (write-char #\space)))
	      (t (when (newline-comment decl)
		   (write (car (newline-comment decl)))
		   (write-char #\space)
		   (pprint-newline :mandatory))
		 (when (and *comment-on-proof-status*
			    (tcc? decl))
		   (format t "  % ~a~%" (proof-status-string decl)))
		 (pp-tex-const-decl id formals (id module))
		 (write-char #\:)
		 (write-char #\space)
		 (pprint-newline :miser)
		 (call-next-method)
		 (when semi (write-char #\;))
		 (write "\\vspace*{\\pvsdeclspacing}")))))))

(defun pp-tex-const-decl (id pre-formals theory-id &optional post-formals)
  (cond (pre-formals
	 (let ((funsym (get-pp-tex-funsym id (mapcar #'length pre-formals)
					  theory-id)))
	   (cond (funsym
		  (unless *in-tex-math-mode*
		    (write "\\("))
		  (let ((*in-tex-math-mode* t))
		    (write funsym)
		    (dolist (args pre-formals)
		      (dolist (a args)
			(write "{")
			(pp-tex* a)
			(write "}"))))
		  (unless *in-tex-math-mode*
		    (write "\\)"))
		  (pp-tex-decl-formals post-formals))
		 (t (pp-tex-const-decl id (butlast pre-formals) theory-id
				       (cons (car (last pre-formals))
					     post-formals))))))
	(t (pp-tex-id id)
	   (pp-tex-decl-formals post-formals))))

(defun pp-tex-decl-formals (formals)
  (when formals
    (let ((*pretty-printing-decl-list* t))
      (pprint-logical-block (nil formals)
	(loop (pp-tex-lambda-formal (pp-tex-chained-decls (pprint-pop)) nil)
	      (pprint-exit-if-list-exhausted)
	      (pprint-newline :fill))))))



;;; Need this as a primary method
(defmethod pp-tex* ((decl declaration))
  nil)

;; (defmethod pp-tex* ((decl nonempty-type-decl)))

(defmethod pp-tex* ((decl type-decl))
  (with-slots (type-expr chain?) decl
    (if (typep decl 'nonempty-type-decl)
	(pp-tex-keyword (case (keyword decl)
		 (nonempty_type 'NONEMPTY_TYPE)
		 (t 'TYPE+)))
	(pp-tex-keyword 'TYPE))
    (when (typep decl 'type-def-decl)
      (write-char #\space)
      (pprint-newline :miser)
      (if (typep decl 'type-eq-decl)
	  (write-char #\=)
	  (pp-tex-keyword 'FROM))
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex* type-expr))))
      

;; (defmethod pp-tex* ((decl nonempty-type-def-decl)) )

;; (defmethod pp-tex* ((decl type-eq-decl)) )

;; (defmethod pp-tex* ((decl nonempty-type-eq-decl)) )

;; (defmethod pp-tex* ((decl type-from-decl)) )

;; (defmethod pp-tex* ((decl nonempty-type-from-decl)) )

;; (defmethod pp-tex* ((decl formal-decl)) )

(defmethod pp-tex* ((decl formal-type-decl))
  (with-slots (type-expr) decl
    (if (typep decl 'formal-nonempty-type-decl)
	(pp-tex-keyword (case (keyword decl)
			  (nonempty_type 'NONEMPTY_TYPE)
			  (t 'TYPE+)))
	(pp-tex-keyword 'TYPE))
    (when (typep decl 'formal-subtype-decl)
      (write-char #\space)
      (pp-tex-keyword 'FROM)
      (write-char #\space)
      (pp-tex* type-expr))))

;; (defmethod pp-tex* ((decl formal-nonempty-type-decl)) )

;; (defmethod pp-tex* ((decl formal-subtype-decl)) )

;; (defmethod pp-tex* ((decl formal-nonempty-subtype-decl)) )

(defmethod pp-tex* ((decl formal-const-decl))
  (with-slots (declared-type) decl
    (pp-tex* declared-type)))

(defmethod pp-tex* ((decl lib-decl))
  (with-slots (lib-string) decl
    (pp-tex-keyword 'library)
    (when (typep decl 'lib-eq-decl)
      (write-char #\space)
      (write-char #\=))
    (write-char #\space)
    (pprint-newline :fill)
    (let* ((str (lib-string decl))
	   (ch (find-verb-char str)))
      (format t "\\symbol{34}$\\verb~c~a~c$\\symbol{34}" ch str ch))))

(defun find-verb-char (str)
  (dotimes (i 127)
    (let ((ch (character i)))
      (when (and (graphic-char-p ch)
		 (not (alphanumericp ch))
		 (not (char= ch #\space))
		 (not (find ch str)))
	(return ch)))))

;; (defmethod pp-tex* ((decl lib-eq-decl)) )

(defmethod pp-tex* ((decl mod-decl))
  (with-slots (modname) decl
    (pp-tex-keyword 'library)
    (when (typep decl 'lib-eq-decl)
      (write-char #\space)
      (write-char #\=))
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* modname)))

(defmethod pp-tex* ((decl var-decl))
  (with-slots (declared-type) decl
    (pp-tex-keyword 'VAR)
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* declared-type)))

(defmethod pp-tex* ((decl const-decl))
  (with-slots (declared-type definition) decl
    (pprint-newline :fill)
    (pp-tex* declared-type)
    (when definition
      (write-char #\space)
      (pp-tex-keyword '=)
      (pprint-indent :block 4)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex* definition)
      (pprint-indent :block 2))))

;; (defmethod pp-tex* ((decl proj-decl)) )

(defmethod pp-tex* ((decl def-decl))
  (with-slots (declared-type definition declared-measure ordering) decl
    (pp-tex-keyword 'RECURSIVE)
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* declared-type)
    (write-char #\space)
    (pp-tex-keyword '=)
    (pprint-indent :block 2)
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* definition)
    (pprint-indent :block 3)
    (pprint-newline :mandatory)
    (pp-tex-keyword 'MEASURE)
    (write-char #\space)
    (pp-tex* declared-measure)
    (when ordering
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex-keyword 'BY)
      (write-char #\space)
      (pp-tex* ordering))
    (pprint-indent :block 2)))

(defmethod pp-tex* ((decl inductive-decl))
  (with-slots (declared-type definition) decl
    (write-char #\space)
    (pp-tex-keyword 'INDUCTIVE)
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* declared-type)
    (write-char #\space)
    (pp-tex-keyword '=)
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* definition)))

(defmethod pp-tex* ((decl formula-decl))
  (with-slots (spelling definition) decl
    (pp-tex-keyword spelling)
    (pprint-indent :block 4)
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* definition)
    (pprint-indent :block 2)))

(defmethod pp-tex* :around ((decl name-judgement))
  (with-slots (name chain? declared-type) decl
    (when (or (not *pretty-printing-decl-list*)
	      (not *pretty-printed-prefix*))
      (when *pretty-printing-decl-list*
	(setq *pretty-printed-prefix* t))
      (pp-tex-keyword 'JUDGEMENT)
      (write-char #\space)
      (pprint-newline :miser))
    (pp-tex* name)
    (cond ((and chain?
		*pretty-printing-decl-list*)
	   (write-char #\,)
	   (write-char #\space))
	  (t (pprint-indent :block 4)
	     (write-char #\space)
	     (pprint-newline :fill)
	     (pp-tex-keyword 'HAS_TYPE)
	     (write-char #\space)
	     (pprint-newline :fill)
	     (pp-tex* declared-type)
	     (pprint-indent :block 2)
	     (setq *pretty-printed-prefix* nil)))
    (pprint-newline :mandatory)))

(defmethod pp-tex* :around ((decl number-judgement))
  (with-slots (number chain? declared-type) decl
    (when (or (not *pretty-printing-decl-list*)
	      (not *pretty-printed-prefix*))
      (when *pretty-printing-decl-list*
	(setq *pretty-printed-prefix* t))
      (pp-tex-keyword 'JUDGEMENT)
      (write-char #\space)
      (pprint-newline :miser))
    (pp-tex* number)
    (cond ((and chain?
		*pretty-printing-decl-list*)
	   (write-char #\,)
	   (write-char #\space))
	  (t (write-char #\space)
	     (pp-tex-keyword 'HAS_TYPE)
	     (write-char #\space)
	     (pprint-newline :fill)
	     (pp-tex* declared-type)
	     (setq *pretty-printed-prefix* nil))))
    (pprint-newline :mandatory))

(defmethod pp-tex* :around ((decl subtype-judgement))
  (with-slots (declared-subtype chain? declared-type) decl
    (when (or (not *pretty-printing-decl-list*)
	      (not *pretty-printed-prefix*))
      (when *pretty-printing-decl-list*
	(setq *pretty-printed-prefix* t))
      (pp-tex-keyword 'JUDGEMENT)
      (write-char #\space)
      (pprint-newline :miser))
    (pp-tex* declared-subtype)
    (cond ((and chain?
		*pretty-printing-decl-list*)
	   (write-char #\,)
	   (write-char #\space))
	  (t (write-char #\space)
	     (pp-tex-keyword 'SUBTYPE_OF)
	     (write-char #\space)
	     (pprint-newline :fill)
	     (pp-tex* declared-type)
	     (setq *pretty-printed-prefix* nil)))
    (pprint-newline :mandatory)))

(defmethod pp-tex* :around ((decl conversion-decl))
  (with-slots (name chain?) decl
    (when (or (not *pretty-printing-decl-list*)
	      (not *pretty-printed-prefix*))
      (when *pretty-printing-decl-list*
	(setq *pretty-printed-prefix* t))
      (pp-tex-keyword 'CONVERSION)
      (write-char #\space)
      (pprint-newline :miser))
    (pp-tex* name)
    (when (typep decl 'typed-conversion-decl)
      (write-char #\:)
      (write-char #\space)
      (pp-tex* (declared-type decl)))
    (when (and chain?
	       *pretty-printing-decl-list*)
      (write-char #\,)
      (write-char #\space))
    (pprint-newline :mandatory)))


;;; Type expressions

(defmethod pp-tex* :around ((te type-expr))
  (if (print-type te)
      (pp-tex* (print-type te))
      (progn (dotimes (p (parens te))
	       (write-char #\[))
	     (call-next-method)
	     (dotimes (p (parens te))
	       (write-char #\])))))

(defmethod pp-tex* ((te type-application))
  (with-slots (type parameters) te
    (pprint-logical-block (nil nil)
      (pp-tex* type)
      (pp-tex-arguments parameters))))

(defun pp-tex-arguments* (args)
  (pprint-logical-block (nil args)
    (loop (pprint-indent :current 2)
	  (pp-tex-arguments (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (pprint-newline :fill))))

(defun pp-tex-arguments (args)
  (pprint-logical-block (nil args :prefix "(" :suffix ")")
    (pprint-indent :block 0)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :fill))))

(defmethod pp-tex* ((te subtype))
  (with-slots (supertype predicate contains) te
    (let* ((bindings (if (typep (predicate te) 'binding-expr)
			 (bindings (predicate te))
			 (let* ((id (make-new-variable '|x| te))
				(bd (mk-bind-decl id
				      (or (print-type (supertype te))
					  (supertype te)))))
			   (list bd))))
	   (expr (if (typep (predicate te) 'binding-expr)
		     (expression (predicate te))
		     (let ((var (mk-name-expr (id (car bindings)))))
		       (mk-application (predicate te) var)))))
      (pprint-logical-block (nil nil :prefix "{" :suffix "}")
	(pp-tex-bindings bindings)
	(write-char #\space)
	(write-char #\|)
	(write-char #\space)
	(pp-tex* expr))
      (when contains
	(write-char #\space)
	(pp-tex-keyword 'CONTAINING)
	(write-char #\space)
	(pp-tex* contains)))))

(defmethod pp-tex* ((te expr-as-type))
  (with-slots (expr contains) te
    (write-char #\()
    (pp-tex* expr)
    (write-char #\))
    (when contains
      (write-char #\space)
      (pp-tex-keyword 'CONTAINING)
      (write-char #\space)
      (pp-tex* contains))))

(defmethod pp-tex* ((te recordtype))
  (with-slots (fields) te
    (pprint-logical-block (nil fields :prefix "[# " :suffix " #]")
      (loop (pp-tex* (pprint-pop))
	    (pprint-exit-if-list-exhausted)
	    (write-char #\,)
	    (write-char #\space)
	    (pprint-newline :linear)))))

(defmethod pp-tex* ((te funtype))
  (with-slots (domain range) te
    (pprint-logical-block (nil nil :prefix "[" :suffix "]")
      (pprint-indent :current 2)
      (pp-tex-funtype domain range)
      (pprint-indent :block 0))))

(defmethod pp-tex-funtype (domain range)
  (pp-tex* domain)
  (write-char #\space)
  (pp-tex-keyword '->)
  (write-char #\space)
  (pprint-newline :fill)
  (pp-tex* range))

(defmethod pp-tex-funtype ((domain domain-tupletype) range)
  (with-slots (types) domain
    (pprint-logical-block (nil types)
      (pprint-indent :current 0)
      (loop (pp-tex* (pprint-pop))
	    (pprint-exit-if-list-exhausted)
	    (write-char #\,)
	    (write-char #\space)
	    (pprint-newline :fill)))
    (write-char #\space)
    (pp-tex-keyword '->)
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex* range)))

(defmethod pp-tex-funtype ((domain dep-binding) range)
  (with-slots (id declared-type) domain
    (if (typep declared-type 'dep-domain-tupletype)
	(let* ((types (types declared-type))
	       (bindings (var-bindings declared-type))
	       (tbindings bindings)
	       (*parsing-or-unparsing* t))
	  (pprint-logical-block (nil types)
	    (pprint-indent :current 0)
	    (loop (let ((nty (pprint-pop))
			(nbd (pop tbindings)))
		    (if (typep nty 'dep-binding)
			(pp-tex* nty)
			(pprint-logical-block (nil nil)
			  (pp-tex* (car nbd))
			  (write-char #\:)
			  (write-char #\space)
			  (pprint-newline :fill)
			  (pp-tex* nty))))
		  (pprint-exit-if-list-exhausted)
		  (write-char #\,)
		  (write-char #\space)
		  (pprint-newline :fill)))
	  (write-char #\space)
	  (pp-tex-keyword '->)
	  (write-char #\space)
	  (pprint-newline :fill)
	  (pp-tex* (gensubst range
		     #'(lambda (ex)
			 (let ((var (car (rassoc (index ex) bindings))))
			   (make-instance 'name-expr
			     'id var)))
		     #'(lambda (ex)
			 (and (typep ex 'projection-application)
			      (typep (argument ex) 'name-expr)
			      (eq (id (argument ex)) (id domain)))))))
	(call-next-method))))



(defmethod pp-tex* ((te tupletype))
  (with-slots (types) te
    (pprint-logical-block (nil types :prefix "[" :suffix "]")
      (pprint-indent :current 0)
      (loop (pp-tex* (pprint-pop))
	    (pprint-exit-if-list-exhausted)
	    (write-char #\,)
	    (write-char #\space)
	    (pprint-newline :fill)))))


;;; Expressions

(defmethod pp-tex* :around ((ex expr))
  (if (typep ex 'binding)
      (call-next-method)
      (progn (dotimes (p (parens ex))
	       (write-char #\())
	     (call-next-method)
	     (dotimes (p (parens ex))
	       (write-char #\))))))

(defmethod pp-tex* ((ex number-expr))
  (unless *in-tex-math-mode*
    (write "\\("))
  (write (number ex))
  (unless *in-tex-math-mode*
    (write "\\)")))

(defmethod pp-tex* ((ex string-expr))
  (unless (string-value ex)
    (setf (string-value ex) (get-string-value (argument ex))))
  (write (string-value ex) :escape t))

(defun get-string-value (charlist &optional list)
  (if (typep charlist 'name-expr)
      (coerce (nreverse list) 'string)
      (get-string-value
       (args2 charlist)
       (nconc (get-string-char (number (args1 (args1 charlist)))) list))))

(defun get-string-char (code)
  (let ((char (code-char code)))
    (case char
      (#-gcl #\Bell #+gcl #\^G (list #\a #\\ #\\))
      (#\Backspace (list #\b #\\ #\\))
      (#\Page (list #\f #\\ #\\))
      (#\Newline (list #\n #\\ #\\))
      (#\Return (list #\r #\\ #\\))
      (#\Tab (list #\t #\\ #\\))
      (#-gcl #\VT #+gcl #\^K (list #\v #\\ #\\))
      (#\" (list #\" #\\ #\\))
      (#\\ (list #\\ #\\ #\\ #\\))
      (t (if (graphic-char-p char)
	     (list char)
	     (nreverse (cons #\\ (cons #\\ (coerce (format nil "~o" code)
						   'list)))))))))

(defmethod pp-tex* ((ex list-expr))
  (pprint-logical-block (nil (exprs ex) :prefix "(: " :suffix " :)")
    (pprint-indent :current 0)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :linear))))

(defmethod pp-tex* ((ex null-expr))
  (pp-tex-keyword '|(:|)
  (pp-tex-keyword '|:)|))

(defmethod pp-tex* ((ex bracket-expr))
  (pprint-logical-block (nil (arguments ex) :prefix "[| " :suffix " |]")
    (pprint-indent :current 0)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :linear))))

(defmethod pp-tex* ((ex record-expr))
  (with-slots (assignments) ex
    (pprint-logical-block (nil assignments :prefix "(# " :suffix " #)")
      (pprint-indent :current 0)
      (loop (pp-tex* (pprint-pop))
	    (pprint-exit-if-list-exhausted)
	    (write-char #\,)
	    (write-char #\space)
	    (pprint-newline :linear)))))

(defmethod pp-tex* ((ex tuple-expr))
  (with-slots (exprs) ex
    (pp-tex-arguments exprs)))

(defmethod pp-tex* ((ex projection-application))
  (with-slots (id argument) ex
    (pp-tex-id id)
    (pp-tex-arguments (argument-list argument))))

(defmethod pp-tex* ((ex field-application))
  (with-slots (id argument) ex
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex-id id)
      (pprint-newline :fill)
      (pp-tex-arguments (argument-list argument)))))

(defmethod pp-tex* :around ((ex application))
  (with-slots (operator argument) ex
    (let* ((args (argument* ex))
	   (arglengths (mapcar #'(lambda (arg)
				   (if (typep arg 'tuple-expr)
				       (length (exprs arg))
				       1))
			 args))
	   (appltrans (get-pp-tex-funsym operator arglengths)))
      (cond (appltrans
	     (unless *in-tex-math-mode*
	       (write "\\("))
	     (let ((*in-tex-math-mode* t))
	       (dotimes (p (parens ex))
		 (write-char #\())
	       (write appltrans)
	       (dolist (arg args)
		 (cond ((typep arg 'tuple-expr)
			(dolist (a (exprs arg))
			  (write "{")
			  (pp-tex* a)
			  (write "}")))
		       (t (write "{")
			  (pp-tex* arg)
			  (write "}"))))
	       (dotimes (p (parens ex))
		 (write-char #\))))
	     (unless *in-tex-math-mode*
	       (write "\\)")))
	    (t (call-next-method))))))

(defmethod pp-tex* ((ex application))
  (with-slots (operator argument) ex
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex* operator)
      (pprint-newline :miser)
      (pp-tex-arguments (argument-list argument)))))

(defmethod pp-tex* ((ex infix-application))
  (with-slots (operator argument) ex
    (if (and (typep operator 'name-expr)
	     (memq (id operator) *infix-operators*)
	     (typep argument 'tuple-expr)
	     (= (length (exprs argument)) 2))
	(progn
	  (set-parens-if-needed ex)
	  (pprint-logical-block (nil nil)
	    (pprint-indent :block 1)
	    (pp-tex* (args1 ex))
	    (write-char #\space)
	    (pprint-newline :fill)
	    (pp-tex-id (id operator)
		       (when (resolution operator)
			 (id (module-instance operator))))
	    (write-char #\space)
	    (pprint-newline :fill)
	    (pp-tex* (args2 ex))))
	(call-next-method))))

(defmethod pp-tex* ((ex unary-application))
  (with-slots (operator argument) ex
    (if (and (typep operator 'name-expr)
	     (memq (id operator) *unary-operators*))
	(pprint-logical-block (nil nil)
	  (pprint-indent :current 2)
	  (pp-tex-id (id operator))
	  (when (valid-pvs-id* (id operator))
	    (write-char #\space)
	    (pprint-newline :miser))
	  (pp-tex* argument)))))

(defmethod pp-tex* ((ex binding-application))
  (with-slots (operator argument) ex
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex-id (id operator))
      (write-char #\!)
      (write-char #\space)
      (pprint-newline :miser)
      (pp-tex-bindings (bindings argument))
      (write-char #\:)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex* (expression argument)))))

(defmethod pp-tex* ((ex when-expr))
  (with-slots (operator argument) ex
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex* (args2 ex))
      (write-char #\space)
      (pprint-newline :miser)
      (pp-tex-id 'when)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex* (args1 ex)))))

(defmethod pp-tex* ((ex if-expr))
  (pprint-logical-block (nil nil)
    (pprint-indent :current 2)
    (pp-tex-keyword 'if)
    (write-char #\space)
    (pp-tex* (condition ex))
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex-keyword 'then)
    (write-char #\space)
    (pp-tex* (then-part ex))
    (write-char #\space)
    (pprint-indent :block 0)
    (pprint-newline :linear)
    (cond ((typep (else-part ex) 'chained-if-expr)
	   (pp-tex-keyword 'elsif)
	   (pp-tex-chained-if-expr (else-part ex) nil))
	  (t (pp-tex-keyword 'else)
	     (write-char #\space)
	     (pp-tex* (else-part ex))))
    (unless (typep (else-part ex) 'chained-if-expr)
      (write-char #\space)
      (pprint-newline :linear)
      (pp-tex-keyword 'endif))))

(defmethod pp-tex* ((ex chained-if-expr))
  (pp-tex-chained-if-expr ex t))

(defun pp-tex-chained-if-expr (ex print-if?)
  (pprint-logical-block (nil nil)
    (pprint-indent :current 2)
    (when print-if?
      (pp-tex-keyword 'if))
    (write-char #\space)
    (pp-tex* (condition ex))
    (write-char #\space)
    (pprint-newline :fill)
    (pp-tex-keyword 'then)
    (write-char #\space)
    (pp-tex* (then-part ex))
    (write-char #\space)
    (pprint-indent :block 0)
    (pprint-newline :linear)
    (pp-tex-keyword 'else)
    (write-char #\space)
    (pp-tex* (else-part ex))
    (write-char #\space)
    (pprint-newline :linear)
    (pp-tex-keyword 'endif)))

(defmethod pp-tex* ((ex coercion))
  (with-slots (argument operator) ex
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex* argument)
      (write-char #\:)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex* (declared-type (car (bindings operator)))))))

(defmethod pp-tex* ((ex binding-expr))
  (let ((*pretty-printing-decl-list* t))
    (pprint-logical-block (nil nil)
      (unless (chain? ex)
	(pp-tex-keyword (operator ex))
	(write-char #\space)
	(pprint-indent :current 0)
	(pprint-newline :miser)
	(pp-tex-lambda-formals ex)
	(write-char #\:)
	(write-char #\space))
      (pprint-indent :block 2)
      (pprint-newline :fill)
      (pp-tex* (expression ex)))))

(defmethod pp-tex* ((ex set-expr))
  (with-slots (bindings expression) ex
    (pprint-logical-block (nil nil :prefix "{" :suffix "}")
      (pprint-indent :current 2)
      (pp-tex-bindings bindings)
      (write-char #\space)
      (pprint-newline :fill)
      (write-char #\|)
      (write-char #\space)
      (pp-tex* expression))))

(defmethod pp-tex* ((ex let-expr))
  (multiple-value-bind (let-bindings expr)
      (get-let-bindings ex)
    (pprint-logical-block (nil nil)
      (pp-tex-keyword 'let)
      (write-char #\space)
      (pp-tex-let-bindings let-bindings)
      (write-char #\space)
      (pprint-indent :block 2)
      (pprint-newline :fill)
      (pp-tex-keyword 'in)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex* expr))))

(defun pp-tex-let-bindings (let-bindings)
  (pprint-logical-block (nil let-bindings)
    (loop (let ((lb (pprint-pop)))
	    (pp-tex-bindings (car lb))
	    (write-char #\space)
	    (pp-tex-keyword '=)
	    (write-char #\space)
	    (pp-tex* (cdr lb)))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :linear))))

(defmethod pp-tex* ((ex where-expr))
  (multiple-value-bind (where-bindings expr)
      (get-where-bindings ex)
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex* expr)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex-keyword 'where)
      (write-char #\space)
      (pp-tex-let-bindings where-bindings))))

(defmethod pp-tex* ((ex update-expr))
  (with-slots (expression assignments) ex
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex* expression)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex-keyword 'with)
      (write-char #\space)
      (pprint-logical-block (nil assignments :prefix "[" :suffix "]")
	(pprint-indent :current 0)
	(loop (pp-tex* (pprint-pop))
	      (pprint-exit-if-list-exhausted)
	      (write-char #\,)
	      (write-char #\space)
	      (pprint-newline :linear))))))

(defmethod pp-tex* ((ex cond-expr))
  (pp-tex-cond-expr ex))

(defmethod pp-tex* ((ex first-cond-expr))
  (pp-tex-cond-expr ex))

(defmethod pp-tex* ((ex single-cond-expr))
  (pp-tex-cond-expr ex))

(defmethod pp-tex* ((ex last-cond-expr))
  (pp-tex-cond-expr ex))

(defun pp-tex-cond-expr (ex)
  (let ((pairs (collect-cond-expr-pairs ex nil)))
    (pprint-logical-block (nil nil)
      (pp-tex-keyword 'cond)
      (write-char #\space)
      (pprint-newline :miser)
      (pprint-logical-block (nil pairs)
	(loop (let ((pair (pprint-pop)))
		(pp-tex* (car pair))
		(write-char #\space)
		(pprint-newline :miser)
		(pp-tex-keyword '->)
		(write-char #\space)
		(pprint-newline :miser)
		(pp-tex* (cdr pair))
		(pprint-exit-if-list-exhausted)
		(write-char #\,)
		(write-char #\space)
		(pprint-newline :linear))))
      (write-char #\space)
      (pprint-newline :linear)
      (pp-tex-keyword 'endcond))))

(defmethod pp-tex* ((ex else-condition))
  (pp-tex-keyword 'else))

(defmethod pp-tex* ((ex cases-expr))
  (with-slots (expression selections else-part) ex
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex-keyword 'cases)
      (write-char #\space)
      (pp-tex* expression)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex-keyword 'of)
      (write-char #\space)
      (pprint-logical-block (nil selections)
	(loop (pp-tex* (pprint-pop))
	      (pprint-exit-if-list-exhausted)
	      (write-char #\,)
	      (write-char #\space)
	      (pprint-newline :linear)))
      (when else-part
	(write-char #\space)
	(pprint-newline :linear)
	(pp-tex-keyword 'else)
	(write-char #\space)
	(pp-tex* else-part))
      (write-char #\space)
      (pprint-newline :linear)
      (pp-tex-keyword 'endcases))))
      
(defmethod pp-tex* ((sel selection))
  (with-slots (constructor args expression) sel
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex* constructor)
      (when args
	(pp-tex-arguments args))
      (write-char #\:)
      (write-char #\space)
      (pprint-newline :fill)
      (pp-tex* expression))))

(defmethod pp-tex* ((ass assignment))
  (with-slots (arguments expression) ass
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (if (typep ass 'uni-assignment)
	  (pp-tex* (caar arguments))
	  (pp-tex-arguments* arguments))
      (write-char #\space)
      (pprint-newline :miser)
      (pp-tex-keyword '|:=|)
      (write-char #\space)
      (pp-tex* expression))))

(defmethod pp-tex* ((ass maplet))
  (with-slots (arguments expression) ass
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (if (typep ass 'uni-assignment)
	  (pp-tex* (caar arguments))
	  (pp-tex-arguments* arguments))
      (write-char #\space)
      (pprint-newline :miser)
      (pp-tex-keyword '|\|->|)
      (write-char #\space)
      (pp-tex* expression))))

(defmethod pp-tex* ((ex implicit-conversion))
  (pp-tex* (argument ex)))

(defmethod pp-tex* ((ex table-expr))
  (with-slots (row-expr col-expr row-headings col-headings table-entries) ex
    (pp-tex-table-expr row-expr col-expr row-headings col-headings
		       table-entries)))

(defmethod pp-tex* ((ex cond-table-expr))
  (with-slots (row-expr col-expr row-headings col-headings table-entries) ex
    (pp-tex-table-expr row-expr col-expr row-headings col-headings
		       table-entries)))

(defmethod pp-tex* ((ex cases-table-expr))
  (with-slots (row-expr col-expr row-headings col-headings table-entries) ex
    (pp-tex-table-expr row-expr col-expr row-headings col-headings
		       table-entries)))

(defmethod pp-tex* ((ex let-table-expr))
  (with-slots (row-expr col-expr row-headings col-headings table-entries) ex
    (pp-tex-table-expr row-expr col-expr row-headings col-headings
		       table-entries)))

(defun pp-tex-table-expr (row-expr col-expr row-headings col-headings
				   table-entries)
  (pprint-logical-block (nil nil)
    (pp-tex-keyword 'table)
    (write-char #\space)
    (pprint-newline :miser)
    (when row-expr
      (pp-tex* row-expr))
    (when col-expr
      (write-char #\,)
      (write-char #\space)
      (pprint-newline :miser)
      (pp-tex* col-expr))
    (pprint-indent :block 2)
    (pprint-newline :mandatory)
    (format t "\\end{alltt}~%\\begin{tabular}{|*{~d}{c|}}\\hline~%"
      (1+ (length (car table-entries))))
    (let ((rows (if row-headings
		    (mapcar #'cons row-headings table-entries)
		    table-entries)))
      (when col-headings
	(write-char #\&)
	(pprint-logical-block (nil col-headings)
	  (loop (pp-tex* (pprint-pop))
		(pprint-exit-if-list-exhausted)
		(write-char #\&)))
	(format t "\\\\\\hline~%")
	(pprint-newline :mandatory))
      (pprint-logical-block (nil rows)
	(loop (let ((row (pprint-pop)))
		(pprint-logical-block (nil row)
		  (loop (pp-tex* (pprint-pop))
			(pprint-exit-if-list-exhausted)
			(write-char #\&)))
		(pprint-exit-if-list-exhausted)
		(format t "\\\\\\hline~%")
		(pprint-newline :mandatory))))
      (pprint-indent :block 0)
      (format t "\\\\\\hline~%\\end{tabular}~%\\begin{alltt}~%")
      (pprint-newline :mandatory)
      (pp-tex-keyword 'endtable))))

(defun pp-tex-bindings (bindings)
  (pprint-logical-block (nil bindings)
    (pprint-indent :current 0)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :linear))))

(defmethod pp-tex* ((d simple-decl))
  (with-slots (id declared-type) d
    (pprint-logical-block (nil nil)
      (pprint-indent :current 2)
      (pp-tex-id id)
      (when declared-type
	(write-char #\:)
	(write-char #\space)
	(pprint-newline :fill)
	(pp-tex* declared-type)))))

(defmethod pp-tex* ((ex name))
  (with-slots (library mod-id actuals id resolutions) ex
    (pprint-logical-block (nil (list ex))
      (when library
	(pp-tex-id library)
	(write-char #\@))
      (cond (mod-id
	     (pp-tex-id mod-id)
	     (when actuals
	       (pp-tex-actuals actuals))
	     (write-char #\.)
	     (pp-tex-id id))
	    (t
	     (pp-tex-id id)
	     (when actuals
	       (pp-tex-actuals actuals)))))))

(defmethod pp-tex* ((list list))
  (let ((*pretty-printing-decl-list* t)
	(*pretty-printed-prefix* nil))
    (dolist (elt list)
      (pp-tex* elt))))

(defun pp-tex-actuals (actuals)
  (pprint-logical-block (nil actuals :prefix "[" :suffix "]")
    (pprint-indent :current 0)
    (loop (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :linear))))

(defmethod pp-tex* ((act actual))
  (with-slots (expr) act
    (pp-tex* expr)))

(defun pp-tex-lambda-formals (expr)
  (pp-tex-lambda-formal (pp-tex-chained-decls (bindings expr))
		    (commas? expr)
		    (set-expr? (typep expr 'set-expr)))
  (when (and (typep (expression expr) 'lambda-expr)
	     (chain? (expression expr)))
    (pp-tex-lambda-formals (expression expr))))

(defun pp-tex-lambda-formal (bindings commas? &optional set-expr?)
  (if commas?
      (if (cdr bindings)
	  (pprint-logical-block (nil nil)
	    (if (or (cdr (car bindings))
		    (and (declared-type (caar bindings))
			 (not (typep (caar bindings) 'untyped-bind-decl))))
		(pp-tex-lambda-adformals (car bindings))
		(if set-expr?
		    (pprint-logical-block (nil nil)
		      (pp-tex-id (id (caar bindings)))
		      (when (and (declared-type (caar bindings))
				 (not (typep (caar bindings)
					     'untyped-bind-decl)))
			(write-char #\:)
			(write-char #\space)
			(pp (declared-type (caar bindings)))))
		    (if (typep (caar bindings) 'untyped-bind-decl)
			(pprint-logical-block (nil nil :prefix "(" :suffix ")")
			  (pp-tex-id (id (caar bindings))))
			(pp-tex-id (id (caar bindings))))))
	    (write-char #\,)
	    (write-char #\space)
	    (pprint-newline :fill)
	    (pp-tex-lambda-formal (cdr bindings) commas? set-expr?))
	  (if (and set-expr?
		   (zerop (parens (caar bindings))))
	      (if (cdar bindings)
		  (pp-tex-lambda-formal (mapcar #'list (car bindings))
				    commas? set-expr?)
		  (pprint-logical-block (nil nil)
		    (pp-tex-id (id (caar bindings)))
		    (when (declared-type (caar bindings))
		      (write-char #\:)
		      (write-char #\space)
		      (pp (declared-type (caar bindings))))))
	      (if (or (cdr (car bindings))
		      (declared-type (caar bindings)))
		  (pprint-logical-block (nil nil :prefix "(" :suffix ")")
		    (pp-tex-paren-adformals* (car bindings)))
		  (pp-tex-id (id (caar bindings))))))
      (if (and set-expr?
	       (zerop (parens (caar bindings))))
	  (pprint-logical-block (nil nil)
	    (pp-tex-id (id (caar bindings)))
	    (when (declared-type (caar bindings))
	      (write-char #\:)
	      (write-char #\space)
	      (pp (declared-type (caar bindings)))))
	  (pp-tex-paren-adformals bindings))))

(defun pp-tex-paren-adformals (bindings)
  (pprint-logical-block (nil bindings :prefix "(" :suffix ")")
    (loop (pp-tex-paren-adformals* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (write-char #\,)
	  (write-char #\space)
	  (pprint-newline :fill))))

(defun pp-tex-paren-adformals* (b &optional (parens (parens (car b))))
  (if (zerop parens)
      (pprint-logical-block (nil nil)
	(mapl #'(lambda (bb)
		  (if (or (cdr bb)
			  (not (chain? (car bb)))
			  (not (typep (car bb) 'untyped-bind-decl)))
		      (pp-tex* (car bb))
		      (pp-tex-bind-decl (car bb)))
		  (when (cdr bb)
		    (write-char #\,)
		    (write-char #\space)
		    (pprint-newline :fill)))
	      b))
      (pprint-logical-block (nil nil :prefix "(" :suffix ")")
	(pp-tex-paren-adformals* b (1- parens)))))

(defun pp-tex-lambda-adformals (bindings)
  (pprint-logical-block (nil bindings :prefix "(" :suffix ")")
    (loop (pprint-indent :current 2)
	  (pp-tex* (pprint-pop))
	  (pprint-exit-if-list-exhausted)
	  (pprint-newline :fill))))

;(defun pp-typed-ids (bindings)
;  (pprint-logical-block (nil bindings)
;    (loop (pprint-indent :current 2)
;	  (write (id (pprint-pop)))
;	  (pprint-exit-if-list-exhausted)
;	  (write-char #\,)
;	  (write-char #\space)
;	  (pprint-newline :linear)))
;  (write-char #\:)
;  (write-char #\space)
;  (pp-tex* (declared-type (car (last bindings)))))

(defmethod pp-tex* ((bd untyped-bind-decl))
  (pp-tex-id (id bd)))

(defmethod pp-tex* ((bd bind-decl))
  (pp-tex-bind-decl bd))

(defun pp-tex-bind-decl (bd)
  (pprint-logical-block (nil nil)
    (pp-tex-id (id bd))
    (when (and (declared-type bd)
	       (not (chain? bd)))
      (cond ((pred-bind-decl? bd)
	     (when (supertype (declared-type bd))
	       (write-char #\:)
	       (write-char #\space)
	       (pprint-newline :linear)
	       (pp-tex* (supertype (declared-type bd))))
	     (write-char #\space)
	     (write-char #\|)
	     (write-char #\space)
	     (pp-tex* (formula (declared-type bd))))
	    (t (pprint-indent :block 2)
	       (write-char #\:)
	       (write-char #\space)
	       (pprint-newline :linear)
	       (pp-tex* (declared-type bd)))))))

(defun pp-tex-chained-decls (decls &optional cdecls part)
  (if (null decls)
      (nreverse (if cdecls (cons (nreverse cdecls) part) part))
      (let ((chainp (and (typep (car decls) '(and (not arg-bind-decl)
					      (or declaration bind-decl)))
			 (chain? (car decls))
			 (or (not (typep (car decls)
					 '(or typed-declaration bind-decl)))
			     (declared-type (car decls))))))
	(pp-tex-chained-decls
	 (cdr decls)
	 (when chainp
	   (cons (car decls) cdecls))
	 (cond (chainp
		part)
	       ((typep (car decls) 'importing)
		(cons (car decls)
		      (if cdecls (cons (nreverse cdecls) part) part)))
	       ((and cdecls
		     (or (and (typep (car cdecls)
				     '(or typed-declaration bind-decl))
			      (declared-type (car cdecls))
			      (typep (car decls)
				     '(or typed-declaration bind-decl))
			      (declared-type (car decls))
			      (ps-eq (declared-type (car cdecls))
				     (declared-type (car decls))))
			 (and (typep (car cdecls) 'type-decl)
			      (typep (car decls) 'type-decl))))
		(cons (nreverse (cons (car decls) cdecls)) part))
	       (t (cons (list (car decls))
			(if cdecls (cons (nreverse cdecls) part) part))))))))
  
(defmethod pp-tex* ((ex symbol))
  (break)
  (write ex))


;;;;; Substitutions

; Identifier  Type  Length  Substitution
; ----------  ----  ------  ------------
; THEORY      key     9     {\large\bf Theory}
; f1          id      3     {\rm bar}
; f2          id[2]   2     {#2_{#1}^{f}}
; f3          2       2     {#1^#2}
; f4          (1 2)   3     {\sum_{i=#2}^{#3}#1(i,#2)}

(defun pp-tex-id (id &optional theory-id)
  (write (get-pp-tex-id id theory-id)))

(defun get-pp-tex-id (symbol &optional theory-id)
  (let* ((msymbol (makesym "~a%" symbol))
	 (thsym (when theory-id (makesym "~a.~a" theory-id symbol)))
	 (mthsym (when theory-id (makesym "~a%" thsym)))
	 (tr (if thsym
		 (if *in-tex-math-mode*
		     (gethash thsym *latex-id-strings*)
		     (gethash mthsym *latex-id-strings*))
		 (if *in-tex-math-mode*
		     (gethash symbol *latex-id-strings*)
		     (gethash msymbol *latex-id-strings*)))))
    (or tr
	(let* ((itrans (or (when thsym
			     (cdr (assq thsym *latex-id-macro-list*)))
			   (cdr (assq symbol *latex-id-macro-list*))))
	       (needs-math (and (not *in-tex-math-mode*) itrans))
	       (trans (or itrans
			  (get-pp-tex-id* symbol)))
	       (len (or (when thsym
			  (cdr (assq thsym *latex-id-length-list*)))
			(cdr (assq symbol *latex-id-length-list*))
			(length (string symbol))))
	       (str (make-new-tex-string len))
	       (strans (if needs-math
			   (format nil "\\(~a\\)" trans)
			   trans)))
	  (setf (gethash (if *in-tex-math-mode*
			     (or thsym symbol)
			     (or mthsym msymbol))
			 *latex-id-strings*)
		str)
	  (setf (gethash str *pvs-tex-substitution-hash*) strans)
	  str))))

(defun get-pp-tex-id* (symbol)
  (let ((str (string symbol)))
    (cond ((and (alpha-char-p (char str 0))
		(every #'digit-char-p (subseq str 1)))
	   (if (= (length str) 1)
	       (if *in-tex-math-mode*
		   str
		   (format nil "\\(~a\\)" str))
	       (format nil "~:[\\(~;~]~c\\sb{~a}~:[\\)~;~]"
		 *in-tex-math-mode* (char str 0) (subseq str 1)
		 *in-tex-math-mode*)))
	  ((find #\! str)
	   (let ((pos (position #\! str)))
	     (if (and (= (- (length str) pos) 2)
		      (digit-char-p (elt str (1+ pos))))
		 (format nil "~:[\\(~;~]~,,v,''a~:[\\)~;~]"
		   *in-tex-math-mode*
		   (parse-integer (subseq str (1+ pos)))
		   (let ((*in-tex-math-mode* t))
		     (get-pp-tex-id* (subseq str 0 pos)))
		   *in-tex-math-mode*)
		 (format nil "\\pvsid{~a}" (latex-protect str)))))
	  (t (format nil "\\pvsid{~a}" (latex-protect str))))))

(defmethod get-pp-tex-funsym ((op name-expr) arglengths &optional theory-id)
  (get-pp-tex-funsym (id op) arglengths theory-id))

(defmethod get-pp-tex-funsym (ex arglengths &optional theory-id)
  (declare (ignore ex arglengths))
  nil)

(defmethod get-pp-tex-funsym ((symbol symbol) arglengths &optional theory-id)
  (let* ((symargs (cons symbol arglengths))
	 (thsym (when theory-id (makesym "~a.~a" theory-id symbol)))
	 (thsymargs (when theory-id (cons thsym arglengths))))
    (multiple-value-bind (texstr there?)
	(if thsym
	    (gethash thsymargs *latex-funsym-strings*)
	    (gethash symargs *latex-funsym-strings*))
      (if there?
	  texstr
	  (let* ((trans (or (when thsym
			     (cdr (assoc thsymargs *latex-fun-sym-macro-list*
					 :test #'equal)))
			   (cdr (assoc symargs *latex-fun-sym-macro-list*
				       :test #'equal))))
		 (len (when trans
			(or (when thsym
			      (cdr (assoc thsymargs *latex-fun-sym-length-list*
					  :test #'equal)))
			    (cdr (assoc symargs *latex-fun-sym-length-list*
					:test #'equal)))))
		 (str (when trans (make-new-tex-string len))))
	    (setf (gethash (or thsymargs symargs) *latex-funsym-strings*)
		  trans)
	    (when trans
	      (setf (gethash str *pvs-tex-substitution-hash*) trans)
	      str))))))

(defun pp-tex-keyword (symbol)
  (write (get-pp-tex-keyword symbol)))

(defun get-pp-tex-keyword (symbol)
  (let ((texstr (gethash symbol *latex-keyword-strings*)))
    (or texstr
	(setf (gethash symbol *latex-keyword-strings*)
	      (let* ((ktrans (cdr (assq symbol *latex-keyword-list*)))
		     (trans (if ktrans
				(if *in-tex-math-mode*
				    ktrans
				    (format nil "\\(~a\\)" ktrans))
				(format nil "\\pvskey{~a}" symbol)))
		     (len (or (cdr (assq symbol *latex-keyword-length-list*))
			      (length (string symbol))))
		     (str (make-new-tex-string len)))
		(setf (gethash str *pvs-tex-substitution-hash*) trans)
		str)))))



(defun make-new-tex-string (length)
  (let ((cnt (get-next-tex-symbol-counter length))
	(str (make-string length :initial-element (code-char 127))))
    (if (and (= length 1) (> cnt 128))
	(make-new-tex-string 2)
	(make-new-tex-string* str (1- length) cnt))))

(defun make-new-tex-string* (str pos cnt)
  (if (zerop cnt)
      str
      (multiple-value-bind (q r)
	  (floor cnt 129)
	(setf (char str pos) (code-char (+ r 127)))
	(make-new-tex-string* str (1- pos) q))))

(defun get-next-tex-symbol-counter (length)
  (let ((counter (assoc length *tex-symbol-counters* :test #'=)))
    (cond (counter (incf (cdr counter)))
	  (t (push (cons length 0) *tex-symbol-counters*)
	     0))))
