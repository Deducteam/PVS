;;; -*- Mode: LISP; Syntax: Common-lisp; Package: VERSE -*-

;------------------------------------------------------------------------------
; PRMACROS - Macros for the prover subsystem
;------------------------------------------------------------------------------


(defmacro newcontext (form)
  `(let ((sigalist sigalist) (findalist findalist) (usealist usealist))
     (catch 'context 
       ,form )))

(defmacro retfalse () `(throw 'context 'false))

; term accessor macros

(defmacro funsym (term) `(car ,term))

(defmacro arg1 (term) `(cadr ,term))

(defmacro arg2 (term) `(caddr ,term))

(defmacro arg3 (term) `(cadddr ,term))

(defmacro argsof (term) `(cdr ,term))

(defmacro lside (term) `(cadr ,term))

(defmacro rside (term) `(caddr ,term))

; getq:
; (getq arg alist) returns the item associated with arg in alist, or nil.

(defmacro getq (arg alist) `(cdr (assq ,arg ,alist)))

(defun prerr (&rest args)
  (apply #'error args))

(defconstant *truecons* '(true))

(defconstant *eqarithrels* '(greatereqp lesseqp))

(defconstant *ifops* '(if if*))

(defconstant *boolconstants* '(false true))

(defconstant *arithrels* '(lessp lesseqp greaterp greatereqp))

(defconstant *arithops* '(plus times difference minus))

(defconstant *boolops* '(and or implies not if iff))

