;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; occurs-in.lisp -- 
;; Author          : Sam Owre
;; Created On      : Sun Jan 16 22:08:45 1994
;; Last Modified By: Sam Owre
;; Last Modified On: Thu Oct 29 22:50:42 1998
;; Update Count    : 9
;; Status          : Unknown, Use with caution!
;; 
;; HISTORY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package 'pvs)

(defmethod occurs-in (x y)
  (when (eql x y) y))

(defmethod occurs-in (obj (l list))
  (when l
    (or (occurs-in obj (car l))
	(occurs-in obj (cdr l)))))

(defmethod occurs-in (obj (te type-name))
  (if (tc-eq obj te)
      te
      (call-next-method)))

(defmethod occurs-in (obj (te adtdecl))
  (occurs-in obj (type te)))

(defmethod occurs-in (obj (te dep-binding))
  (occurs-in obj (type te)))

(defmethod occurs-in ((obj declaration) (te type-name))
  (or (when (eq obj (declaration te))
	te)
      (call-next-method)))

(defmethod occurs-in (obj (te expr-as-type))
  (if (tc-eq obj te)
      te
      (occurs-in obj (expr te))))

(defmethod occurs-in (obj (te subtype))
  (or (when (tc-eq obj te)
	te)
      (occurs-in obj (print-type te))
      (occurs-in obj (supertype te))
      (occurs-in obj (predicate te))))

(defmethod occurs-in (obj (te funtype))
  (or (when (tc-eq obj te)
	te)
      (occurs-in obj (domain te))
      (occurs-in obj (range te))))

(defmethod occurs-in (obj (te tupletype))
  (or (when (tc-eq obj te)
	te)
      (occurs-in obj (types te))))

(defmethod occurs-in (obj (te recordtype))
  (or (when (tc-eq obj te)
	te)
      (occurs-in obj (fields te))))


;;; Recurse on the range, otherwise we will never terminate.

(defmethod occurs-in ((obj name) (fd field-decl))
  (or (when (same-declaration obj fd)
	fd)
      (occurs-in obj (type fd))))

(defmethod occurs-in (obj (fd field-decl))
  (occurs-in obj (type fd)))


;;; Expressions

(defmethod occurs-in ((obj name) (ex name-expr))
  (or (when (same-declaration obj ex)
	ex)
      (call-next-method)))

(defmethod occurs-in (obj (ex name-expr))
  (call-next-method))

(defmethod occurs-in ((decl field-decl) (ex name-expr))
  (when (eq decl (declaration ex))
    ex))

(defmethod occurs-in ((decl declaration) (ex name-expr))
  (when (eq decl (declaration ex))
    ex))

(defmethod occurs-in (obj (ex number-expr))
  (when (tc-eq obj ex) ex))

(defmethod occurs-in (obj (ex record-expr))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (assignments ex))))

(defmethod occurs-in (obj (ex tuple-expr))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (exprs ex))))

;(defmethod occurs-in (obj (ex coercion))
;  (or (when (tc-eq obj ex) ex)
;      (occurs-in obj (expression ex))
;      (occurs-in obj (type ex))))

;(defmethod occurs-in (obj (ex intype))
;  (or (when (tc-eq obj ex) ex)
;      (occurs-in obj (expression ex))
;      (occurs-in obj (type-value ex))))

(defmethod occurs-in (obj (ex projection-application))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (argument ex))))

(defmethod occurs-in (obj (ex field-application))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (argument ex))))

(defmethod occurs-in (obj (ex application))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (operator ex))
      (occurs-in obj (argument ex))))

(defmethod occurs-in (obj (ex binding-expr))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (bindings ex))
      (occurs-in obj (expression ex))))

(defmethod occurs-in (obj (ex cases-expr))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (selections ex))
      (occurs-in obj (expression ex))))

(defmethod occurs-in (obj (ex selection))
  (or (occurs-in obj (expression ex))
      (occurs-in obj (constructor ex))))

(defmethod occurs-in (obj (ex update-expr))
  (or (when (tc-eq obj ex) ex)
      (occurs-in obj (expression ex))
      (occurs-in obj (assignments ex))))

(defmethod occurs-in (obj (ass assignment))
  (or (when (tc-eq obj ass) ass)
      (occurs-in obj (arguments ass))
      (occurs-in obj (expression ass))))

(defmethod occurs-in (obj (bd bind-decl))
  (or (when (tc-eq obj bd) bd)
      (occurs-in obj (type bd))))

(defmethod occurs-in ((decl declaration) (bd bind-decl))
  (or (when (eq decl bd) bd)
      (occurs-in decl (type bd))))

(defmethod occurs-in (obj (nm name))
  (or (when (tc-eq obj nm) nm)
      (occurs-in obj (actuals nm))))

(defmethod occurs-in (obj (act actual))
  (or (when (tc-eq obj act) act)
      (if (type-value act)
	  (occurs-in obj (type-value act))
	  (occurs-in obj (expr act)))))

;;; ps-occurs-in method

(defmethod ps-occurs-in (type1 (list list))
  (some@ #'(lambda (ty) (ps-occurs-in type1 ty)) list))

(defmethod ps-occurs-in (type1 (type2 type-name))
  (or (ps-eq type1 type2)
      (ps-occurs-in type1 (actuals type2))))

(defmethod ps-occurs-in (type1 (type2 expr-as-type))
  (or (ps-eq type1 type2)
      (ps-occurs-in type1 (expr type2))))

(defmethod ps-occurs-in (type1 (type2 subtype))
  (or (ps-eq type1 type2)
      (ps-occurs-in type1 (supertype type2))))

(defmethod ps-occurs-in (type1 (type2 funtype))
  (or (ps-eq type1 type2)
      (ps-occurs-in type1 (domain type2))
      (ps-occurs-in type1 (range type2))))

(defmethod ps-occurs-in (type1 (type2 tupletype))
  (or (ps-eq type1 type2)
      (ps-occurs-in type1 (types type2))))

(defmethod ps-occurs-in (type1 (type2 recordtype))
  (or (ps-eq type1 type2)
      (some@ #'(lambda (fld) (ps-occurs-in type1 (type fld)))
	    (fields type2))))

(defmethod ps-occurs-in (type1 (act actual))
  (ps-occurs-in type1 (expr act)))

;;; Expressions

(defmethod ps-occurs-in (type1 (expr number-expr))
  nil)

(defmethod ps-occurs-in (type1 (expr record-expr))
  (ps-occurs-in type1 (assignments expr)))

(defmethod ps-occurs-in (type1 (expr tuple-expr))
  (ps-occurs-in type1 (exprs expr)))

(defmethod ps-occurs-in (type1 (expr projection-application))
  (ps-occurs-in type1 (argument expr)))

(defmethod ps-occurs-in (type1 (expr field-application))
  (ps-occurs-in type1 (argument expr)))

(defmethod ps-occurs-in (type1 (expr application))
  (or (ps-occurs-in type1 (operator expr))
      (ps-occurs-in type1 (argument expr))))

(defmethod ps-occurs-in (type1 (ex binding-expr))
  (or (ps-occurs-in type1 (bindings ex))
      (ps-occurs-in type1 (expression ex))))

(defmethod ps-occurs-in (type1 (ex update-expr))
  (or (ps-occurs-in type1 (expression ex))
      (ps-occurs-in type1 (assignments ex))))

(defmethod ps-occurs-in (type1 (ass assignment))
  (or (ps-occurs-in type1 (arguments ass))
      (ps-occurs-in type1 (expression ass))))

(defmethod ps-occurs-in (type1 (expr name-expr))
  (or (and (type-name? type1)
	   (eq (id type1) (id expr))
	   (ps-eq (actuals type1) (actuals expr))
	   (eq (mod-id type1) (mod-id expr)))
      (ps-occurs-in type1 (actuals expr))))


(defmethod id-occurs-in (x y)
  (eql x y))

(defmethod id-occurs-in (id (adt datatype))
  (or (id-occurs-in id (formals adt))
      (id-occurs-in id (assuming adt))
      (id-occurs-in id (constructors adt))))

(defmethod id-occurs-in (id (c simple-constructor))
  (or (eq id (id c))
      (some@ #'(lambda (a) (id-occurs-in id a))
	    (arguments c))))

(defmethod id-occurs-in (id (a typed-declaration))
  (or (eq id (id a))
      (id-occurs-in id (declared-type a))))


(defmethod id-occurs-in (id (l list))
  (unless (null l)
    (or (id-occurs-in id (car l))
	(id-occurs-in id (cdr l)))))

;(defmethod id-occurs-in (id (te type-name))
;  (or (tc-eq id te)
;      (call-next-method)))

(defmethod id-occurs-in (id (te type-application))
  (id-occurs-in id (parameters te)))

(defmethod id-occurs-in (id (te dep-binding))
  (id-occurs-in id (declared-type te)))

(defmethod id-occurs-in (id (te expr-as-type))
  (id-occurs-in id (expr te)))

(defmethod id-occurs-in (id (te subtype))
  (or (id-occurs-in id (supertype te))
      (id-occurs-in id (predicate te))
      (and (slot-exists-p te 'formula)
	   (id-occurs-in id (formula te)))))

(defmethod id-occurs-in (id (te funtype))
  (or (id-occurs-in id (domain te))
      (id-occurs-in id (range te))))

(defmethod id-occurs-in (id (te tupletype))
  (id-occurs-in id (types te)))

(defmethod id-occurs-in (id (te recordtype))
  (id-occurs-in id (fields te)))

(defmethod id-occurs-in (id (fd field-decl))
  (or (eq id (id fd))
      (id-occurs-in id (declared-type fd))))


;;; Expressions

;(defmethod id-occurs-in (id (ex name-expr))
;  (or (tc-eq id ex)
;      (call-next-method)))

(defmethod id-occurs-in (id (ex number-expr))
  (declare (ignore id))
  nil)

(defmethod id-occurs-in (id (ex record-expr))
  (id-occurs-in id (assignments ex)))

(defmethod id-occurs-in (id (ex tuple-expr))
  (id-occurs-in id (exprs ex)))

;(defmethod id-occurs-in (id (ex coercion))
;  (or (id-occurs-in id (expression ex))
;      (id-occurs-in id (type ex))))

;(defmethod id-occurs-in (id (ex intype))
;  (or (id-occurs-in id (expression ex))
;      (id-occurs-in id (type-value ex))))

(defmethod id-occurs-in (id (ex projection-application))
  (or (eq id (id ex))
      (id-occurs-in id (argument ex))))

(defmethod id-occurs-in (id (ex field-application))
  (or (eq id (id ex))
      (id-occurs-in id (argument ex))))

(defmethod id-occurs-in (id (ex application))
  (or (id-occurs-in id (operator ex))
      (id-occurs-in id (argument ex))))

(defmethod id-occurs-in (id (ex binding-expr))
  (or (id-occurs-in id (bindings ex))
      (id-occurs-in id (expression ex))))

(defmethod id-occurs-in (id (ex update-expr))
  (or (id-occurs-in id (expression ex))
      (id-occurs-in id (assignments ex))))

(defmethod id-occurs-in (id (ass assignment))
  (or (id-occurs-in id (arguments ass))
      (id-occurs-in id (expression ass))))

(defmethod id-occurs-in (id (nm name))
  (or (eq id (id nm))
      (id-occurs-in id (actuals nm))))

(defmethod id-occurs-in (id (act actual))
  (if (type-value act)
      (id-occurs-in id (type-value act))
      (id-occurs-in id (expr act))))

(defmethod id-occurs-in (id (bd bind-decl))
  (or (eq id (id bd))
      (id-occurs-in id (declared-type bd))))
