;;; Export to Dedukti.
;;; This module provides the function ‘to-dk3’ which exports a PVS theory to a
;;; Dedukti3 file.
;;; TODO non dependent product type with elements of type TYPE
;;; TODO module resolution and importing
;;; TODO recursive functions
;;; TODO assuming sections
;;; TODO dependent pairs
;;; TODO dependent products
;;; TODO records

(in-package :pvs)
(export '(to-dk3))

(deftype polylist (ty)
  `(or (cons ,ty list) null))

(defparameter *print-domains* t
  "Whether to systematically print domain of abstractions.")

(defparameter *print-implicits* t
  "Whether to systematically print implicit arguments.")

(declaim (type (cons (cons symbol string) list) *dk-sym-map*))
(defparameter *dk-sym-map*
  `((|boolean| . "prop") (|bool| . "prop") (true . "true") (false . "false")
    (|type| . "Set" ))
  "Maps PVS names to names of the encoding. It is also used to avoid prepending
the symbols with a module id.")

(defpackage dklog
  (:documentation "Some logging facilities.")
  (:use :cl)
  (:export :log-top :log-expr :log-type :log-decl :log-ctxts))

(in-package :dklog)

(defvar *log-file* "/tmp/pp-dk3.log" "File used for logging and debugging.")

(defun dk-log (tag format-str &rest args)
  "Like format *log-file* FORMAT-STR ARGS adding timestamp, informative tag TAG
at the beginning of line and terminating line."
  (with-open-file
      (out *log-file* :direction :output :if-exists :append
                      :if-does-not-exist :create)
    (multiple-value-bind (second minute hour date month year dow dst-p tz)
        (get-decoded-time)
      (format out "[~d:~d:~d] " hour minute second))
    (if tag (format out "[~a] " tag))
    (apply #'format out format-str args)
    (terpri out)))

(defun log-top (format-str &rest args)
  (apply #'dk-log nil format-str args))
(defun log-decl (format-str &rest args)
  (apply #'dk-log "decl" format-str args))
(defun log-expr (format-str &rest args)
  (apply #'dk-log "expr" format-str args))
(defun log-type (format-str &rest args)
  (apply #'dk-log "type" format-str args))

(in-package :pvs)

(declaim (ftype (function (syntax string) *) to-dk3))
(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (dklog:log-top "Translating ~s" file)
  (with-open-file (stream file :direction :output :if-exists :supersede)
    (let ((*print-pretty* nil)
          (*print-right-margin* 78))
      (write-string "require open personoj.encodings.lhol;
require personoj.encodings.tuple as T;
require personoj.encodings.sum as S;
require open personoj.encodings.logical;
require open personoj.encodings.pvs_cert;
require personoj.encodings.equality_tup as Eqtup;
require open personoj.encodings.builtins;" stream)
      (fresh-line stream)
      (pp-dk stream obj))))

(declaim (type type-name *type*))
(defparameter *type* (mk-type-name '|type|)
  "Symbol that represents TYPE in PVS which is translated as Set.")

(declaim (ftype (function (type-expr) boolean) is-*type*-p))
(defun is-*type*-p (tex)
  "Return true if TEX is the constant TYPE"
  (equal tex *type*))

(declaim (type (polylist symbol) *signature*))
(defparameter *signature* nil
  "Symbols defined in the theory.")

(declaim (ftype (function (list list) list) pairlis*))
(defun pairlis* (l1 l2)
  "Like `pairlis' but accepts L1 and L2 with different lengths, and stop as soon
as a list is exhausted."
  (loop for e1 in l1
        for e2 in l2
        collect (cons e1 e2)))

;;; Contexts
;;;
;;; Contexts are  global variables that are  filled during the export.  They are
;;; filled  using  dynamic  scoping  (that  is  with  (let  ((*ctx*  ...))  ...)
;;; constructs) so that the variables  introduced are automatically removed when
;;; we  escape   their  lexical  scope   in  the  PVS  specification   (and  the
;;; translation). Contexts are always reversed  wrt their definition, that is, a
;;; PVS context [x: nat, y: reals, z: nznat] is represented as ((z . nznat) (y .
;;; reals) (x . nat)), the most recent binding is on top (stack structure).

(deftype context ()
  "A context is an association list mapping symbols to types."
  '(polylist (cons symbol type-expr)))

(declaim (type context *ctx*))
(defparameter *ctx* nil
  "Context enriched by bound arguments, theory formals and `var-decl'. Variable
declarations `var-decl' are never removed from the context.")

(declaim (type context *ctx-var*))
(defparameter *ctx-var* nil
  "Context enriched by `var-decl' only. Not typed bound variables of LAMBDAs
seek their type into this context only (and not previous LAMBDA bindings).")

(defpackage theory
  (:use :cl :pvs)
  (:documentation "This package provide functions to manipulate formals of
theories. The list of formals is not updated with dynamic scoping because we
never need to remove elements from this list. Formals are translated as implicit
arguments.")
  (:nicknames :thy)
  (:export
   :add-type
   :add-val
   :bind-decl-of-thy
   :as-ctx))

(in-package :theory)

(declaim (type context *ctx-thy*))
(defparameter *ctx-thy* nil
  "Contain theory formals. Formals may be either types of type `TYPE' or values
of some type of type `TYPE'.")

(declaim (ftype (function (symbol) *) add-type))
(defun add-type (ty)
  "Add a type variable to the theory."
  (setf *ctx-thy* (acons ty pvs::*type* *ctx-thy*)))

(declaim (ftype (function (symbol type-expr) *) add-val))
(defun add-val (va ty)
  "Add a value variable VA of type TY to the theory."
  (setf *ctx-thy* (acons va ty *ctx-thy*)))

(declaim (ftype (function () list) bind-decl-of-thy))
(defun bind-decl-of-thy ()
  "Returns a list of binding declaration from `*ctx-thy*'. It returns binding
declarations for types concatenated with binding declarations for values."
  (mapcar #'pvs::ctxe->bind-decl (reverse *ctx-thy*)))

(defun as-ctx () (reverse *ctx-thy*))

(in-package :pvs)

(declaim (type (polylist (cons symbol symbol)) *ctx-thy-subtypes*))
(defparameter *ctx-thy-subtypes* nil
  "For each u TYPE FROM t present in the theory formals, a cons cell
(u . u_pred) is added to this context. When u is required, it will be printed as
psub u_pred.")

(declaim (ftype (function ((polylist bind-decl)) context) ctx-of-bindings))
(defun ctx-of-bindings (bindings)
  "Transforms bindings BINDINGS into a context."
  (flet ((f (bd)
           (cons (id bd) (if (declared-type bd)
                             (declared-type bd)
                             (type bd)))))
    (mapcar #'f bindings)))

(declaim (ftype (function (cons symbol type-expr) bind-decl) ctxe->bind-decl))
(defun ctxe->bind-decl (e)
  "Convert element E of a context to a `bind-decl'."
  (make!-bind-decl (car e) (cdr e)))

;;; A bit like a context but not truly a context
(declaim (type (polylist (cons symbol (cons integer (cons integer symbol))))
               *packed-tuples*))
(defparameter *packed-tuples* nil
  "A mapping (v . (n . (m . s))) of this list means that variable ``v'' is the
``n''th element of tuple ``s'' of length ``m''. It is filled by `pack-arg-tuple'
(using lexical scoping).")

;;; Misc functions

(declaim (ftype (function (expr) type-expr) type-of-expr))
(defgeneric type-of-expr (ex)
  (:documentation "Get the type attributed to expression EX by PVS.")
  (:method ((ex name-expr)) (type (car (resolutions ex))))
  (:method ((ex bind-decl)) (type ex))
  (:method ((ex expr-as-type)) (expr ex))
  (:method (ex) (error "Unknown expression" (describe ex))))

(declaim (type (integer) *var-count*))
(defparameter *var-count* 0
  "Number of generated variables. Used to create fresh variable names.")

(declaim (ftype (function (string) string) fresh-var))
(defun fresh-var (&key (prefix ""))
  "Provide a fresh variable name."
  (let ((var-name (format nil "~apvs~d" prefix *var-count*)))
    (incf *var-count*)
    var-name))

(defmacro with-parens ((stream wrap) &body body)
  "Wraps body BODY into parentheses (printed on stream STREAM) if WRAP is true."
  `(progn
     (when ,wrap (format ,stream "("))
     ,@body
     (when ,wrap (format ,stream ")"))))

(defmacro with-binapp-args ((larg rarg binapp) &body body)
  "Binds the left (resp. right) argument of binary application BINAPP to LARG
(resp. RARG) in body BODY."
  `(destructuring-bind (,larg ,rarg &rest _) (exprs (argument ,binapp))
     ,@body))

(in-package :dklog)

(defun log-ctxts (ind &optional obj)
  "Prints debug information on standard output with IND an indication (typically
a function name from where the debug is called)."
  (dk-log nil "~a:" ind)
  (dk-log nil "~a:" obj)
  (dk-log nil "  thf:~i~<~a~:>" (list (thy:as-ctx)))
  (dk-log nil "  tst:~i~<~a~:>" (list pvs::*ctx-thy-subtypes*))
  (dk-log nil "  ctx:~i~<~a~:>" (list pvs::*ctx*))
  (dk-log nil "  tup:~i~<~a~:>" (list pvs::*packed-tuples*)))

(in-package :pvs)

(declaim (ftype
          (function (list
                     (polylist bind-decl)
                     (polylist (cons symbol
                                     (cons integer
                                           (cons integer symbol)))))
                    (cons (polylist bind-decl)
                          (polylist (cons symbol
                                          (cons integer
                                                (cons integer symbol))))))
          pack-arg-tuple))
(defun pack-arg-tuple (args &key vars projspec)
  "Transform the list of list of formals in ARGS into a pair (vs . ps)
where VS is a list of binding declarations, and PS is a list of projection
specifications. For each element E of ARGS, if its length is one, then it is a
variable and a bind decl is made out of it and added to VS. Otherwise, if its
length is more than one, it represents a tuple of argument. In that case, a
fresh variable is created for the binding declaration, and its type is the list
of types of the elements of E. The second element is a list of projection
specifications. For each element E of ARGS, if its length is one, its projection
specification is `nil'. Otherwise, it is a list (x . (n . (m . v))) where X
is the identifier of the formal (that is an element of a tuple), N is its
position in the tuple, M is the length of the tuple and V is the name of the
fresh variable created for this tuple.
We have ARGS of same length as VS and PS."
  (labels
      ((type-with-ctx (elt)
         "Type formal ELT with its `declared-type' if it exists, or from
`*ctx*'."
         (declare (type expr elt))
         (with-slots (id declared-type) elt
           (if (null declared-type)
               (let ((v-ty (assoc id *ctx*)))
                 (assert (not (null v-ty))
                         (id *ctx*)
                         "Could not find variable ~S in context ~S."
                         id *ctx*)
                 (cdr v-ty))
               declared-type)))
       (pack-type (l)
         "Make a `bind-decl' out of L, either by taking the `car' or
creating a fresh variable that stand for a tuple."
         (declare (type list l))
         (if (= 1 (length l))
             (let ((elt (car l)))
               (make-bind-decl (id elt) (type-with-ctx elt)))
             (let ((var (intern (fresh-var :prefix "tup")))
                   (typ (make-tupletype (mapcar #'type-with-ctx l))))
               (make-bind-decl var typ))))
       (get-pspec (l var)
         "Make the projection specification of list of bindings L"
         (declare (type list l))
         (declare (type symbol var))
         (let ((len (length l)))
           (unless (= 1 len)
             (loop for e in l
                   for i upto (- len 1)
                   collect (cons (id e) (cons i (cons len var))))))))
    (if (null args) (cons (reverse vars) (reverse projspec))
        (destructuring-bind (hd &rest tl) args
          (declare (type list hd))
          (let* ((bd (pack-type hd))
                 (spec (get-pspec hd (id bd))))
            (pack-arg-tuple
             tl :vars (cons bd vars)
             :projspec (concatenate 'list spec projspec)))))))

;;; Specialised printing functions

(declaim (ftype (function (stream symbol * *) null) pp-sym))
(defun pp-sym (stream sym &optional colon-p at-sign-p)
  "Prints symbol SYM to stream STREAM, enclosing it in braces {||} if
necessary."
  (flet ((sane-charp (c)
           (or (alphanumericp c) (char= #\_ c))))
    (let ((dk-sym (assoc sym *dk-sym-map*)))
      (cond (dk-sym (format stream "~a" (cdr dk-sym)))
            ((every #'sane-charp (string sym)) (format stream "~a" sym))
            (t (format stream "{|~a|}" sym))))))

(defun pp-type (stream tex &optional wrap at-sign-p)
  "Print `Set' if TEX is `*type*', or prefix TEX by `El'."
  (if (is-*type*-p tex) (write-string "Set" stream)
      (with-parens (stream wrap)
        (format stream "El ~:/pvs:pp-dk/" tex))))

(declaim (ftype (function
                 ((or expr type-expr) (polylist bind-decl) stream * *) null)
                pprint-abstraction))
(defun pprint-abstraction (ex bindings stream &key wrap (impl 0))
  "Print expression EX on stream STREAM abstracting arguments in BINDINGS (with
λs). Note that the context `*ctx*' is enriched on each printed binding. The
binding is automatically removed from the context thanks to dynamic scoping.  If
IMPL is provided, then the first IMPL bindings are made implicit."
  (if (null bindings)
      (pp-dk stream ex wrap)
      (with-parens (stream wrap)
        (destructuring-bind (hd &rest tl) bindings
          (write-string "λ " stream)
          (with-slots (id declared-type) hd
            (if (> impl 0) (write-string "{" stream))
            (format stream "~/pvs:pp-sym/: " id)
            (if declared-type
                (let ((*ctx* (acons id declared-type *ctx*)))
                  ;; Print the body with the variable in context
                  (pp-type stream declared-type)
                  (if (> impl 0) (write-string "}" stream))
                  (write-string ", " stream)
                  ;; Recursive call in `if’ branches for dynamic scoping
                  (pprint-abstraction ex tl stream :impl (- impl 1)))
                (let ((typ (cdr (assoc id *ctx-var*))))
                  ;; If the type of the binding is not specified, then the
                  ;; variable must be typed by a x: VAR t declaration, and
                  ;; hence end up in `*ctx-var*'. We do not need to complete
                  ;; `*ctx*'.
                  (format stream "El ~:/pvs:pp-dk/" typ)
                  (if (> impl 0) (write-string "}" stream))
                  (write-string ", " stream)
                  (pprint-abstraction ex tl stream :impl (- impl 1)))))))))

(declaim (ftype (function (stream (or forall-expr exists-expr) * * string) null)
                pp-quantifier))
(defun pp-quantifier (stream expr &optional colon-p at-sign-p quant)
  (with-slots (bindings expression) expr
    (if (null bindings)
        (pp-dk stream expression colon-p at-sign-p)
        (let ((newex (copy expr))
              (bd (car bindings)))
          (setf (slot-value newex 'bindings) (cdr bindings))
          (with-parens (stream colon-p)
            (write-string quant stream)
            ;; Print domain
            (format stream " {~:/pvs:pp-dk/} " (type-of-expr bd))
            (with-parens (stream t)
              (pprint-abstraction newex (list bd) stream)))))))

(declaim (ftype (function (type-expr symbol list stream *) null)
                pprint-product))
(defun pprint-product (tex kind ctx stream &key wrap (impl 0))
  "Print `Π x1: t1, Π x2: t2, ..., Π xn: tn, ξ (TEX)' where `(xi, ti)' are the
components of CTX, and ξ is determined by KIND which may be 'set, 'prop or
'kind. The first IMPL arguments are made implicit (wrapped into curly
brackets)."
  (if (null ctx)
      (case kind
        ('kind (pp-dk stream tex))
        ('set (format stream "El ~:/pvs:pp-dk/" tex))
        ('prop (format stream "Prf ~:/pvs:pp-dk/" tex)))
      (destructuring-bind ((id . typ) &rest tl) ctx
        (write-string "Π " stream)
        (let ((*ctx* (acons id typ *ctx*)))
          (if (> impl 0) (write-string "{" stream))
          (format stream "~/pvs:pp-sym/: ~/pvs:pp-type/" id typ)
          (if (> impl 0) (write-string "}" stream))
          (write-string ", " stream)
          (pprint-product tex kind tl stream :impl (- impl 1))))))

(declaim (ftype (function (type-expr symbol stream *) null) pprint-thy-formals))
(defun pprint-thy-formals (tex kind stream &optional wrap)
  "Print type expression TEX prefixed by as many products as there are formals
in the theory. Formals are implicit. Parameter KIND behaves as in
`pprint-product'."
  (let* ((thy-ctx (thy:as-ctx))
         (len (length thy-ctx)))
    (pprint-product tex kind thy-ctx stream :wrap wrap :impl len)))

(declaim (ftype (function (symbol stream string) *) pprint-reqopen))
(defun pprint-reqopen (mod stream &optional root)
  "Prints a ``require open'' directive opening module MOD with root path ROOT on
stream STREAM."
  (write-string "require open" stream)
  (unless (null root)
    (write-char #\space stream)
    (write-string root stream)
    (write-char #\. stream))
  (princ mod stream))

(declaim (ftype (function (symbol integer integer stream) null)
                pprint-proj-spec))
(defun pprint-proj-spec (var index len stream)
  "Print the INDEXth projection of VAR being a tuple of length LEN on stream
STREAM. `pprint-proj-spec v 3' prints ``σsnd (σsnd (σsnd (σfst v)))''."
  (labels ((projs-of-ind (ind len)
             "Transform a projection in a list into a succession of `fst' and
`snd' projections."
             (declare (type integer ind))
             (declare (type integer len))
             (let ((snd-projs (make-list ind :initial-element "T.cdr")))
               (if (= ind (- len 1)) snd-projs (cons "T.car" snd-projs))))
           (pprint-projs (ps)
             (declare (type (polylist string) ps))
             (if (null ps)
                 (pp-sym stream var)
                 (with-parens (stream t)
                   (write-string (car ps) stream)
                   (write-char #\space stream)
                   (pprint-projs (cdr ps))))))
    (pprint-projs (projs-of-ind index len))))

;;; Main printing

(declaim (ftype (function (stream syntax * *) null)))
(defgeneric pp-dk (stream obj &optional colon-p at-sign-p)
  (:documentation "Prints object OBJ to stream STREAM. This function can be used
in `format' funcall `~/pvs:pp-dk3/'. The colon modifier specifies whether
arguments should be wrapped into parentheses.")
  (:method (stream obj &optional c a)
    (describe obj)
    (error "Unexpected element: ~w." obj)))

(defmethod pp-dk (stream (mod module) &optional colon-p at-sign-p)
  "Print the declarations of module MOD."
  (labels
      ((handle-var-decl (stream vd rest)
         "Add dynamically variable declaration VD to `*ctx*' and print the rest
of the theory REST with the new context in (dynamic) scope."
         (declare (type var-decl vd))
         (declare (type list rest))
         (with-slots (id declared-type) vd
           (let ((*ctx* (acons id declared-type *ctx*))
                 ;; REVIEW: setting `*ctx*' may be useless. At least the
                 ;; distinction between `*ctx*' and `*ctx-var*' is required,
                 ;; see the documentation of `*ctx-var*'.
                 (*ctx-var* (acons id declared-type *ctx-var*)))
             (pprint-decls rest))))
       (pprint-decls (decls)
         "Print declarations DECLS to stream STREAM. We use a special function
(rather than a `map') because PVS places the declaration of predicates *after*
the declaration of TYPE FROM."
         (declaim (type (polylist (or importing declaration)) decls))
         (when (not (null decls))
           (cond
             ((var-decl? (car decls))
              (handle-var-decl stream (car decls) (cdr decls)))
             ((type-from-decl? (first decls))
              ;; In this case (TYPE FROM declaration), the predicate appears
              ;; after the type declaration
              (assert (>= (length decls) 2))
              (pp-dk stream (second decls))
              (fresh-line stream)
              (pp-dk stream (first decls))
              (fresh-line stream)
              (terpri stream)
              (pprint-decls (cddr decls)))
             (t (pp-dk stream (car decls))
                (fresh-line stream)
                (terpri stream)
                (pprint-decls (cdr decls))))))
       (process-formals (formals theory)
         "Handle formal parameters FORMALS of theory THEORY."
         (declare (type (polylist formal-decl) formals))
         (declare (type list theory))
         ;; FIXME importing must be processed too
         (if
          (null formals)
          (pprint-decls theory)
          (destructuring-bind (hd &rest tl) formals
            (cond
              ((formal-subtype-decl? hd)
               ;; Retrieve the name of the subtype
               (let* ((pred (predicate (type-value hd))))
                 ;; No dynamic scoping because `*ctx-thy-subtypes*' is never
                 ;; depleted
                 (setf *ctx-thy-subtypes*
                       (acons (id hd) (id pred) *ctx-thy-subtypes*))
                 (thy:add-val (id pred) (type pred))
                 (process-formals tl theory)))
              ((formal-type-decl? hd)
               (progn
                 (thy:add-type (id hd))
                 (process-formals tl theory)))
              ((formal-const-decl? hd)
               (let* (;; REVIEW adding to *ctx* might be superfluous
                      (*ctx* (acons (id hd) (declared-type hd) *ctx*)))
                 (thy:add-val (id hd) (declared-type hd))
                 (process-formals tl theory)))))))
       (up-to (e l &optional acc)
         "Return all symbols of list L up to symbol E. If E is not in L, all L
is returned. ACC contains all symbols before E (in reverse order)."
         (declare (type symbol e))
         (declare (type (polylist symbol) l))
         (declare (type (polylist symbol) acc))
         (if (null l)
             (reverse acc)
             (destructuring-bind (hd &rest tl) l
               (if (equal e hd) (reverse acc) (up-to e tl (cons hd acc)))))))
    (with-slots (id theory formals-sans-usings) mod
      (format stream "// Theory ~a~%" id)
      (let ((prelude (mapcar #'id *prelude-theories*)))
        (loop for m in (up-to id prelude)
              do (pprint-reqopen m stream "pvs.prelude")
              do (write-char #\; stream)
              do (fresh-line stream)))
      (process-formals formals-sans-usings theory))))

(defmethod pp-dk (stream (imp importing) &optional colon-p at-sign-p)
  "Prints importing declaration IMP."
  (with-slots (theory-name) imp
    (format stream "require ~a;" theory-name)))

;;; Declarations

(defmethod pp-dk (stream (decl type-decl) &optional colon-p at-sign-p)
  "t: TYPE."
  (dklog:log-decl "type decl")
  (with-slots (id) decl
    (format stream "constant symbol ~/pvs:pp-sym/: " id)
    (pprint-thy-formals *type* 'kind stream t)
    (write-char #\; stream)
    ;; No dynamic scoping because we never remove elements from the signature
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "t: TYPE = x, but also domain(f): TYPE = D"
  (dklog:log-decl "type-eq-decl")
  (with-slots (id type-expr formals) decl
    (format stream "symbol ~/pvs:pp-sym/: " id)
    (let* ((args (car (pack-arg-tuple formals)))
           (ctx (mapcar #'(lambda (a) (cons (id a) (type-of-expr a))) args))
           (ctx (append (thy:as-ctx) ctx)))
      ;; In the case of type definitions with arguments, the type-expr is
      ;; simply `TYPE', even though it ought to be d *> TYPE with *> the arrow
      ;; of type (TYPE, KIND, KIND). So we rebuild back this type.
      (pprint-product
       *type* 'kind ctx stream :wrap t :impl (length (thy:as-ctx))))
    (write-string " ≔ " stream)
    (let* ((form-spec (pack-arg-tuple formals))
           (*packed-tuples* (cdr form-spec))
           (ctx (thy:bind-decl-of-thy))
           (bindings (concatenate 'list ctx (car form-spec))))
      (pprint-abstraction type-expr bindings stream :impl (length (thy:as-ctx))))
    (write-char #\; stream)
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s"
  (dklog:log-ctxts "type from" decl)
  (dklog:log-decl "type-from-decl")
  (with-slots (id predicate supertype) decl
    ;; PREDICATE is a type declaration
    (format stream "symbol ~/pvs:pp-sym/: " id)
    (pprint-thy-formals *type* 'kind stream t)
    (write-string " ≔ " stream)
    (pprint-abstraction
     ;; Build properly the subtype expression for printing
     (mk-subtype supertype (mk-name-expr (id predicate)))
     (thy:bind-decl-of-thy)
     stream
     :impl (length (thy:as-ctx)))
    (write-char #\; stream)
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl formula-decl) &optional colon-p at-sign-p)
  (dklog:log-decl "formula")
  (with-slots (spelling id definition) decl
    (format stream "// Formula declaration: ~a~&" spelling)
    (flet ((univ-closure (ex)
             (let* ((free-ids (mapcar #'id (freevars ex)))
                    (bindings (mapcar
                               #'(lambda (id)
                                   (ctxe->bind-decl (assoc id *ctx*)))
                               free-ids)))
               (make!-forall-expr bindings ex))))
      (declaim (ftype (function (expr) forall-expr) univ-closure))
      (let ((defn (univ-closure definition))
            (axiomp (member spelling '(AXIOM POSTULATE))))
        (unless axiomp (write-string "opaque " stream))
        (write-string "symbol" stream)
        (format stream " ~/pvs:pp-sym/ : " id)
        (pprint-thy-formals defn 'prop stream t)
        (unless axiomp
          ;; TODO: export proof
          (format stream " ≔ begin admitted"))
        (write-char #\; stream)
        (setf *signature* (cons id *signature*))))))

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (dklog:log-decl "const")
  (dklog:log-ctxts "const-decl")
  (with-slots (id type definition formals) decl
    (format stream "// Constant declaration ~a~%" id)
    (if definition
        (let* ((form-proj (pack-arg-tuple formals))
               (*packed-tuples* (cdr form-proj))
               (ctx-thy (thy:bind-decl-of-thy))
               (form-bds (car form-proj))
               (bindings (concatenate 'list ctx-thy form-bds)))
          (format stream "symbol ~/pvs:pp-sym/: " id)
          (pprint-thy-formals type 'set stream t)
          (write-string " ≔ " stream)
          (pprint-abstraction definition bindings stream
                              :impl (length (thy:as-ctx))))
        (progn
          (format stream "symbol ~/pvs:pp-sym/: " id)
          (pprint-thy-formals type 'set stream t)))
    (write-string " begin admitted;" stream)
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl def-decl) &optional colon-p at-sign-p)
  (error "Recursive function definitions are not handled yet."))

(defmethod pp-dk (stream (decl conversion-decl) &optional colon-p at-sign-p)
  "CONVERSION elt, there are conversion(plus|minus)-decl as well."
  (dklog:log-decl "conversion")
  (dklog:log-ctxts "conversion-decl")
  (with-slots (id) decl
    (format stream "// Conversion: ~/pvs:pp-sym/" id)))

(defmethod pp-dk (stream (decl auto-rewrite-decl) &optional colon-p at-sign-p)
  "AUTO_REWRITE, there are auto-rewrite-(plus|minus)-decl as well."
  (format stream "// Auto rewrite ~/pvs:pp-sym/" (id decl)))

;;; Judgements
;; TODO: they are only comments for now

(defmethod pp-dk (stream (decl name-judgement) &optional colon-p at-sign-p)
  (with-slots (name) decl
    (format stream "// Name judgement \"~a\"." name)))

(defmethod pp-dk (stream (decl application-judgement)
                  &optional colon-p at-sign-p)
  "Print the judgement. A TCC is generated with the same `id'.
See parse.lisp:826"
  (dklog:log-decl "application judgement")
  (dklog:log-ctxts "application-judgement" decl)
  (with-slots (id formals declared-type judgement-type name) decl
    (format stream "// Application judgement \"~a\"~%" id)))


(defmethod pp-dk (stream (decl expr-judgement) &optional colon-p _at-sign-p)
  (dklog:log-ctxts "expr-judgement")
  (with-slots (id) decl
    ;; See classes-decl.lisp:656
    (format stream "// expr-judgement: ~/pvs:pp-sym/" id)))

(defmethod pp-dk (stream (decl subtype-judgement) &optional colon-p _at-sign-p)
  (with-slots (id declared-subtype subtype) decl
    (format stream "// Subtype judgment,~%")
    (format stream "// ~/pvs:pp-sym/: ~/pvs:pp-dk/ has type ~/pvs:pp-dk/"
            id subtype declared-subtype)))

(defmethod pp-dk :after
    (stream (decl existence-tcc) &optional colon-p at-sign-p)
  ;; Only add a comment after the formula
  (format stream "// ^^ Existence TCC~&"))

(defmethod pp-dk :after
    (stream (decl subtype-tcc) &optional colon-p at-sign-p)
  (format stream "// ^^ Subtype TCC~&"))

;;; Type expressions

(defmethod pp-dk :around (stream (te type-expr) &optional colon-p at-sign-p)
  "Prints the printable type of type expr TE if it exists, or hand over to next
method. If we do not use the PRINT-TYPE field, all predicate subtypes
definitions are expanded, and the translation becomes too large."
  (if (print-type te)
      (pp-dk stream (print-type te) colon-p at-sign-p)
      (call-next-method)))

(defmethod pp-dk (stream (te tupletype) &optional colon-p at-sign-p)
  "[bool, bool] but also [bool, bool -> bool]"
  (dklog:log-type "tuple")
  (with-slots (types) te
    (with-parens (stream colon-p)
      (write-string "T.t " stream)
      ;; Any tuple type has at least two elements
      (if (= 2 (length types))
          (destructuring-bind (s u) types
            (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/" s u))
          (destructuring-bind (hd &rest tl) types
            (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/"
                    hd (make-tupletype tl)))))))

(defmethod pp-dk (stream (te subtype) &optional colon-p at-sign-p)
  "{n: nat | n /= zero} or (x | p(x)), see classes-decl.lisp:824"
  (dklog:log-type "subtype")
  (with-slots (supertype predicate) te
    (with-parens (stream colon-p)
      (write-string "@psub " stream)
      ;; REVIEW: can the supertype be `nil'?
      (format stream "~:/pvs:pp-dk/ " supertype)
      (pp-dk stream predicate t at-sign-p))))

(defmethod pp-dk (stream (te expr-as-type) &optional colon-p at-sign-p)
  "Used in e.g. (equivalence?), that is, a parenthesised expression used as a
type."
  (dklog:log-type "expr-as-type")
  (with-slots (expr) te
    (with-parens (stream colon-p)
      ;; REVIEW: should get the domain of expression E and pass it as first
      ;; argument of psub
      (write-string "@psub _ " stream)
      (pp-dk stream expr t at-sign-p))))

(defmethod pp-dk (stream (te simple-expr-as-type) &optional colon-p at-sign-p)
  "Used in e.g. (equivalence?) without inheriting subtypes. I don't know when it
can be used."
  (dklog:log-type "simpl-expr-as-type")
  (with-slots (expr) te
    (pp-dk stream expr colon-p at-sign-p)))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM. Used for instance with dependent
(sub)types `subt(i)` where `subt(i) = {x: ... | f(i)}`."
  (dklog:log-type "type-application")
  (with-slots (type parameters) te
    (with-parens (stream colon-p)
      (pp-dk stream type t)
      (write-char #\space stream)
      (pprint-logical-block (stream parameters)
        (pprint-indent :block 2 stream)
        (pprint-newline :fill stream)
        (pp-dk stream (pprint-pop) t)
        (pprint-exit-if-list-exhausted)
        (write-char #\space stream)))))

(defmethod pp-dk (stream (te funtype) &optional colon-p at-sign-p)
  "Prints function type TE to stream STREAM."
  (dklog:log-type "funtype")
  (with-slots (domain range) te
    (with-parens (stream colon-p)
     (format stream "~:/pvs:pp-dk/ ~~> ~:_~/pvs:pp-dk/" domain range))))

;;; Expressions

(defmethod pp-dk (stream (ex name) &optional colon-p at-sign-p)
  "Print name NAME applying theory formal parameters if needed. Takes care of
name resolution"
  (dklog:log-expr "name")
  (with-slots (id mod-id actuals) ex
    (cond
      ;; Member of an unpacked tuple: as it has been repacked, we transform this
      ;; to successsion of projections
      ((assoc id *packed-tuples*)
       (destructuring-bind (v n m . w) (assoc id *packed-tuples*)
         (pprint-proj-spec w n m stream)))
      ((assoc id *ctx*) (pp-sym stream id))
      ((member id *signature*)
       (with-parens (stream (consp (thy:bind-decl-of-thy)))
         (pp-sym stream id)
         (unless (null (thy:bind-decl-of-thy))
           ;; Apply theory arguments (as implicit args) to symbols of signature
           (format stream "~{ {~/pvs:pp-dk/}~}"
                   ;; Print arguments through ‘pp-dk’ because they might be in
                   ;; ‘ctx-local’
                   (flet ((cdr-*type*-p (id-ty) (is-*type*-p (cdr id-ty))))
                     (mapcar #'(lambda (st) (mk-name-expr (car st)))
                             (thy:as-ctx)))))))
      ;; The symbol is a type declared as TYPE FROM in theory parameters,
      ;; we print the predicate associated
      ((assoc id *ctx-thy-subtypes*)
       (format stream "~:/pvs:pp-sym/"
               (cdr (assoc id *ctx-thy-subtypes*))))
      ;; Symbol of the encoding
      ((assoc id *dk-sym-map*) (pp-sym stream id))
      ;; Otherwise, it’s a symbol from an imported theory
      (t (with-parens (stream (consp actuals))
           (unless (null mod-id)
             ;; If `mod-id’ is `nil’, then symbol comes from prelude, which is
             ;; require-open’d
             (pp-sym stream mod-id)
             (write-char #\. stream))
           (format stream "~/pvs:pp-sym/~{ {~/pvs:pp-dk/}~}" id actuals))))))

(defmethod pp-dk (stream (ex lambda-expr) &optional colon-p _at-sign-p)
  "LAMBDA (x: T): t"
  (dklog:log-expr "lambda-expr")
  (with-slots (bindings expression) ex
    (pprint-abstraction expression bindings stream :wrap t)))

(defmethod pp-dk (stream (ex exists-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∃"))

(defmethod pp-dk (stream (ex forall-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∀"))

(defmethod pp-dk (stream (ex application) &optional colon-p _at-sign-p)
  "Print application EX. The expression EX ``f(e1,e2)(g1,g2)'' will be printed
as ``f (σcons e1 e2) (σcons g1 g2)''."
  (dklog:log-expr "application")
  (if (null (type ex))
      ;; For some reason, application-judgements end up as application
      ;; expressions. We don’t handle them here.
      (format stream "// Application judgement")
      (let* ((op (operator* ex))
             (args (arguments* ex)))
        (with-parens (stream colon-p)
          (pp-dk stream op)
          (write-char #\space stream)
          (flet ((tup-if-needed (a)
                   "Transform A into a tuple if its longer than one element."
                   (if (<= 2 (length a))
                       ;; There shouldn't be any additional TCC generated
                       ;; by `make!-tuple-expr', but who knows.
                       ;; REVIEW: use mk-tuple-expr, which doesn't
                       ;; typecheck?
                       (make!-tuple-expr a)
                       (car a))))
            (format stream "~{~:/pvs:pp-dk/~^ ~}"
                    (mapcar #'tup-if-needed args)))))))

(defmethod pp-dk (stream (ex projection-application)
                  &optional _colon-p _at-sign-p)
  "For projections of the form t`2."
  (dklog:log-ctxts "projection-application" ex)
  (with-slots (id index argument) ex
    (let ((len (length (types (type argument))))
          (ident (id argument)))
      (pprint-proj-spec ident index len stream))))

(defmethod pp-dk (stream (ex tuple-expr) &optional colon-p at-sign-p)
  "Prints tuples ``(e1, e2, e3)'' as ``(σcons e1 (σcons e2 e3))''. Note that we
use implicit arguments for σcons. Making arguments explicit prevents the
translation to scale up, because expressions become too verbose."
  (dklog:log-expr "tuple-expr")
  (with-slots (exprs) ex
    ;; Tuple types have at least 2 elements (PVS invariant)
    (with-parens (stream colon-p)
      (cond
        ((= 2 (length exprs))
         (destructuring-bind (x y) exprs
           (format stream "T.cons ~:/pvs:pp-dk/ ~:/pvs:pp-dk/" x y)))
        ((< 2 (length exprs))
         (destructuring-bind (hd &rest tl) exprs
           (let ((argr (make!-tuple-expr tl)))
             (format stream "T.cons ~:/pvs:pp-dk/ ~:/pvs:pp-dk/" hd argr))))
        (t (error "Tuple ~a have too few elements." ex))))))

;; REVIEW in all logical connectors, the generated variables should be added to
;; a context to be available to type expressions.

(defmethod pp-dk (stream (ex branch) &optional colon-p at-sign-p)
  "IF(a,b,c)"
  (dklog:log-expr "branch")
  (destructuring-bind (prop then else) (exprs (argument ex))
    (with-parens (stream colon-p)
      (format stream "if ~:/pvs:pp-dk/ " prop)
      (format stream "(λ ~a~:[~*~;: Prf ~:/pvs:pp-dk/~], ~/pvs:pp-dk/)"
              (fresh-var) *print-domains* prop then)
      (write-char #\Space stream)
      (format stream "(λ ~a~:[~*~;: Prf (not ~:/pvs:pp-dk/)~], ~/pvs:pp-dk/)"
              (fresh-var) *print-domains* prop else))))

;;; REVIEW: factorise disequation and equation

(defmethod pp-dk (stream (ex disequation) &optional colon-p at-sign-p)
  "/=(A, B)"
  (dklog:log-expr "disequation")
  (with-parens (stream colon-p)
    (let* ((eq-ty (type (operator ex)))
           (dom (types (domain eq-ty)))
           (tyl (car dom))
           (tyr (cadr dom)))
      (assert (equal tyl tyr) (tyl tyr)
              "Equality types ~S and ~S are not equal." tyl tyr)
      (with-binapp-args (argl argr ex)
        (format stream
                "@Eqtup.neq ~:/pvs:pp-dk/ (T.cons ~:/pvs:pp-dk/ ~:/pvs:pp-dk/)"
                tyl argl argr)))))

(defmethod pp-dk (stream (ex equation) &optional colon-p at-sign-p)
  "=(A, B)"
  (dklog:log-expr "equation")
  (with-parens (stream colon-p)
    (let* ((eq-ty (type (operator ex)))
           (dom (types (domain eq-ty)))
           (tyl (car dom))
           (tyr (cadr dom)))
      (assert (equal tyl tyr) (tyl tyr)
              "Equality types ~S and ~S are not equal." tyl tyr)
      (with-binapp-args (argl argr ex)
        (format
         stream
         "@Eqtup.eq ~:/pvs:pp-dk/ (T.cons ~:/pvs:pp-dk/ ~:/pvs:pp-dk/)"
         tyl argl argr)))))

(defmethod pp-dk (stream (ex conjunction) &optional colon-p at-sign-p)
  "AND(A, B)"
  (dklog:log-expr "conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format
       stream
       "and ~:/pvs:pp-dk/ (λ ~a~:[~*~;: Prf ~:/pvs:pp-dk/~], ~/pvs:pp-dk/)"
       argl (fresh-var) *print-domains* argl argr))))

(defmethod pp-dk (stream (ex disjunction) &optional colon-p at-sign-p)
  "OR(A, B)"
  (dklog:log-expr "disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format
       stream
       "or ~:/pvs:pp-dk/ (λ ~a~:[~*~;: Prf (not ~:/pvs:pp-dk/)~],~/pvs:pp-dk/)"
       argl (fresh-var) *print-domains* argl argr))))

(defmethod pp-dk (stream (ex implication) &optional colon-p at-sign-p)
  "IMPLIES(A, B)"
  (dklog:log-expr "implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format
       stream
       "imp ~:/pvs:pp-dk/ (λ ~a~:[~*~;: Prf ~:/pvs:pp-dk/~],~/pvs:pp-dk/)"
       argl (fresh-var) *print-domains* argl argr))))

(defmethod pp-dk (stream (ex iff) &optional colon-p at-sign-p)
  "IFF(A, B)"
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "iff ~:/pvs:pp-dk/ ~:/pvs:pp-dk/" argl argr))))

(defmethod pp-dk (stream (ex negation) &optional colon-p _at-sign-p)
  "NOT(A), there is also a `unary-negation' that represents NOT A."
  (dklog:log-expr "negation")
  (with-parens (stream colon-p)
    ;; NOTE we might be able to remove parens (see with LP precedence)
    (format stream "¬ ~:/pvs:pp-dk/" (argument ex))))

(defmethod pp-dk (stream (ex number-expr) &optional colon-p at-sign-p)
  (dklog:log-expr "number")
  ;; PVS uses bignum while lambdapi is limited to 2^30 - 1
  (format stream "~d" ex))

(defmethod pp-dk (stream (ac actual) &optional colon-p at-sign-p)
  "Formal parameters of theories, the `t' in `pred[t]'."
  (dklog:log-expr "actual")
  (pp-dk stream (expr ac) colon-p at-sign-p))

(defmethod pp-dk (stream (ex bitvector) &optional _colon-p _at-sign-p)
  (error "Bitvectors not handled yet."))
