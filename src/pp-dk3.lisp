;;; Export to Dedukti.
;;; This module provides the function ‘to-dk3’ which exports a PVS theory to a
;;; Dedukti3 file.
;;; TODO how to handle uppercase / lowercase identifiers?
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

(declaim (type (cons (cons symbol string) list) *dk-sym-map*))
(defparameter *dk-sym-map*
  `((|boolean| . "prop") (|bool| . "prop") (true . "true") (false . "false")
    (|type| . "{|set|}" ))
  "Maps PVS names to names of the encoding. It is also used to avoid prepending
the symbols with a module id.")

(declaim (ftype (function (syntax string) *) to-dk3))
(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (with-open-file (stream file :direction :output :if-exists :supersede)
    (let ((*print-pretty* t)
          (*print-right-margin* 78))
      (write-string "require open personoj.encodings.lhol
require personoj.encodings.tuple as T
require personoj.encodings.sum as S
require open personoj.encodings.prenex personoj.encodings.logical
  personoj.encodings.pvs_cert
require personoj.encodings.equality_tup as Eqtup
require open personoj.encodings.builtins personoj.encodings.deptype" stream)
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
  "Context enriched by LAMBDA bindings and `var-decl'. Variable declarations
`var-decl' are never removed from the context.")

(declaim (type context *ctx-var*))
(defparameter *ctx-var* nil
  "Context enriched by `var-decl' only. Not typed bound variables of LAMBDAs
seek their type into this context only (and not previous LAMBDA bindings).")

(declaim (type context *ctx-local*))
(defparameter *ctx-local* nil
  "Context used to translate rewriting definitions. Variables in this context
are translated to rewriting variables.")

(declaim (type context *ctx-thy*))
(defparameter *ctx-thy* nil
  "Contain theory formals. All declared (and defined) symbols must abstract on
the definitions of this context using `pprint-prenex'. For instance, if this
variable contains ((t . TYPE) (n . nat)), then all symbols will start by
quantifying over a type and a natural. Note that we cannot separate types from
value declarations because types may depend on values.")

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
  (:method (ex) (type ex)))

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

(defun print-debug (ind &optional obj)
  "Prints debug information on standard output with IND an indication (typically
a function name from where the debug is called)."
  (format t "~%~a:" ind)
  (format t "~%~a:" obj)
  (format t "~%  tct:~i~<~a~:>" (list *ctx-thy*))
  (format t "~%  tst:~i~<~a~:>" (list *ctx-thy-subtypes*))
  (format t "~%  ctx:~i~<~a~:>" (list *ctx*))
  (format t "~%  tup:~i~<~a~:>" (list *packed-tuples*))
  (format t "~%  lct:~i~<~a~:>" (list *ctx-local*)))

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
  "Transform the list of list of arguments in ARGS into a list. For any element
E of ARGS, if E has length one, the result is the element. Otherwise, a new
variable `v' is created, its type is sought from `*ctx*' and we add a binding
`(x . (n . v))' for each symbol in E, where `x' is the symbol, `n' is its
position in E. The list of variables and the mapping are returned as a `cons'
cell."
  (labels ((type-with-ctx (elt)
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
creating a variable."
             (declare (type list l))
             (if (= 1 (length l))
                 (let ((elt (car l)))
                   (make-bind-decl (id elt) (type-with-ctx elt)))
                 (let ((var (intern (fresh-var :prefix "tup")))
                       (typ (make-tupletype (mapcar #'type-with-ctx l))))
                   (make-bind-decl var typ))))
           (get-pspec (l var)
             (declare (type list l))
             (declare (type symbol var))
             (let ((len (length l)))
               (unless (= 1 len)
                 (loop for e in l
                       for i upto (- len 1)
                       collect (cons (id e) (cons i (cons len var))))))))
    (if (null args) (cons vars projspec)
        (destructuring-bind (hd &rest tl) args
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

(declaim (ftype (function (type-expr type-expr stream *) null) pprint-funtype))
(defgeneric pprint-funtype (domain range stream &optional wrap)
  (:documentation "Print the function type from DOMAIN to RANGE, taking care of
currification.")
  (:method (domain range stream &optional wrap)
    "Build the function type [DOMAIN -> RANGE]."
    (with-parens (stream wrap)
      (format stream "~:/pvs:pp-dk/ ~~> ~:_~/pvs:pp-dk/" domain range))))

(declaim (ftype (function (expr (polylist bind-decl) stream *) null)
                pprint-abstraction))
(defun pprint-abstraction (ex bindings stream &optional wrap)
  "Print expression EX on stream STREAM abstracting arguments in BINDINGS (with
a λ). Note that the context `*ctx*' is enriched on each printed binding. The
binding is automatically removed from the context thanks to dynamic scoping."
  (labels
      ((pprint-binding (id dtype)
         (declare (type symbol id))
         (declare (type type-expr dtype))
         (with-parens (stream t)
           (pprint-logical-block (stream nil)
             (pp-sym stream id)
             (write-string ": " stream)
             (pprint-newline :fill stream)
             (let ((dec (if (is-*type*-p dtype) "Ty" "El")))
               (write-string dec stream))
             (write-char #\space stream)
             (pp-dk stream dtype t))))
       (pprint-abstraction* (term bindings)
         "Print term TERM abstracting on bindings BINDINGS. Bindings are
typed if they were typed in PVS (they may be typed by a variable declaration)."
         (declare (type (or expr type-expr) term))
         (declare (type (polylist bind-decl) bindings))
         (if (null bindings)
             (format stream ", ~:_~/pvs:pp-dk/" term)
             (with-slots (id declared-type) (car bindings)
               (if declared-type
                   (progn
                     (pprint-binding id declared-type)
                     (let* ((*ctx* (acons id declared-type *ctx*)))
                       ;; Print the body with the variable in context
                       (pprint-abstraction* term (cdr bindings))))
                   ;; Otherwise, the variable is already declared
                   (progn
                     ;; If the type of the binding is not specified,
                     ;; then the variable must be typed by a x: VAR t
                     ;; declaration, and hence end up in `*ctx-var*'.
                     (pprint-binding id (cdr (assoc id *ctx-var*)))
                     (pprint-abstraction* term (cdr bindings))))))))
    (if (null bindings)
        (pp-dk stream ex wrap)
        (with-parens (stream wrap)
          (pprint-logical-block (stream nil)
            (write-string "λ" stream)
            (pprint-abstraction* ex bindings))))))

(declaim (ftype (function (stream (or forall-expr exists-expr) * * string) null)
                pp-quantifier))
(defun pp-quantifier (stream expr &optional colon-p at-sign-p quant)
  (print-debug "pp-quantifier")
  (with-slots (bindings expression) expr
    (if (null bindings)
        (pp-dk stream expression colon-p at-sign-p)
        (let* ((newex (copy expr)))
          (setf (slot-value newex 'bindings) (cdr bindings))
          (with-parens (stream colon-p)
            (pprint-logical-block (stream nil)
              (write-string quant stream)
              (write-char #\Space stream)
              (with-parens (stream t)
                (pprint-abstraction newex (list (car bindings)) stream))))))))

;; REVIEW rename into `abstract-thy' or something of the kind
(declaim (ftype (function (type-expr symbol stream *) null) pprint-prenex))
(defun pprint-prenex (tex kind stream &optional wrap)
  "Print type expression TEX of kind KIND with prenex polymorphism on
`*ctx-thy*'. KIND can be symbol `kind', `set' or `bool'."
  (labels ((pprint-dtype (ctx)
             "Print the type that is able to accept elements of context CTX as
dependent argument to yield type TEX."
             (declaim (type context ctx))
             (if (null ctx)
                 (pp-dk stream tex t)
                 (destructuring-bind ((id . typ) &rest tl) ctx
                   (with-parens (stream t)
                     (case kind
                       ('kind
                        (format stream "~:/pvs:pp-dk/ *> " typ)
                        (pprint-dtype tl))
                       ('set
                        (format stream "arrd {~/pvs:pp-dk/} " typ)
                        (with-parens (stream t)
                          (format stream "λ~/pvs:pp-sym/," id)
                          (pprint-newline :miser stream)
                          (pprint-dtype tl)))
                       ('bool
                        (format stream "∀ {~/pvs:pp-dk/} " typ)
                        (with-parens (stream t)
                          (format stream "λ~/pvs:pp-sym/," id)
                          (pprint-newline :miser stream)
                          (pprint-dtype tl))))))))
           (ppqu (qu ctx)
             "Print quantifier QU and abstract over the variable of car of CTX."
             (declaim (type string qu))
             (declaim (type context ctx))
             (format stream "~a " qu)
             (with-parens (stream t)
               (pprint-logical-block (stream nil)
                 (format stream "λ~/pvs:pp-sym/, " (caar ctx))
                 (pprint-newline :fill stream)
                 (ppp (cdr ctx)))))
           (ppp (ctx)
             "Print quantifier and abstract on car of CTX or abstract on values
of `*ctx-thy*'."
             (declaim (type context ctx))
             (if
              (null ctx)
              (let ((scheme (case kind
                              ('kind "scheme_k ")
                              ('set "scheme_s ")
                              ('bool "")))
                    (ctx-values (remove-if
                                 #'(lambda (idt) (is-*type*-p (cdr idt)))
                                 (reverse *ctx-thy*))))
                (write-string scheme stream)
                (pprint-dtype ctx-values))
              (let ((quant (case kind ('kind "∀K") ('set "∀S") ('bool "∀B"))))
                (ppqu quant ctx)))))
    (with-parens (stream wrap)
      (ppp (remove-if-not #'(lambda (idt) (is-*type*-p (cdr idt)))
                          (reverse *ctx-thy*))))))

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
               (let* ((pred (predicate (type-value hd)))
                      (*ctx-thy-subtypes*
                        (acons (id hd) (id pred) *ctx-thy-subtypes*))
                      (*ctx-thy* (acons (id pred) (type pred) *ctx-thy*)))
                 (process-formals tl theory)))
              ((formal-type-decl? hd)
               (let ((*ctx-thy* (acons (id hd) *type* *ctx-thy*)))
                 (process-formals tl theory)))
              ((formal-const-decl? hd)
               (let* ((*ctx-thy* (acons (id hd) (declared-type hd)
                                        *ctx-thy*))
                      ;; REVIEW adding to *ctx* might be superfluous
                      (*ctx* (acons (id hd) (declared-type hd) *ctx*)))
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
              do (fresh-line stream)))
      (process-formals formals-sans-usings theory))))

(defmethod pp-dk (stream (imp importing) &optional colon-p at-sign-p)
  "Prints importing declaration IMP."
  (with-slots (theory-name) imp
    (format stream "require ~a" theory-name)))

;;; Declarations

(defmethod pp-dk (stream (decl type-decl) &optional colon-p at-sign-p)
  "t: TYPE."
  (print "type decl")
  (with-slots (id) decl
    (pprint-logical-block (stream nil)
      (format stream "constant symbol ~/pvs:pp-sym/: ~2i~:_El_k " id)
      (pprint-prenex *type* 'kind stream t))
    (fresh-line stream)
    ;; No dynamic scoping because we never remove elements from the signature
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "t: TYPE = x."
  (print "type-eq-decl")
  (with-slots (id type-expr formals) decl
    (pprint-logical-block (stream nil)
      (format stream "symbol ~/pvs:pp-sym/: El_k " id)
      (pprint-prenex *type* 'kind stream t)
      (write-string " ≔ " stream)
      (pprint-indent :block 2 stream)
      (pprint-newline :fill stream)
      (let* ((form-spec (pack-arg-tuple formals))
             (*packed-tuples* (cdr form-spec))
             (ctx (mapcar #'ctxe->bind-decl (reverse *ctx-thy*)))
             (bindings (concatenate 'list ctx (car form-spec))))
        (pprint-abstraction type-expr bindings stream)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s"
  (print-debug "type from" decl)
  (with-slots (id predicate supertype) decl
    ;; PREDICATE is a type declaration
    (pprint-logical-block (stream nil)
      (format stream "symbol ~/pvs:pp-sym/: " id)
      (pprint-indent :block 2 stream)
      (pprint-newline :fill stream)
      (write-string "El_k " stream)
      (pprint-prenex *type* 'kind stream t)
      (write-string " ≔ " stream)
      (pprint-newline :fill stream)
      (pprint-abstraction
       ;; Build properly the subtype expression for printing
       (mk-subtype supertype (mk-name-expr (id predicate)))
       (mapcar #'ctxe->bind-decl (reverse *ctx-thy*)) stream))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl formula-decl) &optional colon-p at-sign-p)
  (print "formula-decl")
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
        (pprint-logical-block (stream nil)
          (unless axiomp
            (write-string "opaque" stream)
            (fresh-line stream))
          (write-string "symbol" stream)
          (format stream " ~/pvs:pp-sym/: " id)
          (pprint-indent :block 2 stream)
          (pprint-newline :fill stream)
          (write-string "Prf " stream)
          (pprint-prenex defn 'bool stream t))
        (fresh-line stream)
        (setf *signature* (cons id *signature*))
        (unless axiomp
          (format stream "≔ begin~%")
          ;; TODO: export proof
          (format stream "abort"))))))

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (print-debug "const-decl")
  (with-slots (id type definition formals) decl
    (format stream "// Constant declaration ~a~%" id)
    (if definition
        (let* ((form-proj (pack-arg-tuple formals))
               (*packed-tuples* (cdr form-proj))
               (ctx-thy (mapcar #'ctxe->bind-decl (reverse *ctx-thy*)))
               (bindings (concatenate 'list ctx-thy (car form-proj))))
          (pprint-logical-block (stream nil)
            (format stream "symbol ~/pvs:pp-sym/: " id)
            (pprint-indent :block 2 stream)
            (pprint-newline :fill stream)
            (write-string "El_s " stream)
            (pprint-prenex type 'set stream t)
            (write-string " ≔ " stream)
            (pprint-newline :fill stream)
            (pprint-abstraction definition bindings stream)))
        (pprint-logical-block (stream nil)
          (format stream "symbol ~/pvs:pp-sym/: " id)
          (pprint-indent :block 2 stream)
          (pprint-newline :fill stream)
          (write-string "El_s " stream)
          (pprint-prenex type 'set stream t)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl def-decl) &optional colon-p at-sign-p)
  (print-debug "def-decl")
  (with-slots (id definition formals type) decl
    (let* ((form-spec (pack-arg-tuple formals))
           (*packed-tuples* (cdr form-spec))
           (ctx-thy (mapcar #'ctxe->bind-decl *ctx-thy*)))
      (format stream "// Recursive declaration ~a~%" id)
      (pprint-logical-block (stream nil)
        (format stream "symbol ~/pvs:pp-sym/: " id)
        (pprint-indent :block 2 stream)
        (pprint-newline :fill stream)
        (write-string "El_s " stream)
        (pprint-prenex type 'set stream t)
        (pprint-newline :mandatory stream))
      (setf *signature* (cons id *signature*))
      (format stream "rule ~:/pvs:pp-sym/ ~{$~/pvs:pp-sym/ ~}~_ ↪ ~:_"
              id (concatenate 'list
                              (mapcar #'car *ctx-thy*)
                              (mapcar #'id (car form-spec))))
      (let ((*ctx-local* (concatenate 'list
                                      (ctx-of-bindings (car form-spec))
                                      *ctx-thy*))
            (*ctx* nil))
        (pp-dk stream definition colon-p at-sign-p)))))

(defmethod pp-dk (stream (decl conversion-decl) &optional colon-p at-sign-p)
  "CONVERSION elt, there are conversion(plus|minus)-decl as well."
  (print-debug "conversion-decl")
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
  (print-debug "application-judgement" decl)
  (with-slots (id formals declared-type judgement-type name) decl
    (format stream "// Application judgement \"~a\"~%" id)))


(defmethod pp-dk (stream (decl expr-judgement) &optional colon-p _at-sign-p)
  (print-debug "expr-judgement")
  (with-slots (id expr free-parameters) decl
    (let
        ;; See classes-decl.lisp:656
        ((exp (first expr))
         (typ (second expr)))
      (format stream "// ~a~%" free-parameters)
      (format stream "// @cast _ ~:/pvs:pp-dk/ ~:/pvs:pp-dk/ P :-~&" typ exp)
      (format stream "//   free-param = ...~&")
      (format stream "//   P = ~/pvs:pp-sym/ freeparams" id))))

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
  (print-debug "tuple-type")
  (with-slots (types) te
    (with-parens (stream colon-p)
      (pprint-logical-block (stream nil)
        (write-string "T.t " stream)
        ;; Any tuple type has at least two elements
        (if (= 2 (length types))
            (destructuring-bind (s u) types
              (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/" s u))
            (destructuring-bind (hd &rest tl) types
              (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/"
                      hd (make-tupletype tl))))))))

(defmethod pp-dk (stream (te subtype) &optional colon-p at-sign-p)
  "{n: nat | n /= zero} or (x | p(x)), see classes-decl.lisp:824"
  (print-debug "subtype" te)
  (with-slots (supertype predicate) te
    (with-parens (stream colon-p)
      (pprint-logical-block (stream nil)
        (write-string "@psub " stream)
        (pprint-indent :block 0 stream)
        (pprint-newline :fill stream)
        ;; REVIEW: can the supertype be `nil'?
        (format stream "~:/pvs:pp-dk/ " supertype)
        (pprint-indent :block 6 stream)
        (pprint-newline :fill stream)
        (pp-dk stream predicate t at-sign-p)))))

(defmethod pp-dk (stream (te expr-as-type) &optional colon-p at-sign-p)
  "Used in e.g. (equivalence?), that is, a parenthesised expression used as a
type."
  (print-debug "expr-as-type" te)
  (with-slots (expr) te
    (with-parens (stream colon-p)
      (pprint-logical-block (stream nil)
        ;; REVIEW: should get the domain of expression E and pass it as first
        ;; argument of psub
        (write-string "@psub _ " stream)
        (pp-dk stream expr t at-sign-p)))))

(defmethod pp-dk (stream (te simple-expr-as-type) &optional colon-p at-sign-p)
  "Used in e.g. (equivalence?) without inheriting subtypes. I don't know when it
can be used."
  (print-debug "simpl-expr-as-type" te)
  (with-slots (expr) te
    (pp-dk stream expr colon-p at-sign-p)))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM. Used for instance with dependent
(sub)types `subt(i)` where `subt(i) = {x: ... | f(i)}`."
  (print-debug "type-application" te)
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
  (print-debug "funtype")
  (with-slots (domain range) te
    (pprint-funtype domain range stream colon-p)))

;;; Expressions

(defmethod pp-dk (stream (ex name) &optional colon-p at-sign-p)
  "Print name NAME applying theory formal parameters if needed. Takes care of
name resolution"
  (print-debug "name")
  (with-slots (id mod-id actuals) ex
    (cond
      ;; Member of an unpacked tuple: as it has been repacked, we transform this
      ;; to successsion of projections
      ((assoc id *packed-tuples*)
       (destructuring-bind (v n m . w) (assoc id *packed-tuples*)
         (pprint-proj-spec w n m stream)))
      ((assoc id *ctx*) (pp-sym stream id))
      ((assoc id *ctx-local*) (format stream "$~/pvs:pp-sym/" id))
      ((member id *signature*)
       (with-parens (stream (consp *ctx-thy*))
         (pp-sym stream id)
         (unless (null *ctx-thy*)
           ;; Apply theory arguments to symbols of signature
           (format stream " ~{~:/pvs:pp-dk/~^ ~}"
                   ;; Print arguments through ‘pp-dk’ because they might be in
                   ;; ‘ctx-local’
                   (flet ((cdr-*type*-p (id-ty) (is-*type*-p (cdr id-ty))))
                     (let* ((ctx-thy (reverse *ctx-thy*))
                            (thy-types (remove-if-not #'cdr-*type*-p ctx-thy))
                            (thy-val   (remove-if #'cdr-*type*-p ctx-thy)))
                       (mapcar #'(lambda (st) (mk-name-expr (car st)))
                               (concatenate 'list thy-types thy-val))))))))
      ((assoc id *ctx-thy*) (pp-sym stream id))
      ;; The symbol is a type declared as TYPE FROM in theory parameters,
      ;; we print it as a predicate sub-type
      ((assoc id *ctx-thy-subtypes*)
       (format stream "(psub ~/pvs:pp-sym/)"
               (cdr (assoc id *ctx-thy-subtypes*))))
      ;; Symbol of the encoding
      ((assoc id *dk-sym-map*) (pp-sym stream id))
      ;; Otherwise, it’s a symbol from an imported theory
      (t (with-parens (stream (consp actuals))
           (pprint-logical-block (stream nil)
             (unless (null mod-id)
               ;; If `mod-id’ is `nil’, then symbol comes from prelude, which is
               ;; require-open’d
               (pp-sym stream mod-id)
               (write-char #\. stream))
             (pp-sym stream id)
             (format stream "~{ ~:/pvs:pp-dk/~}" actuals)))))))

(defmethod pp-dk (stream (ex lambda-expr) &optional colon-p _at-sign-p)
  "LAMBDA (x: T): t"
  (print "lambda-expr")
  (with-slots (bindings expression) ex
    (pprint-abstraction expression bindings stream t)))

(defmethod pp-dk (stream (ex exists-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∃"))

(defmethod pp-dk (stream (ex forall-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∀"))

(defmethod pp-dk (stream (ex application) &optional colon-p _at-sign-p)
  "Print application EX. The expression EX ``f(e1,e2)(g1,g2)'' will be printed
as ``f (σcons e1 e2) (σcons g1 g2)''."
  (print-debug "application")
  (if (null (type ex))
      ;; For some reason, application-judgements end up as application
      ;; expressions. We don’t handle them here.
      (format stream "// Application judgement")
      (let* ((op (operator* ex))
             (dom (domain* (type-of-expr op)))
             (args (arguments* ex)))
        (with-parens (stream colon-p)
          (pprint-logical-block (stream nil)
            (pp-dk stream op)
            (write-char #\space stream)
            (pprint-indent :block 0 stream)
            (pprint-newline :fill stream)
            ;; Perhaps a processing will be necessary if `args’ `dom’ do not
            ;; have same length (in case of partial application)
            (pprint-logical-block (stream args)
              (let ((args (pprint-pop)))
                (pp-dk stream
                       (if (<= 2 (length args))
                           ;; There shouldn't be any additional TCC generated by
                           ;; `make!-tuple-expr', but who knows.
                           ;; REVIEW: use mk-tuple-expr, which doesn't
                           ;; typecheck?
                           (make!-tuple-expr args)
                           (car args))
                       t))
              (pprint-exit-if-list-exhausted)
              (write-char #\space stream)))))))

(defmethod pp-dk (stream (ex projection-application)
                  &optional _colon-p _at-sign-p)
  "For projections of the form t`2."
  (print-debug "projection-application" ex)
  (with-slots (id index argument) ex
    (let ((len (length (types (type argument))))
          (ident (id argument)))
      (pprint-proj-spec ident index len stream))))

(defmethod pp-dk (stream (ex tuple-expr) &optional colon-p at-sign-p)
  "Prints tuples ``(e1, e2, e3)'' as ``(σcons e1 (σcons e2 e3))''. Note that we
use implicit arguments for σcons. Making arguments explicit prevents the
translation to scale up, because expressions become too verbose."
  (print-debug "tuple-expr" ex)
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
  (print-debug "branch")
  (destructuring-bind (prop then else) (exprs (argument ex))
    (with-parens (stream colon-p)
      (pprint-logical-block (stream nil)
        (format stream "if ~:/pvs:pp-dk/ ~2i~:_" prop)
        (format stream "~<(λ~a, ~1i~:_~/pvs:pp-dk/)~:>"
                (list (fresh-var) then))
        (write-char #\Space stream)
        (format stream "~<(λ~a, ~1i~:_~/pvs:pp-dk/)~:>"
                (list (fresh-var) else))))))

;;; REVIEW: factorise disequation and equation

(defmethod pp-dk (stream (ex disequation) &optional colon-p at-sign-p)
  "/=(A, B)"
  (print "disequation")
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
  (print "equation")
  (with-parens (stream colon-p)
    (let* ((eq-ty (type (operator ex)))
           (dom (types (domain eq-ty)))
           (tyl (car dom))
           (tyr (cadr dom)))
      (assert (equal tyl tyr) (tyl tyr)
              "Equality types ~S and ~S are not equal." tyl tyr)
      (with-binapp-args (argl argr ex)
        (format stream
                "@Eqtup.eq ~:/pvs:pp-dk/ (T.cons ~:/pvs:pp-dk/ ~:/pvs:pp-dk/)"
                tyl argl argr)))))

(defmethod pp-dk (stream (ex conjunction) &optional colon-p at-sign-p)
  "AND(A, B)"
  (print "conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "and ~i~:_~:/pvs:pp-dk/ ~:_(λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex infix-conjunction) &optional colon-p at-sign-p)
  "A AND B"
  (print "infix-conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ ∧ ~i~:_(λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex disjunction) &optional colon-p at-sign-p)
  "OR(A, B)"
  (print "disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "or ~i~:_~:/pvs:pp-dk/ ~:_(λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex infix-disjunction) &optional colon-p at-sign-p)
  "A OR B"
  (print "infix-disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ ∨ ~i~:_(λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex implication) &optional colon-p at-sign-p)
  "IMPLIES(A, B)"
  (print "implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "imp ~:/pvs:pp-dk/ ~:_(λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex infix-implication) &optional colon-p at-sign-p)
  "A IMPLIES B"
  (print "infix-implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ ⊃ ~i~:_(λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex negation) &optional colon-p _at-sign-p)
  "NOT(A), there is also a `unary-negation' that represents NOT A."
  (print "negation")
  (with-parens (stream colon-p)
    ;; NOTE we might be able to remove parens (see with LP precedence)
    (format stream "¬ ~:/pvs:pp-dk/" (argument ex))))

(defmethod pp-dk (stream (ex number-expr) &optional colon-p at-sign-p)
  (print "number-expr")
  ;; PVS uses bignum while lambdapi is limited to 2^30 - 1
  (format stream "~d" ex))

(defmethod pp-dk (stream (ac actual) &optional colon-p at-sign-p)
  "Formal parameters of theories, the `t' in `pred[t]'."
  (print-debug "actual")
  (pp-dk stream (expr ac) colon-p at-sign-p))

(defmethod pp-dk (stream (ex bitvector) &optional _colon-p _at-sign-p)
  (error "Bitvectors not handled yet."))
