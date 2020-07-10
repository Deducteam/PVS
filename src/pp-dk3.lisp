;;; Export to Dedukti.
;;; This module provides the function ‘to-dk3’ which exports a PVS theory to a
;;; Dedukti3 file.
;;; TODO some definitions seem to be unfolded every time (type definitions)
;;; TODO non dependent product type with elements of type TYPE and equivalence
;;; between [[t1, ..., tn] -> r] and [t1 -> [t2 -> ... [tn -> r] ... ]]
;;; TODO module resolution and importing
;;; TODO recursive functions
;;; TODO assuming sections
;;; TODO dependent pairs
;;; TODO dependent products
;;; TODO records

(in-package :pvs)
(require "alexandria")
(export '(to-dk3))

(deftype polylist (ty)
  `(or (cons ,ty list) null))

(defparameter *explicit* nil
  "Set to non-nil avoid using implicits.")

(declaim (type (cons (cons symbol symbol) list) *dk-sym-map*))
(defparameter *dk-sym-map*
  `((|boolean| . bool) (|bool| . bool) (|type| . ,(intern "{|set|}"))
    (true . true) (false . false))
  "Maps PVS names to names of the encoding. It is also used to avoid prepending
the symbols with a module id.")

(declaim (ftype (function (syntax string) *) to-dk3))
(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (with-open-file (stream file :direction :output :if-exists :supersede)
    (let ((*print-pretty* t)
          (*print-right-margin* 78))
      (format stream "~{~/pvs:pp-reqopen/~&~}"
              '("lhol" "pvs_cert" "subtype" "bool_hol" "builtins" "prenex"
                "unif_rules" "deptype" "pairs"))
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

(declaim (ftype (function () string) fresh-var))
(defun fresh-var ()
  "Provide a fresh variable name."
  (let ((var-name (format nil "pvs~d" *var-count*)))
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

(defun print-debug (ind)
  "Prints debug information on standard output with IND an indication (typically
a function name from where the debug is called)."
  (format t "~%~a:" ind)
  (format t "~%  tct:~i~<~a~:>" (list *ctx-thy*))
  (format t "~%  tst:~i~<~a~:>" (list *ctx-thy-subtypes*))
  (format t "~%  ctx:~i~<~a~:>" (list *ctx*))
  (format t "~%  lct:~i~<~a~:>" (list *ctx-local*)))

;;; Specialised printing functions

(declaim (ftype (function (stream symbol * *) null) pp-sym))
(defun pp-sym (stream sym &optional colon-p at-sign-p)
  "Prints symbol SYM to stream STREAM, enclosing it in braces {||} if
necessary."
  (flet ((sane-charp (c)
           (cond
             ((alphanumericp c) t)
             ((char= c #\_) t)
             (t nil))))
    (let ((dk-sym (assoc sym *dk-sym-map*)))
      (cond (dk-sym (format stream "~(~a~)" (cdr dk-sym)))
            ((every #'sane-charp (string sym)) (format stream "~(~a~)" sym))
            (t (format stream "{|~(~a~)|}" sym))))))

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
         (let ((dec (if (is-*type*-p dtype) "θ" "η")))
           (format stream "~<(~/pvs:pp-sym/: ~:_~a ~:/pvs:pp-dk/)~:>"
                   (list id dec dtype))))
       (pprint-abstraction* (term bindings)
         "Print term TERM abstracting on bindings BINDINGS. Bindings are
typed if they were typed in PVS (they may be typed by a variable declaration)."
         (if (null bindings)
             (format stream ", ~:_~/pvs:pp-dk/" term)
             (with-slots (id type declared-type) (car bindings)
               (if declared-type
                   (let* ((*ctx* (acons id declared-type *ctx*)))
                     (pprint-binding id declared-type)
                     (pprint-abstraction* term (cdr bindings)))
                   ;; Otherwise, the variable is already declared
                   (progn
                     (pprint-binding id (cdr (assoc id *ctx*)))
                     (pprint-abstraction* term (cdr bindings))))))))
    (declaim (ftype (function (symbol type-expr) null) pprint-binding))
    (declaim (ftype (function (expr (polylist bind-decl) null))
                    pprint-abstraction*))
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

(declaim (ftype (function ((polylist expr) stream *) null) pprint-tuple))
(defun pprint-tuple (args stream &optional wrap)
  (with-parens (stream wrap)
    (pprint-logical-block (stream nil)
      (format stream "ndpair"))))

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

(declaim (ftype (function (stream string * *) null) pp-reqopen))
(defun pp-reqopen (stream mod &optional colon-p at-sign-p)
  "Prints a require open module MOD directive on stream STREAM."
  (format stream "require open personoj.encodings.~a" mod))

(declaim (ftype (function (stream (cons expr type-expr) * *) null) pp-cast))
(defun pp-cast (stream at &optional colon-p _at-sign-p)
  "Print a casting of `car' of AT to type `cdr' of AT."
  (print-debug "pp-cast")
  (with-parens (stream colon-p)
    (format stream
            "cast ~:[~;{_} ~]~:/pvs:pp-dk/ _ ~:/pvs:pp-dk/ _"
            *explicit* (cdr at) (car at))))

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
         (declaim (type var-decl vd))
         (declaim (type list rest))
         (with-slots (id declared-type) vd
           (let ((*ctx* (acons id declared-type *ctx*)))
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
         (declaim (type (polylist formal-decl) formals))
         (declaim (type list theory))
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
                 (process-formals tl theory))))))))
    (with-slots (id theory formals-sans-usings) mod
      (format stream "// Theory ~a~%" id)
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
      (format stream "constant symbol ~/pvs:pp-sym/: ~2i~:_ϕ " id)
      (pprint-prenex *type* 'kind stream t))
    (fresh-line stream)
    (setf *signature* (cons id *signature*))
    (format stream "rule μ ~/pvs:pp-sym/ ↪ ~/pvs:pp-sym/~%" id id)
    (format stream "rule π {~/pvs:pp-sym/} ↪ λ_, true" id)))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "t: TYPE = x."
  (print "type-eq-decl")
  (with-slots (id type-expr formals) decl
    (pprint-logical-block (stream nil)
      (format stream "definition ~/pvs:pp-sym/: ϕ " id)
      (pprint-prenex *type* 'kind stream t)
      (write-string " ≔ " stream)
      (pprint-indent :block 2 stream)
      (pprint-newline :fill stream)
      (let* ((formals (alexandria:flatten formals))
             (ctx (mapcar #'ctxe->bind-decl (reverse *ctx-thy*)))
             (bindings (concatenate 'list ctx formals)))
        (pprint-abstraction type-expr bindings stream)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s"
  (print "type from")
  (with-slots (id type-value) decl
    (pprint-logical-block (stream nil)
      (format stream "definition ~/pvs:pp-sym/: " id)
      (pprint-indent :block 2 stream)
      (pprint-newline :fill stream)
      (write-string "ϕ " stream)
      (pprint-prenex *type* 'kind stream t)
      (write-string " ≔ " stream)
      (pprint-newline :fill stream)
      (pprint-abstraction
       type-value (mapcar #'ctxe->bind-decl (reverse *ctx-thy*)) stream))
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
          (format stream (if axiomp "symbol" "theorem"))
          (format stream " ~/pvs:pp-sym/: " id)
          (pprint-indent :block 2 stream)
          (pprint-newline :fill stream)
          (write-string "ε " stream)
          (pprint-prenex defn 'bool stream t))
        (fresh-line stream)
        (setf *signature* (cons id *signature*))
        (unless axiomp
          (format stream "proof~%")
          ;; TODO: export proof
          (format stream "abort"))))))

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (print "const-decl")
  (with-slots (id type definition formals) decl
    (format stream "// Constant declaration ~a~%" id)
    (if definition
        (let* ((formals (alexandria:flatten formals))
               (ctx-thy (mapcar #'ctxe->bind-decl (reverse *ctx-thy*)))
               (bindings (concatenate 'list ctx-thy formals)))
          (pprint-logical-block (stream nil)
            (format stream "definition ~/pvs:pp-sym/: " id)
            (pprint-indent :block 2 stream)
            (pprint-newline :fill stream)
            (write-string "χ " stream)
            (pprint-prenex type 'set stream t)
            (write-string " ≔ " stream)
            (pprint-newline :fill stream)
            (pprint-abstraction definition bindings stream)))
        (pprint-logical-block (stream nil)
          (format stream "symbol ~/pvs:pp-sym/: " id)
          (pprint-indent :block 2 stream)
          (pprint-newline :fill stream)
          (write-string "χ " stream)
          (pprint-prenex type 'set stream t)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl def-decl) &optional colon-p at-sign-p)
  (print-debug "def-decl")
  (with-slots (id definition formals type) decl
    (let ((formals (alexandria:flatten formals))
          (ctx-thy (mapcar #'ctxe->bind-decl *ctx-thy*)))
      (format stream "// Recursive declaration ~a~%" id)
      (pprint-logical-block (stream nil)
        (format stream "symbol ~/pvs:pp-sym/: " id)
        (pprint-indent :block 2 stream)
        (pprint-newline :fill stream)
        (write-string "χ " stream)
        (pprint-prenex type 'set stream t)
        (pprint-newline :mandatory stream))
      (setf *signature* (cons id *signature*))
      (format stream "rule ~:/pvs:pp-sym/ ~{$~/pvs:pp-sym/ ~}~_ ↪ ~:_"
              id (concatenate 'list
                              (mapcar #'car *ctx-thy*)
                              (mapcar #'id formals)))
      (let ((*ctx-local* (concatenate 'list
                                      (ctx-of-bindings formals)
                                      *ctx-thy*))
            (*ctx* nil))
        (pp-dk stream definition colon-p at-sign-p)))))

(defmethod pp-dk (stream (decl conversion-decl) &optional colon-p at-sign-p)
  "CONVERSION elt, there are conversion(plus|minus)-decl as well."
  (with-slots (id) decl
    (format stream "// Conversion: ~/pvs:pp-sym/" id)))

(defmethod pp-dk (stream (decl auto-rewrite-decl) &optional colon-p at-sign-p)
  "AUTO_REWRITE, there are auto-rewrite-(plus|minus)-decl as well."
  (format stream "// Auto rewrite ~/pvs:pp-sym/" (id decl)))

;; TODO
(defmethod pp-dk (stream (decl application-judgement)
                  &optional colon-p at-sign-p)
  "Print the judgement. A TCC is generated with the same `id'.
See parse.lisp:826"
  (print "application-judgement")
  (with-slots (id formals declared-type judgement-type name) decl
    (format stream "// Application judgement~%")
    (let* ((args (alexandria:flatten formals))
           (term (make!-application name args)))
      (format stream "// @cast _ ~:/pvs:pp-dk/ _ ~:/pvs:pp-dk/ P :-~&"
              declared-type term)
      (let* ((hd (make-instance 'name-expr :id id)) ; Unsafe here
             (uterm (make-instance 'application :operator hd
                                                :argument args)))
        (format stream "//   P = ~/pvs:pp-dk/.~&" uterm)))))


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

(defmethod pp-dk (stream (te tupletype) &optional colon-p at-sign-p)
  "[bool, bool] but also [bool, bool -> bool]"
  (print-debug "tuple-type")
  (with-slots (types) te
    (with-parens (stream colon-p)
      (pprint-logical-block (stream nil)
        (write-string "σ " stream)
        ;; Any tuple type has at least two elements
        (if (= 2 (length types))
            (destructuring-bind (s u) types
              (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/" s u))
            (destructuring-bind (hd &rest tl) types
              (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/"
                      hd (make-tupletype tl))))))))

(defmethod pp-dk (stream (te subtype) &optional colon-p at-sign-p)
  "{n: nat | n /= zero} or (x | p(x)), see classes-decl.lisp:824"
  (print-debug "subtype")
  (with-slots (supertype predicate) te
    (with-parens (stream colon-p)
      (pprint-logical-block (stream nil)
        (write-string "psub " stream)
        (pprint-indent :block 0 stream)
        (when (and *explicit* supertype)
          (format stream "{~/pvs:pp-dk/} " supertype)
          (pprint-indent :block 5 stream))
        (pprint-newline :fill stream)
        (pp-dk stream predicate t at-sign-p)))))

(defmethod pp-dk (stream (te expr-as-type) &optional colon-p at-sign-p)
  "Used in e.g. (equivalence?)"
  (print-debug "expr-as-type")
  (pp-dk stream (expr te) colon-p at-sign-p))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM."
  (print "type app")
  (with-slots (type parameters) te
    (when colon-p (format stream "("))
    (format stream "~<~/pvs:pp-dk/ ~i~:_~{/pvs:pp-dk/~^ ~}~:>"
            (list type parameters))
    (when colon-p (format stream ")"))))

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
           ;; FIXME it seems that symbols from the prelude have ‘nil’ as
           ;; ‘mod-id’
           (format stream "~/pvs:pp-sym/.~/pvs:pp-sym/" mod-id id)
           (format stream "~{ ~:/pvs:pp-dk/~}" actuals))))))

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
  "Print application EX, applying casts to the arguments. The expression EX
``f(e1,e2)(g1,g2)'' will be printed as
``f (cast t _ (σcons e1 e2) _) (cast u _ (σcons g1 g2) _)''."
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
            (pprint-logical-block (stream (pairlis args dom))
              (let* ((args-ty (pprint-pop))
                     (args (car args-ty))
                     (ty (cdr args-ty)))
                (pp-cast stream
                         (if (<= 2 (length args))
                             (cons (make!-tuple-expr args) ty)
                             (cons (car args) ty))
                         t))
              (pprint-exit-if-list-exhausted)
              (write-char #\space stream)))))))

(defmethod pp-dk (stream (ex tuple-expr) &optional colon-p at-sign-p)
  (print-debug "tuple-expr")
  (with-slots (exprs) ex
    ;; Tuple types have at least 2 elements (PVS invariant)
    (with-parens (stream colon-p)
      (cond
        ((= 2 (length exprs))
         (destructuring-bind (x y) exprs
           (format stream "σcons ~:/pvs:pp-dk/ ~:/pvs:pp-dk/" x y)))
        ((< 2 (length exprs))
         (destructuring-bind (hd &rest tl) exprs
           (format stream "σcons ~:/pvs:pp-dk/ ~:/pvs:pp-dk/"
                   hd (make!-tuple-expr tl))))
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

(defmethod pp-dk (stream (ex disequation) &optional colon-p at-sign-p)
  "/=(A, B)"
  (print "disequation")
  (with-parens (stream colon-p)
    (format stream "~<neq ~i~:_~{~:/pvs:pp-dk/~^ ~:_~}~:>" (argument ex))))

(defmethod pp-dk (stream (ex infix-disequation) &optional colon-p at-sign-p)
  "a /= b"
  (print "infix-disequation")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<~:/pvs:pp-dk/ ≠ ~i~:_~:/pvs:pp-dk/~:>"
              (list argl argr)))))

(defmethod pp-dk (stream (ex equation) &optional colon-p at-sign-p)
  "=(A, B)"
  (print "equation")
  (with-parens (stream colon-p)
    (format stream "~<eq ~i~{~:/pvs:pp-dk/~^ ~:_~}~:>" (argument ex))))

(defmethod pp-dk (stream (ex infix-equation) &optional colon-p at-sign-p)
  "a = b"
  (print "infix-equation")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<~:/pvs:pp-dk/ = ~i~:_~:/pvs:pp-dk/~:>"
              (list argl argr)))))

(defmethod pp-dk (stream (ex conjunction) &optional colon-p at-sign-p)
  "AND(A, B)"
  (print "conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<and ~i~:_~:/pvs:pp-dk/ ~:_(λ~a, ~/pvs:pp-dk/)~:>"
              (list argl (fresh-var) argr)))))

(defmethod pp-dk (stream (ex infix-conjunction) &optional colon-p at-sign-p)
  "A AND B"
  (print "infix-conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<~:/pvs:pp-dk/ ∧ ~i~:_(λ~a, ~/pvs:pp-dk/)~:>"
              (list argl (fresh-var) argr)))))

(defmethod pp-dk (stream (ex disjunction) &optional colon-p at-sign-p)
  "OR(A, B)"
  (print "disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<or ~i~:_~:/pvs:pp-dk/ ~:_(λ~a, ~/pvs:pp-dk/)~:>"
              (list argl (fresh-var) argr)))))

(defmethod pp-dk (stream (ex infix-disjunction) &optional colon-p at-sign-p)
  "A OR B"
  (print "infix-disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<~:/pvs:pp-dk/ ∨ ~i~:_(λ~a, ~/pvs:pp-dk/)~:>"
              (list argl (fresh-var) argr)))))

(defmethod pp-dk (stream (ex implication) &optional colon-p at-sign-p)
  "IMPLIES(A, B)"
  (print "implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<imp ~i~:_~:/pvs:pp-dk/ ~:_(λ~a, ~/pvs:pp-dk/)~:>"
              (list argl (fresh-var) argr)))))

(defmethod pp-dk (stream (ex infix-implication) &optional colon-p at-sign-p)
  "A IMPLIES B"
  (print "infix-implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~<~:/pvs:pp-dk/ ⊃ ~i~:_(λ~a, ~/pvs:pp-dk/)~:>"
              (list argl (fresh-var) argr)))))

(defmethod pp-dk (stream (ex negation) &optional colon-p _at-sign-p)
  "NOT(A), there is also a `unary-negation' that represents NOT A."
  (print "negation")
  (with-parens (stream colon-p)
    ;; NOTE we might be able to remove parens (see with LP precedence)
    (format stream "¬ ~:/pvs:pp-dk/" (argument ex))))

(defmethod pp-dk (stream (ex number-expr) &optional colon-p at-sign-p)
  (print "number-expr")
  ;; PVS uses bignum while lambdapi is limited to 2^30 - 1
  (with-parens (stream colon-p)
    (with-slots (type number) ex
      (format stream "~<cast ~i~:_~:/pvs:pp-dk/ ~:__ ~d _~:>"
              (list type number)))))

(defmethod pp-dk (stream (ac actual) &optional colon-p at-sign-p)
  "Formal parameters of theories, the `t' in `pred[t]'."
  (print-debug "actual")
  (pp-dk stream (expr ac) colon-p at-sign-p))

(defmethod pp-dk (stream (ex bitvector) &optional _colon-p _at-sign-p)
  (error "Bitvectors not handled yet."))
