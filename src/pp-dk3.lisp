(in-package :pvs)
(require "alexandria")
(export '(to-dk3))

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
                "unif_rules"))
      (pp-dk stream obj))))

(declaim (type type-name *type*))
(defparameter *type* (mk-type-name '|type|))

;;; Contexts

;; TODO keep resolutions in context

(declaim (type (or null (cons symbol)) *signature*))
(defparameter *signature* nil
  "Symbols defined in the theory.")

(deftype context ()
  "A context is an association list mapping symbols to types."
  '(or (cons (cons symbol type-expr) list) null))

(declaim (type context *ctx*))
(defparameter *ctx* nil
  "Context enriched by bindings. Most recent binding on top.")

(declaim (type context *ctx-local*))
(defparameter *ctx-local* nil
  "Context used to translate rewriting definitions. Variables in this context
are translated to rewriting variables.")

(declaim (ftype (function ((or null (cons bind-decl))) context)
                ctx-of-bindings))
(defun ctx-of-bindings (bindings)
  "Transforms bindings BINDINGS into a context."
  (flet ((f (bd)
           (cons (id bd) (if (declared-type bd)
                             (declared-type bd)
                             (type bd)))))
    (mapcar #'f bindings)))

(declaim (type context *ctx-thy*))
(defparameter *ctx-thy* nil
  "Contain theory formals. Slightly different from other contexts since they can
contain (dependent) types.")

(declaim (ftype (function (formal-decl) (cons symbol type-expr)) cform->ctxe))
(defgeneric cform->ctxe (cform)
  (:documentation "Convert a theory formal CFORM to a context element."))

(defmethod cform->ctxe ((cform formal-type-decl))
  "Transform type declaration in `(t . TYPE)'"
  (cons (id cform) *type*))

(declaim (ftype (function (cons symbol type-expr) bind-decl) ctxe->bind-decl))
(defun ctxe->bind-decl (e)
  "Convert element E of a context to a `bind-decl'."
  (make!-bind-decl (car e) (cdr e)))

;;; Misc functions

(declaim (ftype (function (type-expr) type-expr) currify))
(defgeneric currify (te)
  (:documentation "Currifies a function type, [a,b -> c] --> [a -> [b -> c]].
Recurses only in function types, that is, the type {x: [a, b -> c] | p} won't be
converted to {x: [a -> [b -> c]] | p}."))

(defmethod currify ((te funtype))
  (labels ((currify* (ts acc)
             "Currifies types TS with range ACC."
             (if (consp ts)
                 (currify* (cdr ts)
                           (make-funtype (currify (car ts)) acc))
                 acc)))
    (with-slots (domain range) te
      (if (subtypep (type-of domain) 'tupletype)
          (currify* (reverse (types domain)) range)
          te))))

(defmethod currify ((te type-name)) te)

(defmethod currify ((te subtype)) te)

(declaim (ftype (function (type-expr) (cons type-expr list)) funtype->types))
(defun funtype->types (ex)
  "Extract types of funtion type EX. For instance, ``[a -> b -> c]'' is
converted to list `(a b c)' (a `list' is returned, that is, ended by `nil')."
  (labels ((f->t (ex)
             (if (funtype? ex)
                 (cons (domain ex) (f->t (range ex)))
                 (list ex))))
    (f->t (currify ex))))

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
(resp.RARG) in body BODY."
  (let ((args `(exprs (argument ,binapp))))
    `(let* ((,larg (car ,args))
            (,rarg (cadr ,args)))
       ,@body)))

(defun print-debug (ind)
  "Prints debug information on standard output with IND an indication (typically
a function name from where the debug is called)."
  (format t "~%~a:" ind)
  (format t "~%  tct:~i~<~a~:>" (list *ctx-thy*))
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

(declaim (ftype (function (stream expr * * (or (cons bind-decl) null)) null)
                pp-abstraction))
(defun pp-abstraction (stream ex &optional colon-p at-sign-p bindings)
  "Print expression EX on stream STREAM abstracting arguments in BINDINGS (with
a λ). Note that the context `*ctx*' is enriched on each printed binding. The
binding is automatically removed from the context thanks to dynamic scoping."
  (labels
      ((print-abstraction (term bindings)
         "Print term TERM abstracting on bindings BINDINGS. Bindings are
typed if they were typed in PVS (they may be typed by a variable declaration)."
         (if (null bindings)
             (format stream ", ~:_~/pvs:pp-dk/" term)
             (with-slots (id type declared-type) (car bindings)
               (if declared-type
                   (let ((*ctx* (acons id declared-type *ctx*)))
                     (format stream "(~/pvs:pp-sym/: ~a ~:/pvs:pp-dk/)" id
                             ;; Use θ to decode TYPE constant
                             (if (equal declared-type *type*) "θ" "η")
                             declared-type)
                     (print-abstraction term (cdr bindings)))
                   (let ((*ctx* (acons id type *ctx*)))
                     (pp-sym stream id)
                     (print-abstraction term (cdr bindings))))))))
    (declare (ftype (function (expr (or (cons bind-decl) null) null))
                    print-abstraction))
    (if (null bindings)
        (pp-dk stream ex colon-p at-sign-p)
        (with-parens (stream colon-p)
          (pprint-logical-block (stream nil)
            (write-string "λ" stream)
            (print-abstraction ex bindings))))))

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
            (format stream "~a (~v/pvs:pp-abstraction/)"
                    quant (list (car bindings)) newex))))))

(declaim (ftype (function (stream type-expr * * symbol) null) pp-prenex))
(defun pp-prenex (stream tex &optional colon-p at-sign-p kind)
  "Print type expression TEX of kind KIND with prenex polymorphism on
`*ctx-thy*'. KIND can be symbol `kind', `set' or `bool'."
  (labels ((ppqu (qu ctx)
             (format stream "~a " qu)
             (with-parens (stream t)
               (format stream "λ~/pvs:pp-sym/, " (caar ctx))
               (ppp (cdr ctx))))
           (ppp (ctx)
             (cond
               ((equal kind 'kind)
                (if (null ctx)
                    (format stream "scheme_k ~:/pvs:pp-dk/" tex)
                    (ppqu "∀K" ctx)))
               ((equal kind 'set)
                (if (null ctx)
                    (format stream "scheme_s ~:/pvs:pp-dk/" tex)
                    (ppqu "∀S" ctx)))
               ((equal kind 'bool)
                (if (null ctx)
                    (pp-dk stream tex colon-p at-sign-p)
                    (ppqu "∀B" ctx))))))
    (with-parens (stream colon-p)
      (ppp *ctx-thy*))))

(declaim (ftype (function (stream string * *) null) pp-reqopen))
(defun pp-reqopen (stream mod &optional colon-p at-sign-p)
  "Prints a require open module MOD directive on stream STREAM."
  (format stream "require open personoj.encodings.~a" mod))

(declaim (ftype (function (stream (cons expr type-expr) * *) null) pp-cast))
(defun pp-cast (stream at &optional colon-p _at-sign-p)
  "Print a casting of `car' of AT to type `cdr' of AT."
  (with-parens (stream colon-p)
    (format stream
            "cast ~:[~;{_} ~]~:/pvs:pp-dk/ _ ~:/pvs:pp-dk/ _"
            *explicit* (cdr at) (car at))))

(declaim (ftype (function (stream var-decl list) null) handle-var-decl))
(defun handle-var-decl (stream vd rest)
  (with-slots (id declared-type) vd
    (let ((*ctx* (acons id declared-type *ctx*)))
      (pp-decls stream rest))))

(declaim (ftype (function (stream (or null (cons declaration list))) null)
                pp-decls))
(defun pp-decls (stream decls)
  "Prints declarations DECLS to stream STREAM. We use a special function (rather
than a `map') because PVS places the declaration of predicates *after* the
declaration of TYPE FROM."
  (when (not (null decls))
    (cond
      ((var-decl? (car decls))
       (handle-var-decl stream (car decls) (cdr decls)))
      ((type-from-decl? (first decls))
       ;; In this case (TYPE FROM declaration), the predicate appears after the
       ;; type declaration
       (assert (>= (length decls) 2))
       (pp-dk stream (second decls))
       (format stream "~%")
       (pp-dk stream (first decls))
       (format stream "~%~%")
       (pp-decls stream (cddr decls)))
      (t (pp-dk stream (car decls))
         (format stream "~%~%")
         (pp-decls stream (cdr decls))))))

;;; Main printing

(declaim (ftype (function (stream syntax * *) null)))
(defgeneric pp-dk (stream obj &optional colon-p at-sign-p)
  (:documentation "Prints object OBJ to stream STREAM. This function can be used
in `format' funcall `~/pvs:pp-dk3/'. The colon modifier specifies whether
arguments should be wrapped into parentheses."))

(defmethod pp-dk (stream (mod module) &optional colon-p at-sign-p)
  "Print the declarations of module MOD."
  (with-slots (id theory formals-sans-usings) mod
    (format stream "// Theory ~a~%" id)
    (let ((*ctx-thy* (mapcar #'cform->ctxe formals-sans-usings)))
      (pp-decls stream theory))))

(defmethod pp-dk (stream (imp importing) &optional colon-p at-sign-p)
  "Prints importing declaration IMP."
  (with-slots (theory-name) imp
    (format stream "require ~a" theory-name)))

;;; Declarations

(defmethod pp-dk (stream (decl type-decl) &optional colon-p at-sign-p)
  "t: TYPE."
  (print "type decl")
  (with-slots (id) decl
    (format stream
            "~<constant symbol ~/pvs:pp-sym/: ~2i~:_ϕ ~v:/pvs:pp-prenex/~:>~%"
            (list id 'kind *type*))
    (setf *signature* (cons id *signature*))
    (format stream "rule μ ~/pvs:pp-sym/ ↪ ~/pvs:pp-sym/~%" id id)
    (format stream "rule π {~/pvs:pp-sym/} ↪ λ_, true" id)))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "t: TYPE = x."
  (print "type-eq-decl")
  (with-slots (id type-expr formals) decl
    (pprint-logical-block (stream nil)
      (format stream "definition ~/pvs:pp-sym/: ϕ ~v:/pvs:pp-prenex/ ≔ "
              id 'kind *type*)
      (pprint-indent :block 2 stream)
      (pprint-newline :fill stream)
      (let* ((formals (alexandria:flatten formals))
             (ctx (mapcar #'ctxe->bind-decl *ctx-thy*))
             (bindings (concatenate 'list ctx formals)))
        (pp-abstraction stream type-expr nil nil bindings)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s"
  (print "type from")
  (with-slots (id type-value) decl
    (pprint-logical-block (stream nil)
      (format stream "definition ~/pvs:pp-sym/: " id)
      (pprint-indent :block 2 stream)
      (pprint-newline :fill stream)
      (format stream "ϕ ~v:/pvs:pp-prenex/ ≔ " 'kind *type*)
      (pprint-newline :fill stream)
      (pp-abstraction stream type-value nil nil
                      (mapcar #'ctxe->bind-decl *ctx-thy*)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl formula-decl) &optional colon-p at-sign-p)
  (print "formula-decl")
  (with-slots (spelling id definition) decl
    (format stream "// Formula declaration: ~a~&" spelling)
    (let*
        ((free-ids (map 'list #'id (freevars definition)))
         (bindings (mapcar
                    #'(lambda (id) (ctxe->bind-decl (assoc id *ctx*)))
                    free-ids))
         ;; Quantify universally on all free variables of ‘definition’
         (defbd (make!-forall-expr bindings definition))
         (axiomp (member spelling '(AXIOM POSTULATE))))
      (pprint-logical-block (stream nil)
        (format stream (if axiomp "symbol" "theorem"))
        (format stream " ~/pvs:pp-sym/: " id)
        (pprint-indent :block 2 stream)
        (pprint-newline :fill stream)
        (format stream "ε ~v:/pvs:pp-prenex/~&" 'bool defbd))
      (setf *signature* (cons id *signature*))
      (unless axiomp
        (format stream "proof~%")
        ;; TODO: export proof
        (format stream "abort~%")))))

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (print "const-decl")
  (with-slots (id declared-type type definition formals) decl
    (format stream "// Constant declaration ~a~%" id)
    (if definition
        (let* ((formals (alexandria:flatten formals))
               (ctx-thy (mapcar #'ctxe->bind-decl *ctx-thy*))
               (bindings (concatenate 'list ctx-thy formals)))
          (pprint-logical-block (stream nil)
            (format stream "definition ~/pvs:pp-sym/: " id)
            (pprint-indent :block 2 stream)
            (pprint-newline :fill stream)
            (format stream "χ ~v:/pvs:pp-prenex/ ≔ " 'set (currify type))
            (pprint-newline :fill stream)
            (pp-abstraction stream definition nil nil bindings)))
        (pprint-logical-block (stream nil)
          (format stream "symbol ~/pvs:pp-sym/: ~:_" id)
          (pprint-indent :block 2 stream)
          (format stream "χ ~v:/pvs:pp-prenex/~&" 'set declared-type)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl def-decl) &optional colon-p at-sign-p)
  (print-debug "def-decl")
  (with-slots (id declared-type definition formals type) decl
    (let ((formals (alexandria:flatten formals))
          (ctx-thy (mapcar #'ctxe->bind-decl *ctx-thy*)))
      (format stream "// Recursive declaration ~a~%" id)
      (pprint-logical-block (stream nil)
        (format stream "symbol ~/pvs:pp-sym/: " id)
        (pprint-indent :block 2 stream)
        (pprint-newline :fill stream)
        (format stream "χ ~v:/pvs:pp-prenex/~&" 'set (currify type)))
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

(defmethod pp-dk :after
    (stream (decl existence-tcc) &optional colon-p at-sign-p)
  ;; Only add a comment after the formula
  (format stream "// ^^ Existence TCC~&"))

(defmethod pp-dk :after
    (stream (decl subtype-tcc) &optional colon-p at-sign-p)
  (format stream "// ^^ Subtype TCC~&"))

;;; Type expressions

(defmethod pp-dk (stream (te tupletype) &optional colon-p at-sign-p)
  ;; REVIEW this function might be obsolete since we currify everything
  "[bool, bool]"
  (print "tupletype")
  (with-slots (types) te
    ;; curryfication of tuple types used as function arguments
    (when colon-p (format stream "("))
    (format stream "~{~:/pvs:pp-dk/~^ ~~> ~}" types)
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (te subtype) &optional colon-p at-sign-p)
  "{n: nat | n /= zero}"
  (print "subtype")
  (with-slots (supertype predicate) te
    (with-parens (stream colon-p)
      (format stream "~<psub {~/pvs:pp-dk/} ~5i~:_~:/pvs:pp-dk/~:>"
              (list supertype predicate)))))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM."
  (print "type app")
  (with-slots (type parameters) te
    (when colon-p (format stream "("))
    (format stream "~<~/pvs:pp-dk/ ~:_~i~{/pvs:pp-dk/~^ ~}~:>"
            (list type parameters))
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (te funtype) &optional colon-p at-sign-p)
  "Prints function type TE to stream STREAM."
  (print "funtype")
  (let ((cte (currify te)))
    (with-slots (domain range) cte
      (when colon-p (format stream "("))
      (format stream "~:/pvs:pp-dk/ ~~> ~:_~/pvs:pp-dk/" domain range)
      (when colon-p (format stream ")")))))
;; TODO: domain dep-binding, possibly a function pp-funtype

;;; Expressions

(defmethod pp-dk (stream (ex name) &optional colon-p at-sign-p)
  "Ensure that NAME is in a context. If NAME is in `*ctx-local*', then prepend
it with a sigil."
  (print-debug "name")
  (with-slots (id mod-id) ex
    (cond
      ((assoc id *ctx*) (pp-sym stream id))
      ((assoc id *ctx-local*) (format stream "$~/pvs:pp-sym/" id))
      ((member id *signature*)
       (with-parens (stream (not (null *ctx-thy*)))
         (pp-sym stream id)
         (when (not (null *ctx-thy*))
           ;; Apply theory arguments to symbols of signature
           (format stream " ~{~/pvs:pp-dk/~^ ~}"
                   ;; Print arguments through ‘pp-dk’ because they might be in
                   ;; ‘ctx-local’
                   (mapcar #'(lambda (st)
                               (make-instance 'name :id (car st)))
                           *ctx-thy*)))))
      ((not (assoc id *dk-sym-map*))
       ;; TODO abstract on arguments of imported theory
       (format stream "~/pvs:pp-sym/.~/pvs:pp-sym/" mod-id id))
      ;; Otherwise, it’s a symbol of the encoding
      (t (pp-sym stream id)))))

(defmethod pp-dk (stream (ex lambda-expr) &optional colon-p at-sign-p)
  "LAMBDA (x: T): t"
  (print "lambda-expr")
  (with-slots (bindings expression) ex
    (when colon-p (format stream "("))
    (pp-abstraction stream expression nil nil bindings)
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (ex exists-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∃"))

(defmethod pp-dk (stream (ex forall-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∀"))

(defmethod pp-dk (stream (ex application) &optional colon-p at-sign-p)
  "f(x)"
  (print-debug "application")
  (format t "~%~a: ~a" (operator* ex) (type (operator* ex)))
  (let ((op (operator* ex))
        (args (alexandria:flatten (arguments* ex))))
    (if (type op)
        (let* ((types (funtype->types (type op)))
               (types (reverse (cdr (reverse types))))
               (args (pairlis args types)))
          (with-parens (stream colon-p)
            (format stream "~/pvs:pp-dk/ ~:_~{~:/pvs:pp-cast/~^ ~:_~}"
                    op args)))
        (with-parens (stream colon-p)
          ;; REVIEW currently, application judgement generate such cases
          (format stream "~/pvs:pp-dk/ ~:_~{~:/pvs:pp-dk/~^ ~:_~}" op args)))))

;; REVIEW in all logical connectors, the generated variables should be added to
;; a context to be available to type expressions.

(defmethod pp-dk (stream (ex branch) &optional colon-p at-sign-p)
  "IF(a,b,c)"
  (print-debug "branch")
  (let* ((args (exprs (argument ex)))
         (prop (first  args))
         (then (second args))
         (else (third  args)))
    (when colon-p (format stream "("))
    (format stream "if ~:/pvs:pp-dk/" prop)
    (format stream " ~:_~i~<(λ~a, ~/pvs:pp-dk/)~:>" (list (fresh-var) then))
    (format stream " ~:_~i~<(λ~a, ~/pvs:pp-dk/)~:>" (list (fresh-var) else))
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (ex disequation) &optional colon-p at-sign-p)
  "/=(A, B)"
  (print "disequation")
  (with-parens (stream colon-p)
    (format stream "neq ~:_~{~:/pvs:pp-dk/~^ ~}" (exprs (argument ex)))))

(defmethod pp-dk (stream (ex infix-disequation) &optional colon-p at-sign-p)
  "a /= b"
  (print "infix-disequation")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ ≠ ~:/pvs:pp-dk/" argl argr))))

(defmethod pp-dk (stream (ex equation) &optional colon-p at-sign-p)
  "=(A, B)"
  (print "equation")
  (with-parens (stream colon-p)
    (format stream "eq ~{~:/pvs:pp-dk/~^ ~}" (exprs (argument ex)))))

(defmethod pp-dk (stream (ex infix-equation) &optional colon-p at-sign-p)
  "a = b"
  (print "infix-equation")
  ;; argument is a tuple-expr
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ = ~:/pvs:pp-dk/" argl argr))))

(defmethod pp-dk (stream (ex conjunction) &optional colon-p at-sign-p)
  "AND(A, B)"
  (print "conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "and ~:/pvs:pp-dk/ (λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex infix-conjunction) &optional colon-p at-sign-p)
  "A AND B"
  (print "infix-conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ ∧ (λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex disjunction) &optional colon-p at-sign-p)
  "OR(A, B)"
  (print "disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "or ~:/pvs:pp-dk/ (λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex infix-disjunction) &optional colon-p at-sign-p)
  "A OR B"
  (print "infix-disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ ∨ (λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex implication) &optional colon-p at-sign-p)
  "IMPLIES(A, B)"
  (print "implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "imp ~:/pvs:pp-dk/ (λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex infix-implication) &optional colon-p at-sign-p)
  "A IMPLIES B"
  (print "infix-implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "~:/pvs:pp-dk/ ⊃ (λ~a, ~/pvs:pp-dk/)"
              argl (fresh-var) argr))))

(defmethod pp-dk (stream (ex negation) &optional colon-p _at-sign-p)
  "NOT(A), there is also a `unary-negation' that represents NOT A."
  (print "negation")
  (with-parens (stream colon-p)
    ;; NOTE we might be able to remove parens (see with LP precedence)
    (format stream "¬ ~:/pvs:pp-dk/" (argument ex))))

;; Not documented, subclass of tuple-expr
(defmethod pp-dk (stream (ex arg-tuple-expr) &optional colon-p at-sign-p)
  "(t, u, v)"
  (print "arg-tuple-expr")
  (with-slots (exprs) ex
    (format stream "~{~:/pvs:pp-dk/~^ ~_~}" exprs)))

(defmethod pp-dk (stream (ex number-expr) &optional colon-p at-sign-p)
  (print "number-expr")
  ;; PVS uses bignum while lambdapi is limited to 2^30 - 1
  (with-parens (stream colon-p)
    (with-slots (type number) ex
      (format stream "cast {_} {~/pvs:pp-dk/} _ ~d _" type number))))
