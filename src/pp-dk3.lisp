(in-package :pvs)
(require "alexandria")
(export '(to-dk3))

(defparameter *use-implicits* nil
  "Set to non-nil to use implicits where it can be.")

(declaim (type (cons (cons symbol symbol) list) *dk-sym-map*))
(defparameter *dk-sym-map* `((|boolean| . bool) (|type| . ,(intern "{|set|}")))
  "Maps PVS names to names of the encoding.")

(declaim (ftype (function (syntax string) *) to-dk3))
(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (with-open-file (stream file :direction :output :if-exists :supersede)
    (let ((*print-pretty* t))
      (format stream "~{~/pvs:pp-reqopen/~&~}"
              '("lhol" "pvs_cert" "subtype" "bool_hol" "builtins" "prenex"
                "unif_rules"))
      (pp-dk stream obj))))

(defparameter *type* (make-instance 'type-name :id '|type|))

;;; Contexts

(declaim (type (or null (cons symbol)) *signature*))
(defparameter *signature* nil
  "Symbols defined in the theory.")

(deftype context ()
  "A context is an association list mapping symbols to types."
  '(or (cons (cons symbol type-expr) list) null))

(declaim (type context *ctx*))
(defparameter *ctx* nil
  "Context enriched by bindings. Most recent binding on top.")

(declaim (type context *ctx-var*))
(defparameter *ctx-var* nil
  "Successive VAR declarations, as `bind-decl', (n: VAR nat).
They can be used in formula declaration as-is, without explicit quantification,
such as in AXIOM succ(n) /= zero. If a constant declaration quantifies on an
untyped variable, its type is sought among the declared variables.
`bind-decl' has almost the same slots as `var-decl', so we don't lose much
information in the transformation. ")

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

(defun ctxe->bind-decl (e)
  "Convert element E of a context to a `bind-decl'."
  (make-instance 'bind-decl :id (car e) :declared-type (cdr e)))

;;; Misc functions

(declaim (ftype (function (type-expr) type-expr) currify))
(defgeneric currify (te)
  (:documentation "Currifies a function type, [a,b -> c] --> [a -> [b -> c]]"))

(defmethod currify ((te funtype))
  (labels ((currify* (ts acc)
             "Currifies types TS with range ACC."
             (if (consp ts)
                 (currify* (cdr ts) (make-instance 'funtype
                                                   :domain (car ts)
                                                   :range acc))
                 ;; Recursive curryfication of `(car ts)' is handled by
                 ;; pp-dk
                 acc)))
    (with-slots (domain range) te
      (if (subtypep (type-of domain) 'tupletype)
          (currify* (reverse (types domain)) range)
          te))))

(declaim (ftype (function (typed-declaration) type-expr) type-of-decl))
(defun type-of-decl (decl)
  "Provide the type of the symbol declared in DECL."
  (labels
      ((typ (arg)
         "Return type of ARG: its `declared-type', or its type from `*ctx-var*'
or its `type'."
         (let* ((dtyp (declared-type arg))
                (vdef (assoc (id arg) *ctx-var*)))
           (cond
             (dtyp dtyp)
             (vdef (cdr vdef))
             (t (type decl)))))
       (f (args acc)
         "Takes type `t' of `car' of ARGS and builds ``t ~> acc''"
         (if (null args) acc
             (make-instance 'funtype
                            :domain (typ (car args))
                            :range acc))))
    (f (reverse (alexandria:flatten (formals decl)))
       (declared-type decl))))

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
  (format t "~%  tct:~i~<~{~a~^,~_ ~}~:>" (list *ctx-thy*))
  (format t "~%  ctx:~i~<~{~a~^,~_ ~}~:>" (list *ctx*))
  (format t "~%  lct:~i~<~{~a~^,~_ ~}~:>" (list *ctx-local*)))

;;; Specialised printing functions

(declaim (ftype (function (stream bind-decl * *) null) pp-binding))
(defun pp-binding (stream bd &optional colon-p at-sign-p)
  "Print binding BD and add the variable to `*ctx*'."
  (with-slots (id type declared-type) bd
    (if declared-type
        (progn
          ;; If binding is (explicitly) typed, add the typed binding to context
          (setf *ctx* (acons id declared-type *ctx*))
          (format stream "(~/pvs:pp-sym/: ~a ~:/pvs:pp-dk/)"
                  id
                  ;; Use θ to decode the TYPE constant
                  (if (equal declared-type *type*) "θ" "η")
                  declared-type))
        (let ((vartype (cdr (assoc id *ctx-var*))))
          (if vartype
              (format stream "(~/pvs:pp-sym/: η ~:/pvs:pp-dk/)"
                      id vartype)
              (progn
                (setf *ctx* (acons id type *ctx*))
                (format stream "~/pvs:pp-sym/" id)))))))

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
            (format stream "~a ~<(λ~/pvs:pp-binding/, ~_~/pvs:pp-dk/)~:>"
                    quant (list (car bindings) newex)))))))

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

(declaim (ftype (function (stream symbol * *) null) pp-sym))
(defun pp-sym (stream sym &optional colon-p at-sign-p)
  "Prints symbol SYM to stream STREAM, enclosing it in braces {||} if
necessary."
  (assert (symbolp sym))
  (flet ((sane-charp (c)
           (cond
             ((alphanumericp c) t)
             ((char= c #\_) t)
             (t nil))))
    (let ((dk-sym (assoc sym *dk-sym-map*)))
      (cond (dk-sym (format stream "~(~a~)" (cdr dk-sym)))
            ((every #'sane-charp (string sym)) (format stream "~(~a~)" sym))
            (t (format stream "{|~(~a~)|}" sym))))))

(declaim (ftype (function (stream (cons declaration list)) null) pp-decls))
(defun pp-decls (stream decls)
  "Prints declarations DECLS to stream STREAM. We use a special function (rather
than a `map') because PVS places the declaration of predicates *after* the
declaration of TYPE FROM."
  (if (>= (length decls) 2)
      (let ((decl-1 (first decls))
            (decl-2 (second decls)))
        (if (subtypep (type-of decl-1) 'type-from-decl)
            ;; If the first declaration is a TYPE FROM declaration,
            ;; print the generated predicate first
            (progn
              (format stream "~/pvs:pp-dk/~&" decl-2)
              (format stream "~/pvs:pp-dk/~&" decl-1)
              (pp-decls stream (cddr decls)))
            (progn
              (format stream "~/pvs:pp-dk/~&" decl-1)
              (pp-decls stream (cdr decls)))))
      (format stream "~{~/pvs:pp-dk/~^~&~}" decls)))

;;; Main printing

(declaim (ftype (function (stream syntax * *) null)))
(defgeneric pp-dk (stream obj &optional colon-p at-sign-p)
  (:documentation "Prints object OBJ to stream STREAM. This function can be used
in `format' funcall `~/pvs:pp-dk3/'. The colon modifier specifies whether
arguments should be wrapped into parentheses."))

(defmethod pp-dk (stream (mod module) &optional colon-p at-sign-p)
  "Prints the declarations of module MOD."
  (with-slots (id theory formals-sans-usings) mod
    (format stream "// Theory ~a~%" id)
    (let ((*ctx-thy* (mapcar #'cform->ctxe formals-sans-usings)))
      (pp-decls stream theory))))

(defmethod pp-dk :around (stream (decl declaration)
                          &optional _colon-p _at-sign-p)
  (let ((*ctx* nil)
        (*var-count* 0))
    (call-next-method)))

(defmethod pp-dk (stream (imp importing) &optional colon-p at-sign-p)
  "Prints importing declaration IMP."
  (with-slots (theory-name) imp
    (format stream "require ~a~%" theory-name)))

;;; Declarations

(defmethod pp-dk (stream (decl var-decl) &optional colon-p at-sign-p)
  "n: VAR nat, add the declaration to `*ctx-var*' in the form of a binding."
  (flet ((bd-of-decl (d)
           "Converts declaration D to a binding declaration."
           (make-instance 'bind-decl
                          ;; REVIEW assign module?
                          :type (type d)
                          :id (id d)
                          :declared-type (declared-type d))))
    (setf *ctx-var*
          (concatenate 'list *ctx-var*
                       (list (cons (id decl) (declared-type decl)))))))

(defmethod pp-dk (stream (decl type-decl) &optional colon-p at-sign-p)
  "t: TYPE."
  (print "type decl")
  (with-slots (id) decl
    (format stream "constant symbol ~/pvs:pp-sym/: ϕ ~v:/pvs:pp-prenex/~%"
            id 'kind *type*)
    (setf *signature* (cons id *signature*))
    (format stream "rule μ ~/pvs:pp-sym/ ↪ ~/pvs:pp-sym/~%" id id)
    (format stream "rule π {~/pvs:pp-sym/} ↪ λ_, true~%" id)))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "t: TYPE = x."
  (print "type-eq-decl")
  (with-slots (id type-expr formals) decl
    (format stream "definition ~/pvs:pp-sym/: ϕ ~v:/pvs:pp-prenex/ ≔~%"
            id 'kind *type*)
    (let ((formals (alexandria:flatten formals))
          (ctx (mapcar #'ctxe->bind-decl *ctx-thy*)))
      (format stream
              "  ~i~<λ~{~/pvs:pp-binding/~^ ~}, ~/pvs:pp-dk/~:>~%"
              (list (concatenate 'list ctx formals) type-expr)))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s"
  (print "type from")
  (with-slots (id type-value) decl
    (format stream "definition ~/pvs:pp-sym/: ϕ ~v:/pvs:pp-prenex/ ≔~%"
            id 'kind *type*)
    (format stream "  ~i~<λ~{~/pvs:pp-binding/~^ ~}~:>, ~/pvs:pp-dk/~&"
            (list (mapcar #'ctxe->bind-decl *ctx-thy*))
            type-value)
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl formula-decl) &optional colon-p at-sign-p)
  (print "formula-decl")
  (with-slots (spelling id definition) decl
    (format stream "// Formula declaration: ~a~&" spelling)
    (let*
        ;; Remove from `*ctx-var' variables that are not free in `definition' to
        ;; avoid creating too many abstractions on top of the definition.
        ((free-ids (map 'list #'id (freevars definition)))
         (subctx (remove-if #'(lambda (id-type)
                                (not (member (car id-type) free-ids)))
                            *ctx-var*))
         (bindings (mapcar #'ctxe->bind-decl subctx))
         ;; Quantify universally on all free variables of `definition'
         (defbd (make-instance 'forall-expr
                               :bindings bindings
                               :expression definition))
         (axiomp (member spelling '(AXIOM POSTULATE))))
      (format stream (if axiomp "symbol" "theorem"))
      (format stream " ~/pvs:pp-sym/:~%" id)
      (format stream "  ~iε ~<~v:/pvs:pp-prenex/~:>~&" (list 'bool defbd))
      (setf *signature* (cons id *signature*))
      (unless axiomp
        (format stream "proof~%")
        ;; TODO: export proof
        (format stream "admit~%")))))

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (print "const-decl")
  (with-slots (id declared-type type definition formals) decl
    (format stream "// Constant declaration ~a~%" id)
    (if definition
        (let ((typ (type-of-decl decl))
              (formals (alexandria:flatten formals))
              (ctx-thy (mapcar #'ctxe->bind-decl *ctx-thy*)))
          (format stream "definition ~/pvs:pp-sym/: " id)
          (format stream "χ ~<~v:/pvs:pp-prenex/~:> ≔~&" (list 'set typ))
          (format stream "  ~iλ~<~{~:/pvs:pp-binding/~^ ~}~:>,"
                  (list (concatenate 'list ctx-thy formals)))
          (format stream "~<~/pvs:pp-dk/~:>" (list definition)))
        (progn
          (format stream "symbol ~/pvs:pp-sym/:~%" id)
          (format stream "  ~i~<χ ~v:/pvs:pp-prenex/~:>~%"
                  (list 'set declared-type))))
    (setf *signature* (cons id *signature*))))

(defmethod pp-dk (stream (decl def-decl) &optional colon-p at-sign-p)
  (print-debug "def-decl")
  (with-slots (id declared-type definition formals) decl
    (let ((formals (alexandria:flatten formals)))
      (format stream "// Recursive declaration ~a~%" id)
      (format stream "symbol ~/pvs:pp-sym/ " id)
      (format stream "~{~:/pvs:pp-binding/~^ ~}" formals)
      (format stream ": η ~:/pvs:pp-dk/~&" declared-type)
      (setf *signature* (cons id *signature*))
      (format stream "rule ~:/pvs:pp-sym/ ~{$~/pvs:pp-sym/ ~}~_ ↪ "
              id (mapcar #'id formals))
      (let ((*ctx-local* (ctx-of-bindings formals))
            (*ctx* nil))
        (pprint-logical-block (stream nil)
          (pp-dk stream definition colon-p at-sign-p))))))

;; TODO
(defmethod pp-dk (stream (decl application-judgement)
                  &optional colon-p at-sign-p)
  "Print the judgement. A TCC is generated with the same `id'.
See parse.lisp:826"
  (print "application-judgement")
  (with-slots (id formals declared-type judgement-type name) decl
    (format stream "// Application judgement~%")
    (let* ((args (alexandria:flatten formals))
           (term (make-instance 'application
                                :operator name
                                :argument args)))
      (format stream "// @cast _ ~:/pvs:pp-dk/ _ ~:/pvs:pp-dk/ P :-~&"
              declared-type term)
      (let* ((hd (make-instance 'name-expr :id id))
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
      (format stream "psub {~/pvs:pp-dk/} ~:/pvs:pp-dk/"
              supertype predicate))))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM."
  (print "type app")
  (with-slots (type parameters) te
    (when colon-p (format stream "("))
    (format stream "~<~/pvs:pp-dk/ ~{/pvs:pp-dk/~^ ~}~:>" `(,type ,parameters))
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (te funtype) &optional colon-p at-sign-p)
  "Prints function type TE to stream STREAM."
  (print "funtype")
  (let ((cte (currify te)))
    (with-slots (domain range) cte
      (when colon-p (format stream "("))
      (format stream "~:/pvs:pp-dk/ ~~> ~/pvs:pp-dk/" domain range)
      (when colon-p (format stream ")")))))
;; TODO: domain dep-binding, possibly a function pp-funtype

;;; Expressions

(defmethod pp-dk (stream (ex lambda-expr) &optional colon-p at-sign-p)
  "LAMBDA (x: T): t"
  (print "lambda-expr")
  (with-slots (bindings expression) ex
    (when colon-p (format stream "("))
    (format stream "λ~{~/pvs:pp-binding/~},~_ ~<~/pvs:pp-dk/~:@>"
            bindings `(,expression))
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (ex exists-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∃"))

(defmethod pp-dk (stream (ex forall-expr) &optional colon-p at-sign-p)
  (pp-quantifier stream ex colon-p at-sign-p "∀"))

(defmethod pp-dk (stream (ex name) &optional colon-p at-sign-p)
  "Ensure that NAME is in a context. If NAME is in `*ctx-local*', then prepend
it with a sigil."
  (print-debug "name")
  (with-slots (id) ex
    (cond
      ((assoc id *ctx*) (format stream "~/pvs:pp-sym/" id))
      ((assoc id *ctx-local*) (format stream "$~/pvs:pp-sym/" id))
      ((member id *signature*)
       (with-parens (stream (>= (length *ctx-thy*) 1))
         ;; Apply theory arguments to symbols of signature
         (format stream "~/pvs:pp-sym/ ~{~a~^ ~}"
                 id (mapcar #'car *ctx-thy*))))
      ;; Otherwise, it’s a symbol of the encoding
      (t (format stream "~/pvs:pp-sym/" id)))))

(declaim (ftype (function (expr) *) pp-cast))
(defun pp-cast (stream expr &optional colon-p _at-sign-p)
  "Print expression EXPR preceding it by a cast ``cast''."
  (with-parens (stream colon-p)
    (format stream "@cast _ _ _ ~:/pvs:pp-dk/ _" expr)))

(defmethod pp-dk (stream (ex application) &optional colon-p at-sign-p)
  "f(x)"
  (print-debug "application")
  (let
      ;; Unpack completely the application, de-tuplifying everything
      ((op (operator* ex))
       (args (alexandria:flatten (arguments* ex))))
    (with-parens (stream colon-p)
      (format stream "~/pvs:pp-dk/~_ " op)
      (format stream "~{~:/pvs:pp-cast/~^ ~}" args))))

;; REVIEW in all logical connectors, the generated variables should be added to
;; a context to be available to type expressions.

(defmethod pp-dk (stream (ex branch) &optional colon-p at-sign-p)
  "IF(a,b,c)"
  (let* ((args (exprs (argument ex)))
         (prop (first  args))
         (then (second args))
         (else (third  args)))
    (when colon-p (format stream "("))
    ;; TODO: handle properly branches
    (format stream "if ~:/pvs:pp-dk/" prop)
    (format stream " ~_~i~<(λ~a, ~/pvs:pp-dk/)~:>" (list (fresh-var) then))
    (format stream " ~_~i~<(λ~a, ~/pvs:pp-dk/)~:>" (list (fresh-var) else))
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (ex disequation) &optional colon-p at-sign-p)
  "/=(A, B)"
  (print "disequation")
  (with-parens (stream colon-p)
    (format stream "neq ~{~:/pvs:pp-dk/~^ ~}" (exprs (argument ex)))))

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
