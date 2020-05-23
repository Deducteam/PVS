(in-package :pvs)
(export '(to-dk3))

(defparameter *use-implicits* nil
  "Set to non-nil to use implicits where it can be.")

(defparameter *dk-sym-map* `((|boolean| . bool) (|type| . ,(intern "{|set|}")))
  "Maps PVS names to names of the encoding.")

(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (with-open-file (stream file :direction :output :if-exists :supersede)
    (let ((*print-pretty* t))
      (format stream "~{~/pvs:pp-reqopen/~&~}"
              '("lhol" "pvs_cert" "subtype" "bool_hol" "builtins" "prenex"
                "unif_rules"))
      (pp-dk stream obj))))

;;; Contexts

(defparameter *ctx* nil "Context enriched by bindings.")

(defgeneric in-ctxp (obj)
  (:documentation "Returns `nil' if object OBJ is not defined in `*ctx*' and
return the definition otherwise."))

(defmethod in-ctxp ((name name-expr))
  (find (id name) *ctx* :key #'id))

(defparameter *ctx-var* nil
  "Successive VAR declarations, as `bind-decl', (n: VAR nat).
They can be used in formula declaration as-is, without explicit quantification,
such as in AXIOM succ(n) /= zero. If a constant declaration quantifies on an
untyped variable, its type is sought among the declared variables.
`bind-decl' has almost the same slots as `var-decl', so we don't lose much
information in the transformation. ")

(defun type-with-vars (sym)
  "Type symbol SYM searching for a binding on symbol SYM in `*ctx-var*', or
return `nil' if SYM is not in `*ctx-var*'."
  (let ((res (find sym *ctx-var* :key #'id)))
    (when res (declared-type res))))

(defparameter *thy-formals* nil
  "Formal parameters of the theory (reversed). Translated to prenex
quantification on elements.")

(defun thy-types ()
  "Returns the type declarations of `*thy-formals*'."
  (remove-if #'(lambda (f) (not (formal-type-decl? f))) *thy-formals*))

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

(defparameter *var-count* 0
  "Number of generated variables. Used to create fresh variable names.")

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
  (format t "~%~a:~%" ind)
  (format t "  for:~i~<~{~a~^,~_ ~}~:>~%" (list *thy-formals*))
  (format t "  ctx:~i~<~{~a~^,~_ ~}~:>~%" (list *ctx*)))

;;; Specialised printing functions

(defgeneric pp-abstract-thy-formals (stream formals &optional colon-p at-sign-p)
  (:documentation "Prints the formals to abstract them, if T: TYPE is a formal
parameter, it prints (T: θ {|set|})."))

(defmethod pp-abstract-thy-formals (stream (decl formal-type-decl)
                                    &optional colon-p at-sign-p)
  (if *use-implicits*
      (format stream "{~/pvs:pp-sym/: θ {|set|}}" (id decl))
      (format stream "(~/pvs:pp-sym/: θ {|set|})" (id decl))))

(defgeneric pp-applied-thy-formals (stream formals &optional colon-p at-sign-p)
  (:documentation "Prints the formals as applied arguments, having the `id' they
are declared with."))

(defmethod pp-applied-thy-formals (stream (decl formal-type-decl)
                                   &optional colon-p at-sign-p)
  (unless *use-implicits*
    (format stream "~/pvs:pp-sym/" (id decl))))

(defgeneric pp-binding (stream binding &optional colon-p at-sign-p)
  (:documentation
   "Prints a typed or untyped binding BINDING to stream STREAM. All bindings are
printed with this function *except* type declaration in theory."))

(defmethod pp-binding :before (stream (bd binding) &optional colon-p at-sign-p)
  "Add `id' of binding BD to `*ctx*', shadowing previous bindings."
  (setf *ctx* (cons bd *ctx*)))

(defmethod pp-binding (stream (bd bind-decl) &optional colon-p at-sign-p)
  "(x: T), `untyped-bind-decl' is rather useless since untyped binder can end up
with the `bind-decl' class."
  (print-debug "bind-decl")
  (with-slots (id declared-type) bd
    (if declared-type
        (format stream "(~/pvs:pp-sym/: η ~:/pvs:pp-dk/)" id declared-type)
        (let ((typ (type-with-vars id)))
          ;; Try to type the binding using ‘*ctx-var*'
          (if typ
              (pp-binding stream
                          (make-instance 'bind-decl :id id :declared-type typ)
                          colon-p at-sign-p)
              (pp-sym stream id))))))

(defun pp-reqopen (stream mod &optional colon-p at-sign-p)
  "Prints a require open module MOD directive on stream STREAM."
  (format stream "require open personoj.encodings.~a" mod))

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

(defgeneric pp-dk (stream obj &optional colon-p at-sign-p)
  (:documentation "Prints object OBJ to stream STREAM. This function can be used
in `format' funcall `~/pvs:pp-dk3/'. The colon modifier specifies whether
arguments should be wrapped into parentheses."))

(defmethod pp-dk (stream (mod module) &optional colon-p at-sign-p)
  "Prints the declarations of module MOD."
  (with-slots (id theory formals-sans-usings) mod
    ;; Add the formals to ‘*thy-formals*’
    (setf *thy-formals* (concatenate 'list *thy-formals* formals-sans-usings))
    (format stream "// Theory ~a~%" id)
    (pp-decls stream theory)))

(defmethod pp-dk :before (stream (decl declaration)
                          &optional _colon-p _at-sign-p)
  (setf *var-count* 0)
  (setf *ctx* *thy-formals*))

(defmethod pp-dk (stream (imp importing) &optional colon-p at-sign-p)
  "Prints importing declaration IMP."
  (with-slots (theory-name) imp
    (format stream "require ~a~%" theory-name)))

(defmethod pp-dk (stream (decl var-decl) &optional colon-p at-sign-p)
  "n: VAR nat, add the declaration to the context in the form of a binding."
  (flet ((bd-of-decl (d)
           "Converts declaration D to a binding declaration."
           (with-slots (declared-type type id) d
             (if declared-type
                 (make-instance 'bind-decl
                                :type (type d)
                                :id (id d)
                                :declared-type (declared-type d))
                 (make-instance 'untyped-bind-decl
                                :type (type d)
                                :id (id d))))))
    (setf *ctx-var* (concatenate 'list *ctx-var* (list (bd-of-decl decl))))))

(defmethod pp-dk (stream (decl type-decl) &optional colon-p at-sign-p)
  "t: TYPE."
  (print "type decl")
  (with-slots (id) decl
    (format stream "constant symbol ~/pvs:pp-sym/: θ {|set|}~%" id)
    (format stream "rule μ ~/pvs:pp-sym/ ↪ ~/pvs:pp-sym/~%" id id)
    (format stream "rule π {~/pvs:pp-sym/} ↪ λ_, true~%" id)))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "t: TYPE = x."
  (print "type-eq-decl")
  (with-slots (id type-expr formals) decl
    (format stream "definition ~/pvs:pp-sym/ " id)
    (format stream "~{~/pvs:pp-abstract-thy-formals/ ~}" *thy-formals*)
    (map nil #'(lambda (fl) (format stream "~{~/pvs:pp-binding/ ~}" fl))
         formals)
    (format stream ": θ {|set|} ≔~%")
    (format stream "  ~i~<~/pvs:pp-dk/~:>~%" (list type-expr))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s"
  (print "type from")
  (with-slots (id type-value) decl
    (format stream "definition ~/pvs:pp-sym/ ≔~%" id)
    (format stream "  ~i~/pvs:pp-dk/~&" type-value)))

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

(defmethod pp-dk (stream (ex name) &optional colon-p at-sign-p)
  "Prints name NAME to stream STREAM."
  (print-debug "name")
  (with-slots (id) ex (format stream "~/pvs:pp-sym/" id)))

(defmethod pp-dk (stream (decl formula-decl) &optional colon-p at-sign-p)
  (print "formula-decl")
  (with-slots (spelling id definition) decl
    (format stream "// Formula declaration: ~a~&" spelling)
    (let*
        ;; Remove from `*ctx-var' variables that are not free in `definition' to
        ;; avoid creating too many abstractions on top of the definition.
        ((free-ids (map 'list #'id (freevars definition)))
         (subctx (remove-if #'(lambda (bd)
                                (not (member (id bd) free-ids)))
                            *ctx-var*))
         ;; Quantify universally on all free variables of `definition'
         (defbd (make-instance 'forall-expr
                               :bindings subctx
                               :expression definition
                               :commas? nil))
         (axiomp (member spelling '(AXIOM POSTULATE))))
      (format stream (if axiomp "symbol" "theorem"))
      (format stream " ~/pvs:pp-sym/:~%" id)
      (format stream "  ~iε ~:<~v/pvs:pp-prenex-bool/~:>~&"
              (list (thy-types) defbd))
      (unless axiomp
        (format stream "proof~%")
        ;; TODO: export proof
        (format stream "admit~%")))))

(defmethod pp-dk :after
    (stream (decl existence-tcc) &optional colon-p at-sign-p)
  ;; Only add a comment after the formula
  (format stream "// ^^ Existence TCC~&"))

(defmethod pp-dk :after
    (stream (decl subtype-tcc) &optional colon-p at-sign-p)
  (format stream "// ^^ Subtype TCC~&"))

(defmethod pp-dk (stream (ex lambda-expr) &optional colon-p at-sign-p)
  "LAMBDA (x: T): t"
  (print "lambda-expr")
  (with-slots (bindings expression) ex
    (when colon-p (format stream "("))
    (format stream "λ~{~/pvs:pp-binding/~},~_ ~<~/pvs:pp-dk/~:@>"
            bindings `(,expression))
    (when colon-p (format stream ")"))))

(defmethod pp-dk (stream (ex exists-expr) &optional colon-p at-sign-p)
  (print "exists-expr")
  (with-slots (bindings expression) ex
    (if (consp bindings)
        ;; Lexical and functional binding of car, because `bindings' seems to be
        ;; a pointer to the attribute
        (let ((binding (car bindings)))
          ;; Here we update the `ex' `exists-expr' removing the first binding,
          ;; print the binding and print the new expression
          (setf (slot-value ex 'bindings) (cdr bindings))
          (when colon-p (format stream "("))
          (format stream "∃ ~<(λ~/pvs:pp-binding/, ~_~/pvs:pp-dk/)~:>"
                  `(,binding ,ex))
          (when colon-p (format stream ")")))
        (pp-dk stream expression colon-p at-sign-p))))

(defmethod pp-dk (stream (ex forall-expr) &optional colon-p at-sign-p)
  "FORALL (x: T): t"
  (print "forall-expr")
  (with-slots (bindings expression) ex
    (if (consp bindings)
        (let ((binding (car bindings)))
          (setf (slot-value ex 'bindings) (cdr bindings))
          (when colon-p (format stream "("))
          (format stream "∀ (~<λ~/pvs:pp-binding/, ~_~/pvs:pp-dk/~:>)"
                  `(,binding ,ex))
          (when colon-p (format stream ")")))
        (pp-dk stream expression colon-p at-sign-p))))

(defmethod pp-dk (stream (ex application) &optional colon-p at-sign-p)
  "f(x)"
  (print-debug "application")
  (let ((op (operator* ex))
        (args (argument* ex)))
    ;; Unpack completely the application, de-tuplifying everything
    (with-parens (stream colon-p)
      (format stream "~/pvs:pp-dk/~_ " op)
      (unless (in-ctxp op)
        ;; If the operator is defined in the signature, it abstracts on the
        ;; arguments of the theory, so we need to apply them
        (format stream "~{~:/pvs:pp-applied-thy-formals/ ~}~_" *thy-formals*))
      (format stream "~{~:/pvs:pp-dk/~^ ~}" args))))

;; TODO in all logical connectors, the generated variables should be added to a
;; context to be available to type expressions.

(defmethod pp-dk (stream (ex branch) &optional colon-p at-sign-p)
  "IF(a,b,c)"
  (let* ((args (exprs (argument ex)))
         (prop (first  args))
         (then (second args))
         (else (third  args)))
    (when colon-p (format stream "("))
    ;; TODO: handle properly branches
    (format stream "if ~:/pvs:pp-dk/ (λ~a, ~/pvs:pp-dk/) (λ~a, ~/pvs:pp-dk/)"
            prop (fresh-var) then (fresh-var) else)
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

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (print "const-decl")
  (with-slots (id declared-type type definition formals) decl
    (format stream "// Constant declaration ~a~%" id)
    (format t "~%Formals: ~a" formals)
    (if definition
        (progn
          (format stream
                  "definition ~/pvs:pp-sym/ ~{~/pvs:pp-abstract-thy-formals/ ~}"
                  id (thy-types))
          ;; It is not clear what `formals' are, type-wise, it's a list of list
          ;; of bind-decl
          (map nil #'(lambda (f)
                       ;; F here is a list of ‘bind-decl'
                       (format stream "~{~/pvs:pp-binding/~^ ~}" f))
               formals)
          (format stream ": η ~/pvs:pp-dk/ ≔~&" declared-type)
          ;; Either we print in a “definition” way and type by the return type,
          ;; or we print in a “functional” way (with λ) and we type by the whole
          ;; type of the expression, using ‘pp-prenex-type’
          (format stream "  ~i~<~/pvs:pp-dk/~:>~&" (list definition)))
        (progn
          (format stream "symbol ~/pvs:pp-sym/:~%" id)
          (format stream "  ~i~<χ ~v:/pvs:pp-prenex-type/~:>~%"
                  (list (thy-types) declared-type))))))

(defun pp-prenex-type (stream obj &optional colon-p at-sign-p types)
  "Prints object OBJ of type `TYPE' with prenex polymorphism on types TYPES."
  (print "pp-prenex-type")
  (when colon-p (format stream "("))
  (if (consp types)
      (let ((tid (id (car types)))
            (rest (cdr types)))
        (format stream
                "∀S (λ~/pvs:pp-sym/: θ {|set|}, ~v/pvs:pp-prenex-type/)"
                tid rest obj))
      (format stream "scheme ~:/pvs:pp-dk/" obj))
  (when colon-p (format stream ")")))

(defun pp-prenex-bool (stream obj &optional colon-p at-sign-p types)
  "Prints object OBJ of type `BOOL' with prenex polymorphism on types TYPES."
  (print "pp-prenex-bool")
  (if (consp types)
      (let ((tid (id (car types)))
            (rest (cdr types)))
        (when colon-p (format stream "("))
        (format stream
                "∀B (λ~/pvs:pp-sym/: θ {|set|}, ~v/pvs:pp-prenex-bool/)"
                tid rest obj)
        (when colon-p (format stream ")")))
      (pp-dk stream obj colon-p at-sign-p)))

(defmethod pp-dk (stream (ex number-expr) &optional colon-p at-sign-p)
  (print "number-expr")
  ;; PVS uses bignum while lambdapi is limited to 2^30 - 1
  (with-parens (stream colon-p)
    (with-slots (type number) ex
      (format stream "cast {_} {~/pvs:pp-dk/} _ ~d _" type number))))

(defmethod pp-dk (stream (decl application-judgement) &optional
                                                        colon-p at-sign-p)
  (print "application-judgement")
  (with-slots (id formals declared-type judgement-type) decl
    (format stream "// Application judgement")
    (format stream "theorem ~/pvs:pp-sym/:~%" id)
    (format stream "  ~iε ~:<~/pvs:pp-dk/~:>~&" judgement-type)
    (format stream "proof~%")
    (format stream "admit~%")))
