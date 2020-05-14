(in-package :pvs)
(export '(to-dk3))

(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (with-open-file (stream file :direction :output :if-exists :supersede)
    (let ((*print-pretty* t))
      (format stream "~{~/pvs:pp-reqopen/~&~}"
              '("lhol" "pvs_cert" "subtype" "bool_hol" "builtins"))
      (pp-dk stream obj))))

(defparameter *ctx-var* nil
  "Successive VAR declarations (n: VAR nat).")

(defun pp-sym (stream sym &optional colon-p at-sign-p)
  "Prints symbol SYM to stream STREAM, enclosing it in braces {||} if
necessary."
  (flet ((sane-charp (c)
           (cond
             ((alphanumericp c) t)
             ((char= c #\_) t)
             (t nil))))
    (if (every #'sane-charp (string sym))
        (format stream "~(~a~)" sym)
        (format stream "{|~(~a~)|}" sym))))

(defun pp-reqopen (stream mod &optional colon-p at-sign-p)
  "Prints a require open module MOD directive on stream STREAM."
  (format stream "require open personoj.encodings.~a" mod))

(defgeneric pp-dk (stream obj &optional colon-p at-sign-p)
  (:documentation "Prints object OBJ to stream STREAM. This function can be used
in `format' funcall `~/pvs:pp-dk3/'."))

(defmethod pp-dk (stream (mod module) &optional colon-p at-sign-p)
  "Prints the name of the module MOD as a comment."
  (with-slots (id theory) mod
    (format stream "// Theory ~a~%" id)
    (format stream "~{~/pvs:pp-dk/~^~_~}" theory)))

(defmethod pp-dk (stream (imp importing) &optional colon-p at-sign-p)
  "Prints importing declaration IMP."
  (with-slots (theory-name) imp
    (format stream "require ~a~%" theory-name)))

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
  (with-slots (id type-expr) decl
    (format stream "definition ~/pvs:pp-sym/: θ {|set|} ≔~_" id)
    (format stream "~i~<~/pvs:pp-dk/~:>~%" `(,type-expr))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s."
  (print "type from")
  (with-slots (id predicate supertype) decl
    (format stream "definition ~/pvs:pp-sym/ ≔~_ " id)
    (format stream "~i~<psub {~/pvs:pp-dk/} ~/pvs:pp-dk/~:>~%"
            `(,supertype ,predicate))))

(defmethod pp-dk :around (stream (te type-expr) &optional colon-p at-sign-p)
  (print "type expr")
  (with-slots (parens print-type free-variables free-parameters) te
    (if print-type
        (call-next-method)
        ;; (format stream "~/pvs:pp-dk/" print-type)
        (progn
          (dotimes (p parens)
            (format stream "("))
          (call-next-method)
          (dotimes (p parens)
            (format stream ")"))))))

(defmethod pp-dk (stream (te tupletype) &optional colon-p at-sign-p)
  "[bool, bool]"
  (with-slots (types) te
    ;; curryfication of tuple types used as function arguments
    (format stream "~{(~/pvs:pp-dk/)~^ ~~> ~}" types)))

(defmethod pp-dk (stream (te subtype) &optional colon-p at-sign-p)
  "{n: nat | n /= zero}"
  (print "subtype")
  (with-slots (supertype predicate) te
    (format stream "psub {~/pvs:pp-dk/} (~/pvs:pp-dk/)" supertype predicate)))

;; exists-type < quant-type < type-expr
(defmethod pp-dk (stream (te exists-type) &optional colon-p at-sign-p)
  (print "exists type")
  (format stream "∃"))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM."
  (print "type app")
  (with-slots (type parameters) te
    (format stream "~:<~/pvs:pp-dk/ ~{/pvs:pp-dk/~^ ~}~:>"
            `(,type ,parameters))))

(defmethod pp-dk (stream (te funtype) &optional colon-p at-sign-p)
  "Prints function type TE to stream STREAM."
  (with-slots (domain range) te
    (format stream "~/pvs:pp-dk/ ~~> ~/pvs:pp-dk/" domain range)))
;; TODO: domain dep-binding, possibly a function pp-funtype

(defmethod pp-dk (stream (ex name) &optional colon-p at-sign-p)
  "Prints name NAME to stream STREAM."
  (print "name")
  (with-slots (id) ex (format stream "~/pvs:pp-sym/" id)))

(defmethod pp-dk (stream (decl formula-decl) &optional colon-p at-sign-p)
  "Prints formula declaration DECL to stream STREAM."
  (print "formula-decl")
  (with-slots (spelling id definition) decl
    (format stream "// Formula declaration: ~a~&" spelling)
    (cond ((member spelling '(AXIOM POSTULATE))
           (format stream "symbol ~/pvs:pp-sym/: ~_ε ~:<~/pvs:pp-dk/~:>~&"
                   id `(,definition)))
          ((member spelling '(OBLIGATION LEMMA THEOREM))
           (format stream "theorem ~/pvs:pp-sym/: ~_ε ~:<~/pvs:pp-dk/~:>~&"
                   id `(,definition))
           (format stream "proof~&")
           ;; TODO: export proof
           (format stream "admit~&"))
          (t (error "pp-dk-formula-decl: unknown spelling")))))

(defgeneric pp-binding (stream binding &optional colon-p at-sign-p)
  (:documentation
   "Prints a typed or untyped binding BINDING to stream STREAM."))

(defmethod pp-binding (stream (bd bind-decl) &optional colon-p at-sign-p)
  "(x: T)"
  (print "bind-decl")
  (if (declared-type bd)
      ;; TODO: add a 'wrap' argument to put parentheses around type only if
      ;; needed
      (format stream "(~/pvs:pp-sym/: η ~:<~/pvs:pp-dk/~:>)"
              (id bd) (list (declared-type bd)))
      (format stream "~/pvs:pp-sym/" (id bd))))

(defmethod pp-dk (stream (ex lambda-expr) &optional colon-p at-sign-p)
  "LAMBDA (x: T): t"
  (print "lambda-expr")
  (with-slots (bindings expression) ex
    (format stream "λ~{~/pvs:pp-binding/~},~_ ~<~/pvs:pp-dk/~:@>"
            bindings `(,expression))))

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
          (format stream "∃ ~:<λ~/pvs:pp-binding/, ~_~/pvs:pp-dk/~:>"
                  `(,binding ,ex)))
        (format stream "~/pvs:pp-dk/" expression))))

(defmethod pp-dk (stream (ex forall-expr) &optional colon-p at-sign-p)
  "FORALL (x: T): t"
  (print "forall-expr")
  (with-slots (bindings expression) ex
    (if (consp bindings)
        (let ((binding (car bindings)))
          (setf (slot-value ex 'bindings) (cdr bindings))
          (format stream "∀ ~:<λ~/pvs:pp-binding/, ~_~/pvs:pp-dk/~:>"
                  `(,binding ,ex)))
        (format stream "~/pvs:pp-dk/" expression))))

(defmethod pp-dk (stream (ex application) &optional colon-p at-sign-p)
  "f(x)"
  (print "application")
  (with-slots (operator argument) ex
    (format stream "(~/pvs:pp-dk/)~_ (~/pvs:pp-dk/)" operator argument)))

(defmethod pp-dk (stream (ex disequation) &optional colon-p at-sign-p)
  "a /= b, there is also an infix-disequation class"
  (print "disequation")
  (with-slots (operator argument) ex
    (format stream "neq ~/pvs:pp-dk/" argument)))

;; Not documented, subclass of tuple-expr
(defmethod pp-dk (stream (ex arg-tuple-expr) &optional colon-p at-sign-p)
  "(t, u, v)"
  (print "arg-tuple-expr")
  (with-slots (exprs) ex
    (format stream "~{(~/pvs:pp-dk/)~^ ~_~}" exprs)))

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (print "const-decl")
  (with-slots (id declared-type type definition) decl
    (format stream "// Constant declaration ~a~%" id)
    (if definition
        (format stream "definition ~/pvs:pp-dk/ ≔~_ ~i~<~/pvs:pp-dk/~:>~%"
                declared-type `(,definition))
        (format stream "symbol ~/pvs:pp-sym/: η ~:<~/pvs:pp-dk/~:>~%"
                id (list type)))))
