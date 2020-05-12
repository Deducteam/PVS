(in-package :pvs)
(export '(to-dk3))

(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (with-open-file (stream file :direction :output :if-exists :supersede)
    (let ((*print-pretty* t))
      (pp-dk stream obj))))

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
  "Prints an uninterpreted type declaration DECL,
t: TYPE."
  (with-slots (id) decl
    (format stream "constant symbol ~a: θ {|set|}~%" id)
    (format stream "rule μ ~a ↪ ~a~%" id id)
    (format stream "rule π ~a ↪ λ_, true~%" id)))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "Prints a interpreted type declaration DECL,
t: TYPE = x."
  (with-slots (id type-expr) decl
    (format stream "definition ~a: θ {|set|} ≔~_" id)
    (format stream "~i~<~/pvs:pp-dk/~:>~&" type-expr)))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "Prints a sub-type declaration DECL on stream STREAM, t: TYPE FROM s."
  (with-slots (id predicate supertype) decl
    (format stream "definition ~a ≔~&" id)
    (format stream "~i~<psub {~/pvs:pp-dk/} ~/pvs:pp-dk/~:>~&"
            supertype predicate))) ; Type of predicate?

(defmethod pp-dk :around (stream (te type-expr) &optional colon-p at-sign-p)
  (with-slots (parens print-type free-variables free-parameters) te
    (if print-type
        (pp-dk stream print-type)
        (progn
          (dotimes (p parens)
            (format stream "("))
          (call-next-method)
          (dotimes (p parens)
            (format stream ")"))))))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM."
  (with-slots (type parameters) te
    (format stream "~<(~/pvs:pp-dk/ ~{/pvs:pp-dk/~^ ~})~:>" type parameters)))

(defmethod pp-dk (stream (te subtype) &optional colon-p at-sign-p)
  (with-slots (supertype predicate) te
    ;; TODO: can be factorised with `type-from-decl'
    nil))

(defmethod pp-dk (stream (te funtype) &optional colon-p at-sign-p)
  "Prints function type TE to stream STREAM."
  (with-slots (domain range) te
    (format stream "(~/pvs:pp-dk/ ~> /pvs:pp-dk/)" domain range)))
;; TODO: domain dep-binding, possibly a function pp-funtype

(defmethod pp-dk (stream (ex name) &optional colon-p at-sign-p)
  "Prints name NAME to stream STREAM."
  (with-slots (id) ex
    (format stream "~a" id)))
