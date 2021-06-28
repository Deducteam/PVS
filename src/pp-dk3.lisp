;;; Export to Dedukti.
;;; This module provides the function ‘to-dk3’ which exports a PVS theory to a
;;; Dedukti3 file.
;;; TODO recursive functions
;;; TODO assuming sections
;;; TODO dependent pairs
;;; TODO dependent products
;;; TODO records

(in-package :pvs)
(export '(to-dk3))

;;; Global parameters

(defparameter *print-domains* t
  "Whether to systematically print domain of abstractions.")

(defparameter *print-implicits* t
  "Whether to systematically print implicit arguments.")

(declaim (type (cons (cons symbol string) list) *dk-sym-map*))
(defparameter *dk-sym-map*
  '((|boolean| . "prop") (|bool| . "prop") (true . "true") (false . "false")
    (|type| . "Set" ))
  "Maps PVS names to names of the encoding. It is also used to avoid prepending
the symbols with a module id.")

(declaim (type type-name *type*))
(defparameter *type* (mk-type-name '|type|)
  "Symbol that represents TYPE in PVS which is translated as Set.")

(declaim (ftype (function (type-expr) boolean) is-*type*-p))
(defun is-*type*-p (tex)
  "Return true if TEX is the constant TYPE"
  (equal tex *type*))

;;; Signature handling

(defparameter *workdir* nil "Directory where signatures are saved and read.")

(declaim (type dksig:signature *signature*))
(defparameter *signature* (dksig:make-signature :theory 'dummy)
  "Signature of the currently exported theory.")

(defparameter *opened-signatures* nil
  "Signatures that are opened into the current one.")

(defun set-workdir (path)
  "Set PATH as the working directory (see `*workdir*')"
  (assert
   (uiop:directory-pathname-p path) (path)
   "Working directory must be a dirctory: ~a is not a directory." path)
  (when *workdir* (error "Working directory already set: ~a" *workdir*))
  (setf *workdir* path))

(defun dump-sig ()
  "Write the signature of the current theory to filename `theory.pvsig'."
  (let* ((filename (string (dksig:signature-theory *signature*)))
         (path (pvs::merge-pathnames
                *workdir* (make-pathname :name filename :type "pvsig"))))
    (with-open-file (s path :direction :output :if-exists :supersede
                            :if-does-not-exist :create)
      (dksig:dump *signature* s))))

(defun open-sig (theory)
  "Import the defined symbols of THEORY into the current one."
  (let*
      ((filename (string theory))
       (path (pvs::merge-pathnames
              *workdir* (make-pathname :name filename :type "pvsig")))
       (content
         (with-open-file (s path :direction :input)
           (loop for line = (read-line s nil) while line collect line)))
       (content (format nil "~{~a~^~%~}" content))
       (newsig (dksig:open theory content)))
    (setf *opened-signatures* (cons newsig *opened-signatures*))))

(defmacro with-sig-update ((bind id ty sig) &body body)
  "Bind BIND with the symbol name for ID which denotes a symbol of type TY that
will be added into signature SIG at the end of BODY"
  (let ((newsig (gensym)))
    `(multiple-value-bind (,bind ,newsig) (dksig:add ,id ,ty ,sig)
       ,@body
       (setf sig ,newsig))))

(deftype polylist (ty)
  `(or (cons ,ty list) null))

(defpackage dklog
  (:documentation "Some logging facilities.")
  (:use :cl)
  (:export :top :expr :type :decl :contexts)
  (:shadow :expr :type :decl :contexts))

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

(defun top (format-str &rest args)
  (apply #'dk-log nil format-str args))
(defun decl (format-str &rest args)
  (apply #'dk-log "decl" format-str args))
(defun expr (format-str &rest args)
  (apply #'dk-log "expr" format-str args))
(defun type (format-str &rest args)
  (apply #'dk-log "type" format-str args))

(in-package :pvs)

(declaim (ftype (function (syntax string) *) to-dk3))
(defun to-dk3 (obj file)
  "Export PVS object OBJ to Dedukti file FILE using Dedukti3 syntax."
  (dklog:top "Translating ~s" file)
  (let ((path (uiop:parse-unix-namestring file :want-absolute t))
        (*print-pretty* nil)            ;slows down printing when t
        (*print-right-margin* 78))
    (set-workdir (uiop:pathname-directory-pathname path))
    (with-open-file (stream file :direction :output :if-exists :supersede)
      (write-string "require open personoj.lhol personoj.tuple personoj.sum
personoj.logical personoj.pvs_cert personoj.eqtup;
require open personoj.nat personoj.coercions;" stream)
      (fresh-line stream)
      (pp-dk stream obj))))

;;; Contexts
;;;
;;; Contexts are  global variables that are  filled during the export.  They are
;;; filled  using  dynamic  scoping  (that  is  with  (let  ((*ctx*  ...))  ...)
;;; constructs) so that the variables  introduced are automatically removed when
;;; we  escape   their  lexical  scope   in  the  PVS  specification   (and  the
;;; translation). Contexts are always reversed  wrt their definition, that is, a
;;; PVS context [x: nat, y: reals, z: nznat] is represented as ((z . nznat) (y .
;;; reals) (x . nat)), the most recent binding is on top (stack structure).

(defun context-p (thing)
  "A context is a list of cons cells, each cons cell contains a symbol and a
type-expr."
  (flet ((ctx-binding-p (b)
           (and (consp b) (symbolp (car b)) (type-expr? (cdr b)))))
    (and (listp thing) (every #'ctx-binding-p thing))))

(deftype context ()
  "A context is an association list mapping symbols to types."
  '(satisfies context-p))

(declaim (type context *ctx*))
(defparameter *ctx* nil
  "Context enriched by bound arguments, theory formals and `var-decl'. Variable
declarations `var-decl' are never removed from the context.")

(declaim (type context *ctx-var*))
(defparameter *ctx-var* nil
  "Context enriched by `var-decl' only. Not typed bound variables of LAMBDAs
seek their type into this context only (and not previous LAMBDA bindings).")

(defmacro with-extended-context ((bd ctx) &body body)
  "Expand to BODY but extending context CTX with binding BD before"
  `(with-slots (id declared-type) ,bd
     (let ((,ctx (if declared-type (acons id declared-type ,ctx) ,ctx)))
       ,@body)))

(defun thy-binding-p (thing)
  (and (bind-decl? thing) (symbolp (id thing)) (declared-type thing)))
(defun thy-bindings-p (thing)
  (and (listp thing) (every #'thy-binding-p thing)))
(deftype thy-bindings ()
  '(satisfies thy-bindings-p))

(declaim (type thy-bindings *thy-bindings*))
(defparameter *thy-bindings* nil
  "Bindings of the theory. This list is not updated using dynamic scoping
because elements are never removed from it. Formals are printed as implicit
arguments.")

(declaim (ftype (function (symbol type-expr thy-bindings) thy-bindings)))
(defun add-thy-binding (va ty bds)
  "Add variable VA of type TY to theory bindings BDS."
  (cons (make-bind-decl va ty) bds))

(declaim (type (polylist (cons symbol symbol)) *ctx-thy-subtypes*))
(defparameter *ctx-thy-subtypes* nil
  "For each u TYPE FROM t present in the theory formals, a cons cell
(u . u_pred) is added to this context. When u is required, it will be printed as
psub u_pred.")

(declaim (ftype (function (cons symbol type-expr) bind-decl) ctxe->bind-decl))
(defun ctxe->bind-decl (e)
  "Convert element E of a context to a `bind-decl'."
  (make!-bind-decl (car e) (cdr e)))

(defstruct tuple-element
  "A place designator in a tuple. PVS frequently performs pattern matching on
tuples, such as f(x,y,z) = x + y + z is in fact f e = car e + cadr e + caddr e.
A `tuple-element' links pattern matched variables (the x, y and z), to their
original tuple. It's made of the identifier of the tuple, the index of the
variable inside the tuple and the length of this tuple."
  id
  (index 0 :type integer)
  (length 0 :type integer))
(defun mk-tuple-element (id ind len)
  "Create a tuple element at index IND of tuple ID of length LEN (with
positional argument)."
  (assert (<= ind len))
  (make-tuple-element :id id :index ind :length len))

;;; A bit like a context but not truly a context
(declaim (type (polylist (cons symbol tuple-element)) *packed-tuples*))
(defparameter *packed-tuples* nil
  "A mapping (v . te) of this list means that variable V is encoded as the tuple
element TE. This variable is filled by `pack-arg-tuple' (using lexical
scoping).")

;;; Misc functions

(declaim (ftype (function (expr) type-expr) type-of-expr))
(defgeneric type-of-expr (ex)
  (:documentation "Get the type attributed to expression EX by PVS.")
  (:method ((ex name-expr)) (type (car (resolutions ex))))
  (:method ((ex bind-decl)) (type ex))
  (:method ((ex expr-as-type)) (expr ex))
  (:method (ex) (error "Unknown expression" (describe ex))))

(declaim (type integer *var-count*))
(defparameter *var-count* 0
  "Number of generated variables. Used to create fresh variable names.")

(declaim (ftype (function (string) string) fresh-var))
(defun fresh-var (&key (prefix ""))
  "Provide a fresh variable name."
  (let ((var-name (format nil "_~av~36r" prefix *var-count*)))
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

(defun contexts (ind &optional obj)
  "Prints debug information on standard output with IND an indication (typically
a function name from where the debug is called)."
  (dk-log nil "~a:" ind)
  (dk-log nil "~a:" obj)
  (dk-log nil "  thf:~i~<~a~:>" (list pvs::*thy-bindings*))
  (dk-log nil "  tst:~i~<~a~:>" (list pvs::*ctx-thy-subtypes*))
  (dk-log nil "  ctx:~i~<~a~:>" (list pvs::*ctx*))
  (dk-log nil "  tup:~i~<~a~:>" (list pvs::*packed-tuples*)))

(in-package :pvs)

(declaim
 (ftype
  (function (list * *) (cons (polylist bind-decl) (polylist tuple-element)))
  pack-arg-tuple))
(defun pack-arg-tuple (args &key vars projspec)
  "Transform the list of list of formals in ARGS into a pair (vs . ps)
where VS is a list of binding declarations, and PS is a list of projection
specifications. For each element E of ARGS, if its length is one, then it is a
variable and a `bind-decl' is made out of it and added to VS. Otherwise, the
list stands for a (PVS) tuple. In that case, a fresh variable is created for the
binding declaration, and its type is the tuple type made of the list of types of
the elements of E.
The second element is a list of projection specifications. For each element E of
ARGS, if its length is one, its projection specification is `nil'. Otherwise, it
is a pair (x . te) where X is the identifier of the formal (that is
an element of a tuple) and TE a `tuple-element'.
We have ARGS of same length as VS and PS."
  (labels
      ((type-with-ctx (elt)
         "Type formal ELT with its `declared-type' if it exists, or from
`*ctx*'."
         (declare (type expr elt))
         (with-slots (id declared-type) elt
           (if declared-type declared-type (cdr (assoc id *ctx*)))))
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
                   collect
                   (let ((te (mk-tuple-element var i len)))
                     (cons (id e) te)))))))
    (if (null args) (cons (reverse vars) (reverse projspec))
        (destructuring-bind (hd &rest tl) args
          (declare (type list hd))
          (let* ((bd (pack-type hd))
                 (spec (get-pspec hd (id bd))))
            (pack-arg-tuple
             tl :vars (cons bd vars)
             :projspec (concatenate 'list spec projspec)))))))

;;; Specialised printing functions

(defparameter +dk-id-forbidden+
  (list #\Newline #\Space #\Rubout #\Tab #\: #\, #\; #\`
        #\( #\) #\{ #\} #\[ #\])
  "List of characters that are forbidden inside Dedukti identifiers.")

(defun dk-id-char-p (thing)
  "True if THING is a character allowed in Dedukti identifiers."
  (and (characterp thing) (not (member thing +dk-id-forbidden+))))

(declaim (ftype (function (* stream) *) pprint-ident))
(defgeneric pprint-ident (id stream)
  (:documentation "Transform identifier ID so that is can be read by Dedukti and
print it to stream STREAM."))
(defmethod pprint-ident ((id string) stream)
  "Print identifier IDENT to STREAM so that it can be read by Lambdapi."
  (if (every #'dk-id-char-p id)
      (princ id stream)
      (format stream "{|~a|}" id)))
(defmethod pprint-ident ((id symbol) stream)
  "Resolve symbol SYM, transform it to a Dedukti identifier and print it to
stream STREAM."
  (aif (assoc id *dk-sym-map*)
       (princ (cdr it) stream)
       (pprint-ident (mkstr id) stream)))
(defun pp-sym (stream sym &optional _colon-p _at-sign-p)
  "Wrapper of pprint-ident to be used in format strings."
  (pprint-ident sym stream))

(defun pp-type (stream tex &optional wrap at-sign-p)
  "Print `Set' if TEX is `*type*', or prefix TEX by `El'."
  (if (is-*type*-p tex) (write-string "Set" stream)
      (with-parens (stream wrap)
        (format stream "El ~:/pvs:pp-dk/" tex))))

(declaim
 (ftype (function (bind-decl
                   stream
                   &optional boolean)
                  *) pprint-bind-decl))
(defun pprint-bind-decl (bd stream &optional impl)
  "Print binding BD as id: type to stream STREAM between curly braces if IMPL is
true."
  (when impl (write-char #\{ stream))
  (with-slots (id declared-type) bd
    (pp-sym stream id)
    (write-char #\: stream)
    (if declared-type
        (with-extended-context (bd *ctx*)
          ;; Print the body with the variable in context
          (pp-type stream declared-type))
        (let ((typ (cdr (assoc id *ctx-var*))))
          ;; If the type of the binding is not specified, then the
          ;; variable must be typed by a x: VAR t declaration, and
          ;; hence end up in `*ctx-var*'. We do not need to complete
          ;; `*ctx*'.
          (format stream "El ~:/pvs:pp-dk/" typ))))
  (when impl (write-char #\} stream)))

(declaim (ftype
          (function
           ((or expr type-expr)
            list
            stream &key (wrap boolean) (impl integer)) null)
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
          (pprint-bind-decl hd stream (> impl 0))
          (write-char #\, stream)
          (with-extended-context (hd *ctx*)
            (pprint-abstraction ex tl stream :impl (- impl 1)))))))

(declaim (ftype (function (type-expr symbol list stream *) null)
                pprint-product))
(defun pprint-product (tex kind bds stream &key wrap (impl 0))
  "Print `Π x1: t1, Π x2: t2, ..., Π xn: tn, ξ (TEX)' where `(xi, ti)' are the
bindings of BDS, and ξ is determined by KIND which may be :set, :prop or :kind.
The first IMPL arguments are made implicit (wrapped into curly brackets)."
  (if (null bds)
      (case kind
        ;; The only term of type Kind is "Set"
        (:kind (assert (equalp (mkstr tex) "type")) (pp-dk stream tex))
        (:set (format stream "El ~:/pvs:pp-dk/" tex))
        (:prop (format stream "Prf ~:/pvs:pp-dk/" tex)))
      (destructuring-bind (bd &rest tl) bds
        (write-char #\Π stream)
        (write-char #\space stream)
        (pprint-bind-decl bd stream (> impl 0))
        (write-char #\, stream)
        (with-extended-context (bd *ctx*)
          (pprint-product tex kind tl stream :impl (- impl 1))))))

(declaim (ftype (function (type-expr symbol stream *) null) pprint-thy-formals))
(defun pprint-thy-formals (tex kind stream &optional wrap)
  "Print type expression TEX prefixed by as many products as there are formals
in the theory. Formals are implicit. Parameter KIND behaves as in
`pprint-product'."
  (let* ((thy-bds (reverse *thy-bindings*))
         (len (length thy-bds)))
    (pprint-product tex kind thy-bds stream :wrap wrap :impl len)))

(declaim (ftype (function (symbol stream string) *) pprint-reqopen))
(defun pprint-reqopen (mod stream &optional root)
  "Prints a ``require open'' directive opening module MOD with root path ROOT on
stream STREAM."
  (write-string "require open" stream)
  (unless (null root)
    (write-char #\space stream)
    (write-string root stream)
    (write-char #\. stream))
  (princ mod stream)
  (open-sig mod))

(declaim (ftype (function (stream obj * *) *) pp-impl))
(defun pp-impl (stream obj &optional _colon-p at-sign-p)
  "Print object OBJ to stream STREAM if `*print-implicits*' is true."
  (when *print-implicits*
    (write-char #\{ stream)
    (pp-dk stream obj nil at-sign-p)
    (write-char #\} stream)))

;;; Main printing

(declaim (ftype (function (stream syntax * *) *) pp-dk))
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
               (let ((pred (predicate (type-value hd))))
                 ;; No dynamic scoping because `*ctx-thy-subtypes*' and
                 ;; `*thy-bindings*' are never depleted
                 (psetf
                  *ctx-thy-subtypes*
                  (acons (id hd) (id pred) *ctx-thy-subtypes*)
                  *thy-bindings*
                  (add-thy-binding (id pred) (type pred) *thy-bindings*))
                 (process-formals tl theory)))
              ((formal-type-decl? hd)
               (setf *thy-bindings*
                     (add-thy-binding (id hd) *type* *thy-bindings*))
               (process-formals tl theory))
              ((formal-const-decl? hd)
               (let (;; REVIEW adding to *ctx* might be superfluous
                     (*ctx* (acons (id hd) (declared-type hd) *ctx*)))
                 (setf *thy-bindings*
                       (add-thy-binding (id hd) (declared-type hd)
                                        *thy-bindings*))
                 (process-formals tl theory))))))))
    (with-slots (id theory formals-sans-usings) mod
      (setf *signature* (dksig:make-signature :theory id))
      (format stream "// Theory ~a~%" id)
      (let ((prelude (mapcar #'id *prelude-theories*)))
        (loop for m in (list-upto prelude id) do
          (pprint-reqopen m stream "pvs.prelude")
          (write-char #\; stream)
          (fresh-line stream)))
      (process-formals formals-sans-usings theory)
      (dump-sig))))

(defmethod pp-dk (stream (imp importing) &optional colon-p at-sign-p)
  "Prints importing declaration IMP."
  (with-slots (theory-name) imp
    (format stream "require ~a;" theory-name)))

;;; Declarations

(defmethod pp-dk (stream (decl type-decl) &optional colon-p at-sign-p)
  "t: TYPE."
  (dklog:decl "type decl")
  (with-slots (id) decl
    (with-sig-update (newid id nil *signature*)
      (format stream "constant symbol ~/pvs:pp-sym/: " newid)
      (pprint-thy-formals *type* :kind stream t)
      (write-char #\; stream))))

(defmethod pp-dk (stream (decl type-eq-decl) &optional colon-p at-sign-p)
  "t: TYPE = x, but also domain(f): TYPE = D"
  (dklog:decl "type-eq-decl")
  (with-slots (id type-expr formals) decl
    (with-sig-update (newid id nil *signature*)
      (format stream "symbol ~/pvs:pp-sym/: " newid)
      (let* ((args (car (pack-arg-tuple formals)))
             (bds (nconc (reverse *thy-bindings*) args)))
        (pprint-product
         *type* :kind bds stream :wrap t :impl (length *thy-bindings*)))
      (write-string " ≔ " stream)
      (let* ((form-spec (pack-arg-tuple formals))
             (*packed-tuples* (cdr form-spec))
             (thy-bds (reverse *thy-bindings*))
             (bindings (append thy-bds (car form-spec))))
        (pprint-abstraction type-expr bindings stream
                            :impl (length *thy-bindings*)))
      (write-char #\; stream))))

(defmethod pp-dk (stream (decl type-from-decl) &optional colon-p at-sign-p)
  "t: TYPE FROM s"
  (dklog:contexts "type from" decl)
  (dklog:decl "type-from-decl")
  (with-slots (id predicate supertype) decl
    (with-sig-update (newid id nil *signature*)
      ;; PREDICATE is a type declaration
      (format stream "symbol ~/pvs:pp-sym/: " newid)
      (pprint-thy-formals *type* :kind stream t)
      (write-string " ≔ " stream)
      (pprint-abstraction
       ;; Build properly the subtype expression for printing
       (mk-subtype supertype (mk-name-expr (id predicate)))
       (reverse *thy-bindings*)
       stream
       :impl (length *thy-bindings*))
      (write-char #\; stream))))

(defmethod pp-dk (stream (decl formula-decl) &optional colon-p at-sign-p)
  (dklog:decl "formula: ~S" (id decl))
  (with-slots (spelling id definition) decl
    (format stream "// Formula declaration: ~a~&" spelling)
    ;; TODO the type is for now `nil', something more meaningful must be used,
    ;; in accordance to what the type is when the name of the  formula is
    ;; printed
    (with-sig-update (newid id nil *signature*)
      (flet
          ((univ-closure (ex)
             (let* ((free-ids (mapcar #'id (freevars ex)))
                    (bindings (mapcar
                               #'(lambda (id)
                                   (ctxe->bind-decl (assoc id *ctx*)))
                               free-ids)))
               ;; Here we may build a formula of the form FORALL (x,y,..):
               ;; FORALL (z,...):..., but it shouldn't be a problem.
               (if (null bindings) ex (make!-forall-expr bindings ex)))))
        (declaim (ftype (function (expr) forall-expr) univ-closure))
        (let ((defn (univ-closure definition))
              (axiomp (member spelling '(AXIOM POSTULATE))))
          (unless axiomp (write-string "opaque " stream))
          (format stream "symbol ~/pvs:pp-sym/ : " newid)
          (pprint-thy-formals defn :prop stream t)
          (unless axiomp
            ;; TODO: export proof
            (write-string " ≔" stream))
          (write-string " begin admitted;" stream))))))

(defmethod pp-dk (stream (decl const-decl) &optional colon-p at-sign-p)
  (dklog:decl "const: ~S" (id decl))
  (dklog:contexts "const-decl")
  (with-slots (id type definition formals) decl
    (format stream "// Constant declaration ~a~%" id)
    (with-sig-update (newid id type *signature*)
      (if definition
          (let* ((form-proj (pack-arg-tuple formals))
                 (*packed-tuples* (cdr form-proj))
                 (ctx-thy (reverse *thy-bindings*))
                 (form-bds (car form-proj))
                 (bindings (concatenate 'list ctx-thy form-bds)))
            (format stream "symbol ~/pvs:pp-sym/: " newid)
            (pprint-thy-formals type :set stream t)
            (write-string " ≔ " stream)
            (pprint-abstraction definition bindings stream
                                :impl (length *thy-bindings*)))
          (progn
            (format stream "symbol ~/pvs:pp-sym/: " newid)
            (pprint-thy-formals type :set stream t)))
      (write-string " begin admitted;" stream))))

(defmethod pp-dk (stream (decl macro-decl) &optional _colon-p _at-sign-p)
  "Ignore macro definitions, they are expanded anyway."
  nil)

;; REVIEW: a lot of duplication between inductive-decl and const-decl, but
;; inductive decl is not yet handled as it should
(defmethod pp-dk (stream (decl inductive-decl) &optional colon-p at-sign-p)
  (dklog:decl "inductive: ~S" (id decl))
  (with-slots (id type definition formals) decl
    (format stream "// Inductive definition ~a~%" id)
    (with-sig-update (newid id type *signature*)
      (let* ((form-proj (pack-arg-tuple formals))
             (*packed-tuples* (cdr form-proj))
             (ctx-thy (reverse *thy-bindings*))
             (form-bds (car form-proj))
             (bindings (concatenate 'list ctx-thy form-bds)))
        (format stream "symbol ~/pvs:pp-sym/:" newid)
        (pprint-thy-formals type :set stream t)
        ;; TODO inductive definitions are not handled yet, they are axiomatised
        (write-string "/*" stream)       ;Comment definition
        (write-string " ≔ " stream)
        (pprint-abstraction definition bindings stream
                            :impl (length *thy-bindings*))
        (write-string "*/" stream)       ;End of definition comment
        (write-string " begin admitted;" stream)))))

(defmethod pp-dk (stream (decl def-decl) &optional colon-p at-sign-p)
  (error "Recursive function definitions are not handled yet."))

(defmethod pp-dk (stream (decl conversion-decl) &optional colon-p at-sign-p)
  "CONVERSION elt, there are conversion(plus|minus)-decl as well."
  (dklog:decl "conversion")
  (dklog:contexts "conversion-decl")
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
  (dklog:decl "application judgement")
  (dklog:contexts "application-judgement" decl)
  (with-slots (id formals declared-type judgement-type name) decl
    (format stream "// Application judgement \"~a\"~%" id)))


(defmethod pp-dk (stream (decl expr-judgement) &optional colon-p _at-sign-p)
  (dklog:contexts "expr-judgement")
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
  (aif (print-type te)
       (pp-dk stream it colon-p at-sign-p)
       (call-next-method)))

(defmethod pp-dk (stream (te tupletype) &optional colon-p at-sign-p)
  "[bool, bool] but also [bool, bool -> bool]"
  (dklog:type "tuple")
  (with-slots (types) te
    (with-parens (stream colon-p)
      (write-string "σ " stream)
      ;; Any tuple type has at least two elements
      (if (= 2 (length types))
          (destructuring-bind (s u) types
            (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/" s u))
          (destructuring-bind (hd &rest tl) types
            (format stream "~:/pvs:pp-dk/ ~:/pvs:pp-dk/"
                    hd (make-tupletype tl)))))))

(defmethod pp-dk (stream (te subtype) &optional colon-p at-sign-p)
  "{n: nat | n /= zero} or (x | p(x)), see classes-decl.lisp:824"
  (dklog:type "subtype")
  (with-slots (supertype predicate) te
    (with-parens (stream colon-p)
      (write-string "@psub " stream)
      (assert supertype)
      (format stream "~:/pvs:pp-dk/ " supertype)
      (pp-dk stream predicate t at-sign-p))))

(defmethod pp-dk (stream (te expr-as-type) &optional colon-p at-sign-p)
  "Used in e.g. (equivalence?), that is, a parenthesised expression used as a
type."
  (dklog:type "expr-as-type")
  (with-slots (expr) te
    (with-parens (stream colon-p)
      ;; REVIEW: get the domain of expression E and pass it as first argument of
      ;; psub
      (format stream "psub ~:/pvs:pp-dk/" expr))))

(defmethod pp-dk (stream (te simple-expr-as-type) &optional colon-p at-sign-p)
  "Used in e.g. (equivalence?) without inheriting subtypes. I don't know when it
can be used."
  (dklog:type "simpl-expr-as-type")
  (with-slots (expr) te
    (pp-dk stream expr colon-p at-sign-p)))

(defmethod pp-dk (stream (te type-application) &optional colon-p at-sign-p)
  "Prints type application TE to stream STREAM. Used for instance with dependent
(sub)types `subt(i)` where `subt(i) = {x: ... | f(i)}`."
  (dklog:type "type-application")
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

(defgeneric pprint-funtype (domain range stream &optional wrap)
  (:documentation "Print function type from type DOMAIN to type RANGE on stream
STREAM."))

(defmethod pprint-funtype ((domain dep-binding) range stream &optional wrap)
  (with-slots (id declared-type) domain
    (with-parens (stream wrap)
      (format stream "arrd ~:/pvs:pp-dk/ " declared-type)
      (pprint-abstraction
       range (list (mk-bind-decl id declared-type)) stream :wrap t))))

(defmethod pprint-funtype (domain range stream &optional wrap)
  (with-parens (stream wrap)
    (format stream "~:/pvs:pp-dk/ ~~> ~/pvs:pp-dk/" domain range)))

(defmethod pp-dk (stream (te funtype) &optional colon-p _at-sign-p)
  "Prints function type TE to stream STREAM."
  (dklog:type "funtype")
  (with-slots (domain range) te
    (pprint-funtype domain range stream colon-p)))

;;; Expressions

(declaim
 (ftype (function (symbol
                   (or type-expr null)
                   stream
                   &key (mod-id *) (actuals list) (wrap boolean)) *)
        pprint-name))
(defun pprint-name (id ty stream &key mod-id actuals wrap)
  "Print identifier ID of module MOD-ID to stream STREAM with ACTUALS applied.
If WRAP is true, then the application of ID to ACTUALS is wrapped between
parentheses. The type TY of the symbol represented by ID may be used to resolve
overloading."
  (acond
    ;; Member of an unpacked tuple: as it has been repacked, we transform this
    ;; to successsion of projections
    ((assoc id *packed-tuples*)
     (with-slots (id index length) (cdr it)
       (with-parens (stream wrap)
         (format stream "proj ~d ~d ~/pvs:pp-sym/" index (- length 1) id))))
    ((assoc id *ctx*) (pp-sym stream id))
    ;; The symbol is a type declared as TYPE FROM in theory parameters,
    ;; we print the predicate associated
    ((assoc id *ctx-thy-subtypes*)
     (format stream "~:/pvs:pp-sym/" (cdr it)))
    ;; Symbol of the encoding
    ((assoc id *dk-sym-map*) (pp-sym stream id))
    ;; Symbol from the current signature
    ((dksig:find id ty *signature*)
     (with-parens (stream (consp *thy-bindings*))
       (pprint-ident it stream)
       (when *thy-bindings*
         ;; Apply theory arguments (as implicit args) to symbols of signature
         (format
          stream "~{ {~/pvs:pp-sym/}~}"
          (mapcar #'id (reverse *thy-bindings*))))))
    ;; Symbol from an opened signature
    ((dksig:find id ty *opened-signatures*) (pprint-ident it stream))
    ;; Symbol from an imported theory
    (t
     (with-parens (stream (consp actuals))
       (when mod-id
         ;; TODO fail if `mod-id' is `nil'
         (pp-sym stream mod-id)
         (write-char #\. stream))
       ;; (unless mod-id
       ;;   (error "Symbol ~a is supposed to come from an imported theory." id))
       ;; (pp-sym stream mod-id)
       ;; (write-char #\. stream)
       (format stream "~/pvs:pp-sym/~{ {~/pvs:pp-dk/}~}" id actuals)))))

(defmethod pp-dk (stream (ex name-expr) &optional colon-p _at-sign-p)
  "Print name NAME applying theory formal parameters if needed. Takes care of
name resolution"
  (dklog:expr "Name ~S" (id ex))
  (with-slots (id type mod-id actuals) ex
    (pprint-name id type stream :mod-id mod-id :actuals actuals :wrap colon-p)))

(defmethod pp-dk (stream (ex type-name) &optional colon-p _at-sign-p)
  (dklog:expr "Type name ~S" (id ex))
  (with-slots (id mod-id actuals) ex
    (pprint-name id nil stream :mod-id mod-id :actuals actuals
                                  :wrap colon-p)))

(defmethod pp-dk (stream (ex lambda-expr) &optional colon-p _at-sign-p)
  "LAMBDA (x: T): t. The expression LAMBDA x, y: x binds a tuple of two elements
to its first element."
  (dklog:expr "lambda-expr ~a" ex)
  (with-slots (bindings expression) ex
    (if
     (and (listp bindings) (null (cdr bindings))) ;== (= 1 (length bindings))
     ;; If there is only one binding, it represents a variable
     (pprint-abstraction expression bindings stream :wrap colon-p)
     ;; Otherwise, each variable of the binding is the component of a tuple
     (destructuring-bind (bindings . projspecs) (pack-arg-tuple (list bindings))
       (let ((*packed-tuples* (append projspecs *packed-tuples*)))
         (pprint-abstraction expression bindings stream :wrap colon-p))))))

(defmethod pp-dk (stream (te set-expr) &optional colon-p at-sign-p)
  "{n: nat | p(x)}, but an expression, it's only syntactic sugar for LAMBDA (n:
nat): p(x)"
  (dklog:type "set-expr")
  (with-slots (expression bindings) te
    ;; `binding' should contain one binding
    (assert (consp bindings))
    (with-slots (id) (car bindings)
      ;; NOTE: the binding is untyped, can we merge with `lambda-expr'?
      (with-parens (stream colon-p)
        (format stream "λ ~/pvs:pp-sym/, ~:/pvs:pp-dk/"
                id expression)))))

(defmethod pp-dk (stream (ex quant-expr) &optional wrap _at-sign-p)
  (dklog:expr "quantified expression ~S" ex)
  (with-parens (stream wrap)
    (write-char (cond ((forall-expr? ex) #\∀) ((exists-expr? ex) #\∃)) stream)
    (write-char #\Space stream)
    (with-slots (bindings expression) ex
      (destructuring-bind (hd &rest tl) bindings
        (pp-impl stream (type-of-expr hd))
        (let ((subex
                (cond
                  ((null tl) expression) ; No more quantification needed
                  ((forall-expr? ex) (make!-forall-expr tl expression))
                  ((exists-expr? ex) (make!-exists-expr tl expression))
                  (otherwise (error "Invalid expression ~S" ex)))))
          (pprint-abstraction subex (list hd) stream :wrap t))))))

(defmethod pp-dk (stream (ex application) &optional colon-p _at-sign-p)
  "Print application EX. The expression EX ``f(e1,e2)(g1,g2)'' will be printed
as ``f (σcons e1 e2) (σcons g1 g2)''."
  (dklog:expr "application")
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
                  &optional colon-p _at-sign-p)
  "For projections of the form t`2."
  (dklog:contexts "projection-application" ex)
  (with-slots (id index argument) ex
    (let ((len (length (types (type argument))))
          (ident (id argument)))
      (with-parens (stream colon-p)
        ;; TODO print types if *print-implicits* is true
        (format stream "proj ~d ~d ~/pvs:pp-sym/" index len ident)))))

(defmethod pp-dk (stream (ex tuple-expr) &optional colon-p at-sign-p)
  "Prints tuples ``(e1, e2, e3)'' as ``(cons e1 (cons e2 e3))''. Note that we
use implicit arguments for ``cons''."
  (dklog:expr "tuple-expr")
  (with-slots (exprs) ex
    ;; Tuple types have at least 2 elements (PVS invariant)
    (with-parens (stream colon-p)
      (cond
        ((= 2 (length exprs))
         (destructuring-bind (x y) exprs
           (format stream "cons ~:/pvs:pp-impl/ ~:/pvs:pp-impl/ ~
~:/pvs:pp-dk/ ~:/pvs:pp-dk/" (type x) (type y) x y)))
        ((< 2 (length exprs))
         (destructuring-bind (hd &rest tl) exprs
           (let ((argr (make!-tuple-expr tl)))
             (format stream "cons ~:/pvs:pp-impl/ ~:/pvs:pp-impl/ ~
~:/pvs:pp-dk/ ~:/pvs:pp-dk/" (type hd) (type argr) hd argr))))
        (t (error "Tuple ~a have too few elements." ex))))))

(defmethod pp-dk (stream (ex branch) &optional colon-p at-sign-p)
  "IF(a,b,c)"
  (dklog:expr "branch")
  (destructuring-bind (prop then else) (exprs (argument ex))
    (with-parens (stream colon-p)
      (format stream "if ~:/pvs:pp-impl/ ~:/pvs:pp-dk/ " (type ex) prop)
      (format stream "(λ ~a~:[~*~;: Prf ~:/pvs:pp-dk/~], ~/pvs:pp-dk/)"
              (fresh-var) *print-domains* prop then)
      (write-char #\Space stream)
      (format stream "(λ ~a~:[~*~;: Prf (¬ ~:/pvs:pp-dk/)~], ~/pvs:pp-dk/)"
              (fresh-var) *print-domains* prop else))))

;;; REVIEW: factorise disequation and equation

(defmethod pp-dk (stream (ex disequation) &optional colon-p at-sign-p)
  "/=(A, B)"
  (dklog:expr "disequation")
  (with-parens (stream colon-p)
    (let* ((eq-ty (type (operator ex)))
           (dom (types (domain eq-ty)))
           (tyl (car dom))
           (tyr (cadr dom)))
      (assert (equal tyl tyr))
      (with-binapp-args (argl argr ex)
        (format stream
                "@neq ~:/pvs:pp-dk/ ~
(cons ~:/pvs:pp-impl/ ~:/pvs:pp-impl/ ~:/pvs:pp-dk/ ~:/pvs:pp-dk/)"
                tyl (type argl) (type argr) argl argr)))))

(defmethod pp-dk (stream (ex equation) &optional colon-p at-sign-p)
  "=(A, B)"
  (dklog:expr "equation")
  (with-parens (stream colon-p)
    (let* ((eq-ty (type (operator ex)))
           (dom (types (domain eq-ty)))
           (tyl (car dom))
           (tyr (cadr dom)))
      (assert (equal tyl tyr))
      (with-binapp-args (argl argr ex)
        (format
         stream
         "@eq ~:/pvs:pp-dk/ ~
(cons ~:/pvs:pp-impl/ ~:/pvs:pp-impl/ ~:/pvs:pp-dk/ ~:/pvs:pp-dk/)"
         tyl (type argl) (type argr) argl argr)))))

(defmethod pp-dk (stream (ex conjunction) &optional colon-p at-sign-p)
  "AND(A, B)"
  (dklog:expr "conjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format
       stream
       "~:/pvs:pp-dk/ ∧ (λ ~a~:[~*~;: Prf ~:/pvs:pp-dk/~], ~/pvs:pp-dk/)"
       argl (fresh-var) *print-domains* argl argr))))

(defmethod pp-dk (stream (ex disjunction) &optional colon-p at-sign-p)
  "OR(A, B)"
  (dklog:expr "disjunction")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format
       stream
       "~:/pvs:pp-dk/ ∨ (λ ~a~:[~*~;: Prf (¬ ~:/pvs:pp-dk/)~],~/pvs:pp-dk/)"
       argl (fresh-var) *print-domains* argl argr))))

(defmethod pp-dk (stream (ex implication) &optional colon-p at-sign-p)
  "IMPLIES(A, B)"
  (dklog:expr "implication")
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format
       stream
       "~:/pvs:pp-dk/ ⇒ (λ ~a~:[~*~;: Prf ~:/pvs:pp-dk/~],~/pvs:pp-dk/)"
       argl (fresh-var) *print-domains* argl argr))))

(defmethod pp-dk (stream (ex iff) &optional colon-p at-sign-p)
  "IFF(A, B)"
  (with-parens (stream colon-p)
    (with-binapp-args (argl argr ex)
      (format stream "iff ~:/pvs:pp-dk/ ~:/pvs:pp-dk/" argl argr))))

(defmethod pp-dk (stream (ex negation) &optional colon-p _at-sign-p)
  "NOT(A), there is also a `unary-negation' that represents NOT A."
  (dklog:expr "negation")
  (with-parens (stream colon-p)
    (format stream "¬ ~:/pvs:pp-dk/" (argument ex))))

(defmethod pp-dk (stream (ex number-expr) &optional colon-p at-sign-p)
  (dklog:expr "number")
  ;; PVS uses bignum while lambdapi is limited to 2^30 - 1
  (format stream "~d" ex))

(defmethod pp-dk (stream (ac actual) &optional colon-p at-sign-p)
  "Formal parameters of theories, the `t' in `pred[t]'."
  (dklog:expr "actual")
  (pp-dk stream (expr ac) colon-p at-sign-p))

(defmethod pp-dk (stream (ex bitvector) &optional _colon-p _at-sign-p)
  (error "Bitvectors not handled yet."))
