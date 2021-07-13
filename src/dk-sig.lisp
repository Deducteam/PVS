(defpackage dklog
  (:documentation "Some logging facilities.")
  (:use :cl)
  (:export :top :expr :type :decl :sign :contexts)
  (:shadow :expr :type :decl :sign :contexts))

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
      (declare (ignore date month year dow dst-p tz))
      (format out "[~d:~d:~d] " hour minute second))
    (if tag (format out "[~a] " tag))
    (apply #'format out format-str args)
    (terpri out)))

(defun top (format-str &rest args)
  (apply #'dk-log nil format-str args))
(defun sign (format-str &rest args)
  (apply #'dk-log "sign" format-str args))
(defun decl (format-str &rest args)
  (apply #'dk-log "decl" format-str args))
(defun expr (format-str &rest args)
  (apply #'dk-log "expr" format-str args))
(defun type (format-str &rest args)
  (apply #'dk-log "type" format-str args))

(defpackage dksig
  (:documentation "Signatures for the export to Dedukti. They allow to remove
overloading from PVS' theories")
  (:use :cl)
  (:import-from :pvs :aif :mkstr :symb)
  (:export
   :signature :make-signature :signature-theory
   :find :add
   :open :dump)
  (:shadow :open :find))

;; TODO: solving overloading across theories is not yet handled. If `foo' is
;; defined in two different theories with two different types, thu current
;; algorithm won't create a new name for the overloading `foo'.

(in-package :dksig)

(defun some-pvs-type-p (thing)
  (or (null thing) (pvs:type-expr? thing)))

(defun variants-p (thing)
  (and (listp thing) (every #'variant-p thing)))

(deftype some-pvs-type ()
  "A PVS type or `nil'."
  '(satisfies some-pvs-type-p))

(defstruct variant
  "A variant of a symbol. It is identified by its type, and has a suffix to be
appended to the symbol."
  (type nil :type some-pvs-type) (suffix "" :type string))

(deftype variants ()
  "A list of variants."
  '(satisfies variants-p))

(defstruct signature
  "A signature is made of the identifier of its theory and a hash table mapping
symbols as they appear in PVS to a list of variants."
  theory
  (decls (make-hash-table)))

(declaim (ftype (function (* some-pvs-type) variants) init-variants))
(defun init-variants (id ty)
  "Create a new list of variants for symbol of identifier ID whose type is TY."
  (declare (ignore id))
  (list (make-variant :type ty)))

(declaim (ftype (function (some-pvs-type variants)
                          (values string variants)) add-variant))
(defun add-variant (ty vs)
  "Add a variant with type TY to variants VS and return the new list of variants
along with the suffix of the new variant."
  (let* ((suff (format nil "~36r" (length vs)))
         (v (make-variant :type ty :suffix suff)))
    (values suff (append vs (list v)))))

(declaim (ftype (function (some-pvs-type some-pvs-type) *) some-pvs-type-eq))
(defun some-pvs-type-eq (x y)
  "PVS equality on optional terms. X and Y are equal if they are both `nil' or
if they are `pvs:ps-eq'. Behaviour on open term is undefined."
  (or (and (null x) (null y)) (and x y (pvs:ps-eq x y))))

;; TODO add opened signatures to `add' to perform overloading across theories
(declaim
 (ftype (function (symbol some-pvs-type signature)
                  (values symbol signature)) add))
(defun add (sym ty sig)
  "Add the declaration of symbol sym of type TY to the signature SIG and return
the new identifier that is to be used in place of SYM and the new signature.
Destructive on SIG."
  (aif (gethash sym (signature-decls sig))
       (multiple-value-bind (suff vs) (add-variant ty it)
         (setf (gethash sym (signature-decls sig)) vs)
         (values (symb sym suff) sig))
       (progn
         (setf (gethash sym (signature-decls sig)) (init-variants sym ty))
         (values sym sig))))

(declaim
 (ftype (function (symbol some-pvs-type signature) (or null symbol)) find1))
(defun find1 (sym ty sig)
  "Get the appropriate identifier for PVS symbol identified with symbol SYM of
type TY among defined symbols of signature SIG."
  (aif (gethash sym (signature-decls sig))
       (aif (cl:find ty it :test #'some-pvs-type-eq :key #'variant-type)
            (symb sym (variant-suffix it)))))

(declaim (ftype (function (symbol some-pvs-type list) (or null symbol))))
(defun find* (sym ty sigs)
  "Search for symbol SYM of type TY among signatures SIGS."
  (if (consp sigs)
      (aif (find1 sym ty (car sigs)) it (find* sym ty (cdr sigs)))))

(defun find (sym ty sig)
  "Find symbol SYM of type TY in signature(s) SIG."
  (if (listp sig) (find* sym ty sig) (find1 sym ty sig)))

(declaim (ftype (function (stream variant) *) pp-variant))
(defun pp-variant (stream v &optional colon-p at-sign-p)
  "Write variant V to stream STREAM such that it can be read back by `open'."
  (declare (ignore colon-p at-sign-p))
  (with-slots (type suffix) v
    ;; Some setup to have compact signatures
    (let ((pvs::*pp-no-newlines?* t)
          (pvs::*pp-compact* t)
          (pvs::*pp-print-pretty* nil))
      (format stream "(\"~a\" . \"~a\")" type suffix))))

(declaim (ftype (function (stream signature) *) pp-signature))
(defun pp-signature (s sig &optional colon-p at-sign-p)
  (declare (ignore colon-p at-sign-p))
  (princ #\( s)
  (maphash
   #'(lambda (sym vs)
       (format s "(\"~a\" . (~{~/dksig::pp-variant/~^ ~}))" sym vs))
   (signature-decls sig))
  (princ #\) s))

(declaim (ftype (function (signature stream) *) dump))
(defun dump (sig stream)
  "Write signature SIG to stream STREAM."
  (pp-signature stream sig))

;;; Rules to parse saved to disk signatures
;;; Signatures are saved in the following format
;;; (("s0" . ("ty0,0" . "d0,0") ("ty0,1" . "d0,1"))
;;;  ("s1" . ("ty1,0" . "d1,0") ("ty1.1" . "d1.1")))
;;; where s0, s1 are the symbols from PVS, tyi,j are the types of these symbols,
;;; there may be several types when the symbol is overloaded. Types are between
;;; carets to ease parsing. And di,j are the symbols used into the Dedukti
;;; translation, to bypass overloading.

(declaim (ftype (function (string) some-pvs-type) open-some-pvs-type))
(defun open-some-pvs-type (pty)
  (if (string/= pty "NIL") (pvs::parse :string pty :nt 'pvs:type-expr)))

(declaim (ftype (function (cons) variant) open-variant))
(defun open-variant (ts)
  (destructuring-bind (ty . suff) ts
    (make-variant :type (open-some-pvs-type ty) :suffix suff)))

(defun open* (s)
  (let*
      ((presig
         (cond ((stringp s) (with-input-from-string (is s) (read is)))
               ((streamp s) (read s))
               (t (error "Cannot read from ~a." s)))))
    (assert (listp presig))
    (assert (every #'consp presig))
    (assert (every (lambda (sv) (stringp (car sv)) (listp (cdr sv))) presig))
    (mapcar
     (lambda (sv) (cons (symb (car sv)) (mapcar #'open-variant (cdr sv))))
     presig)))

(defun open (theory s)
  (let ((decls (open* s))
        (ht (make-hash-table)))
    (assert (every #'variants-p (mapcar #'cdr decls)))
    (assert (every #'symbolp (mapcar #'car decls)))
    (mapc (lambda (d) (setf (gethash (car d) ht) (cdr d))) decls)
    (make-signature :theory theory :decls ht)))
