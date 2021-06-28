(defpackage dksig
  (:documentation "Signatures for the export to Dedukti. They allow to remove
overloading from PVS' theories")
  (:use :cl :esrap)
  (:import-from :pvs :aif)
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
if they are `pvs::tc-eq'."
  (or (and (null x) (null y)) (and x y (pvs::tc-eq x y))))

;; TODO add opened signatures to `add' to perform overloading across theories
(declaim
 (ftype (function (symbol some-pvs-type signature)
                  (values string signature)) add))
(defun add (id ty sig)
  "Add the declaration of symbol ID of type TY to the signature SIG and return
the new identifier that is to be used in place of ID and the new signature.
Destructive on SIG."
  (let ((sid (string id))) ;for some reason it doesn't work with mkstr
    (aif (gethash sid (signature-decls sig))
         (multiple-value-bind (suff vs) (add-variant ty it)
           (setf (gethash sid (signature-decls sig)) vs)
           (values (concatenate 'string sid suff) sig))
         (progn
           (setf (gethash sid (signature-decls sig)) (init-variants sid ty))
           (values sid sig)))))

(declaim
 (ftype (function (symbol some-pvs-type signature) (or null string)) find1))
(defun find1 (id ty sig)
  "Get the appropriate identifier for PVS symbol identified with ID of type TY
among defined symbols of signature SIG."
  (aif (gethash (string id) (signature-decls sig))
       (aif (cl:find ty it :test #'some-pvs-type-eq :key #'variant-type)
            (concatenate 'string (string id) (variant-suffix it)))))

(declaim (ftype (function (symbol some-pvs-type list) (or null string))))
(defun find* (id ty sigs)
  "Search for symbol ID of type TY among signatures SIGS."
  (when sigs
    (aif (find1 id ty (car sigs)) it
         (find* id ty (cdr sigs)))))

(defun find (id ty sig)
  "Find symbol SYM of type TY in signature(s) SIG."
  (if (listp sig) (find* id ty sig) (find1 id ty sig)))

(declaim (ftype (function (stream variant) *) pp-variant))
(defun pp-variant (stream v &optional colon-p at-sign-p)
  "Write variant V to stream STREAM such that it can be read back by `open'."
  (declare (ignore colon-p at-sign-p))
  (with-slots (type suffix) v
    ;; Some setup to have compact signatures
    (let ((pvs::*pp-no-newlines?* t)
          (pvs::*pp-compact* t)
          (pvs::*pp-print-pretty* nil))
      (format stream "($~a$ . \"~a\")" type suffix))))

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
;;; (("s0" . ($ty0,0$ . "d0,0") ($ty0,1$ . "d0,1"))
;;;  ("s1" . ($ty1,0$ . "d1,0") ($ty1.1$ . "d1.1")))
;;; where s0, s1 are the symbols from PVS, tyi,j are the types of these symbols,
;;; there may be several types when the symbol is overloaded. Types are between
;;; carets to ease parsing. And di,j are the symbols used into the Dedukti
;;; translation, to bypass overloading.

(defrule whitespace (+ (or #\Space #\Tab #\Newline))
  (:constant nil))

;; Parse a PVS type surrounded by dollars
(defrule some-pvs-type (and #\$ (+ (not #\$)) #\$)
  (:destructure (op ty cl)
    (declare (ignore op cl))
    (let ((ty (concatenate 'string ty)))
      (if (string= ty "NIL") nil
          (pvs::parse :string ty :nt 'pvs:type-expr)))))

;; Transform a string into a symbol
(defrule stringlit (and #\" (* (not #\")) #\")
  (:destructure (qu1 el qu2)
    (declare (ignore qu1 qu2))
    (concatenate 'string el)))

;; Parses a cell of the form "(" pvs-type "." stringlit ")"
(defrule variant
    (and #\( some-pvs-type (? whitespace) #\. (? whitespace) stringlit #\))
  (:destructure (ca1 ty w1 d w2 str ca2)
    (declare (ignore ca1 w1 d w2 ca2))
    (make-variant :type ty :suffix str)))

;; Parses a list of cells
(defrule variants (* (and variant (? whitespace)))
  (:lambda (cs) (mapcar #'car cs)))

;; Parses the declaration of a symbol "(" stringlit . "(" cells ")" ")"
(defrule sig-decl
    (and #\( stringlit (? whitespace) #\. (? whitespace) #\( variants #\) #\))
  (:destructure
    (pa1 sym w1 dot w2 pa2 variants pa3 pa4)
    (declare (ignore pa1 w1 dot w2 pa2 pa3 pa4))
    (cons sym variants)))

(defrule sig-top (and #\( (? whitespace) (* (and sig-decl (? whitespace))) #\))
  (:destructure
    ;; Keep only the variants
    (pa1 w cells pa2)
    (declare (ignore pa1 w pa2))
    cells)
  (:lambda (cells)
    ;; Remove the whitespace from parsed element
    (mapcar #'car cells)))

(declaim (ftype (function (* string) signature) open))
(defun open (theory s)
  "Create a signature for theory THEORY from stream S."
  (let
      ((decls
         (multiple-value-bind (prod pos succ) (esrap:parse 'sig-top s)
           (declare (ignore pos))
           (assert
            succ () "Open signature failed: can't parse signature.")
           (assert (every #'variants-p (mapcar #'cdr prod)))
           (assert (every #'stringp (mapcar #'car prod)))
           prod))
       (ht (make-hash-table)))
    (mapc #'(lambda (d) (setf (gethash (car d) ht) (cdr d))) decls)
    (make-signature :theory theory :decls ht)))
