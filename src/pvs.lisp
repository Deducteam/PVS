;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pvs.lisp -- Main file for PVS handling PVS commands.
;; Author          : Sam Owre
;; Created On      : Wed Dec  1 15:00:38 1993
;; Last Modified By: Sam Owre
;; Last Modified On: Thu Jul  1 18:50:39 1999
;; Update Count    : 94
;; Status          : Alpha test
;; 
;; HISTORY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :pvs)

;;; This file provides the basic commands of PVS.  It provides the
;;; functions invoked by pvs-cmds.el, as well as the functions used in
;;; batch mode.

;;; Keeps track of the latest edit-proof information - has the form
;;; (DECL PLACE BUFFER PRELUDE-OFFSET)
;;;   - see edit-proof-at, install-proof, and prove-proof-at

(defvar *edit-proof-info* nil)

(defvar *justifications-changed?* nil)

(defvar *started-with-minus-q* nil)

;;; Invoked from Emacs

(defun pvs-init (&optional dont-load-patches dont-load-user-lisp)
  (setq excl:*enclose-printer-errors* nil)
  (setq *print-pretty* t)
  (setf (symbol-function 'ilisp::ilisp-restore) #'pvs-ilisp-restore)
  #+allegro (setq top-level::*print-length* nil
		  top-level::*print-level* nil)
  (setq *started-with-minus-q* dont-load-user-lisp)
  (unless dont-load-patches
    (load-pvs-patches))
  (pvs-init-globals)
  (initialize-decision-procedures))

(defun pvs-init-globals ()
  (setq *pvs-modules* (make-hash-table :test #'eq :size 20 :rehash-size 10))
  (setq *pvs-files* (make-hash-table :test #'equal))
  (setq *loaded-libraries* (make-hash-table :test #'equal))
  (setq *imported-libraries* (make-hash-table :test #'equal))
  (setq *prelude-libraries* (make-hash-table :test #'equal))
  (setq *prelude-library-context* nil)
  (reset-typecheck-caches)
  (setq *current-theory* nil)
  (setq *last-proof* nil)
  (clrnumhash)
  (setq *pvs-context-writable* (write-permission? (working-directory)))
  (setq *pvs-library-path* (get-pvs-library-path))
  ;;(restore-context)
  ;; This strange-looking line just looks at the bdd_interrupted variable.
  ;; This is because the first time lisp looks at the variable, it returns
  ;; a bogus value.  I suspect this is an Allegro bug.
  bdd_interrupted
  (setq *pvs-initialized* t)
  (when *to-emacs*
    (pvs-emacs-eval "(setq *pvs-initialized* t)")))

(defun reset-typecheck-caches ()
  (dolist (fn *untypecheck-hook*)
    (funcall fn))
  (when *subst-type-hash* (clrhash *subst-type-hash*))
  (reset-subst-mod-params-cache)
  (reset-pseudo-normalize-caches)
  ;;(reset-fully-instantiated-cache)
  (reset-beta-cache) ;;; PDL added Nov23 1994
  (reset-type-canon-cache)
  (reset-store-object-caches)
  (reset-print-equal-cache)
  (setq *store-object-hash* (make-hash-table :test #'eq))
  (setq *current-theory* nil)
  (setq *last-proof* nil)
  (setq *subtype-names* nil)
  (setq *named-exprs* nil)
  (setq *edit-proof-info* nil)
  (setq *add-declaration-info* nil)
  (setq *mod-declaration-info* nil))

(defun remove-typecheck-caches ()
  (remove-subst-mod-params-cache)
  (remove-pseudo-normalize-cache)
  (remove-beta-cache)
  (remove-store-object-caches)
  (setq *store-object-hash* nil))

(defun clear-theories (&optional all?)
  (reset-typecheck-caches)
  (clrhash *pvs-modules*)
  (clrhash *pvs-files*)
  (setq *circular-file-dependencies* nil)
  (when all?
    (clrhash *loaded-libraries*)
    (clrhash *prelude-libraries*)
    (clrhash *imported-libraries*)
    (setq *prelude-libraries-uselist* nil)
    (setq *prelude-library-context* nil)))

(defun get-pvs-library-path ()
  (setq *pvs-library-path* nil)
  (let ((libs nil)
	(pathenv (environment-variable "PVS_LIBRARY_PATH")))
    (when pathenv
      (let ((dirs (excl:split-regexp ":" pathenv)))
	(dolist (dir dirs)
	  (unless (char= (char dir (1- (length dir))) #\/)
	    (setq dir (concatenate 'string dir "/")))
	  (cond ((file-exists-p dir)
		 (pushnew dir libs :test #'file-equal))
		(t (pushnew dir libs :test #'string=)
		   (pvs-message "Directory ~a in PVS_LIBRARY_PATH does not exist"
		     dir))))))
    (pushnew (concatenate 'string *pvs-path* "/lib") libs :test #'file-equal)
    (setq *pvs-library-path* (nreverse libs))))

(defvar *pvs-patches-loaded* nil)

(defvar *pvs-binary-type*
    #+(and allegro sparc) "fasl"	; Sun4
    #+(and allegro rios) "rfasl"	; PowerPC/RS6000
    #+(and allegro hpux) "hfasl"	; HP 9000
    #+(and allegro x86) "lfasl"         ; Intel x86
    #+(and lucid lcl4.1 sparc) "sbin"	; Sun4 new Lucid
    #+(and lucid (not lcl4.1) sparc) "obin" ; Sun4 old Lucid
    #+(and lucid rios) "rbin"		; PowerPC/RS6000
    #+(and lucid mips) "mbin"		; DEC
    ;;; These are experimental
    #+gcl "o"
    #+cmu "sparcf"
    #+harlequin-common-lisp "wfasl"
    )

(defun load-pvs-patches ()
  (dolist (pfile (append (collect-pvs-patch-files)
			 (user-pvs-lisp-file)))
    (let* ((bfile (make-pathname :defaults pfile :type *pvs-binary-type*))
	   (compile? (and #+runtime nil
			  (file-exists-p pfile)
			  (or (not (file-exists-p bfile))
			      (compiled-file-older-than-source? pfile bfile)))))
      (multiple-value-bind (ignore error)
	  (ignore-file-errors
	   (cond (compile?
		  (pvs-message "Compiling patch file ~a"
		    (pathname-name pfile))
		  (multiple-value-bind (ignore condition)
		      (ignore-file-errors
		       (values (compile-file pfile)))
		    (declare (ignore ignore))
		    (cond (condition
			   (pvs-message "Compilation error - ~a" condition)
			   (pvs-message "Loading patch file ~a interpreted"
			     (shortname pfile))
			   (load pfile))
			  (t
			   (chmod "ug+w" (namestring bfile))
			   (pvs-message "Compilation complete: loading ~a"
			     (shortname bfile))
			   (load bfile)))))
		 (t (pvs-message "Loading compiled patch file ~a"
		      (shortname bfile))
		    (load bfile))))
	(declare (ignore ignore))
	(if error
	    (pvs-message "Error in loading ~a:~%  ~a"
	      (shortname pfile) error)
	    (pushnew (pathname-name pfile) *pvs-patches-loaded*
		     :test #'string=))))))

(defun collect-pvs-patch-files ()
  (case (ignore-errors (parse-integer
			(environment-variable "PVSPATCHLEVEL")))
    (0 nil)
    (1 (pvs-patch-files-for nil))
    (2 (append (pvs-patch-files-for nil)
	       (pvs-patch-files-for "test")))
    (3 (append (pvs-patch-files-for nil)
	       (pvs-patch-files-for "test")
	       (pvs-patch-files-for "exp")))))

(defun user-pvs-lisp-file ()
  (unless *started-with-minus-q*
    (let ((home-lisp-file (make-pathname :defaults "~/" :name ".pvs" :type "lisp"))
	  (home-fasl-file (make-pathname :defaults "~/" :name ".pvs" :type *pvs-binary-type*)))
      (when (or (file-exists-p home-lisp-file)
		(file-exists-p home-fasl-file))
	(list home-lisp-file)))))

(defun pvs-patch-files-for (ext)
  (let* ((defaults (pathname (format nil "~a/"
			      (environment-variable "PVSPATH"))))
	 (pfile (make-pathname
		 :defaults defaults
		 :name (format nil "patch~d~@[-~a~]~@[~a~]"
			 (major-version) ext (pvs-image-suffix))
		 :type "lisp"))
	 (bfile (make-pathname :defaults pfile :type *pvs-binary-type*)))
    (when (or (file-exists-p pfile)
	      (file-exists-p bfile))
      (list pfile))))

(defun get-pvs-version-information ()
  (list *pvs-version*
	(get-patch-version)
	(when (fboundp 'get-patch-test-version)
	  (get-patch-test-version))
	(when (fboundp 'get-patch-exp-version)
	  (get-patch-exp-version))
	(lisp-implementation-type)
	(lisp-implementation-version)))

(defun pvs-image-suffix ()
  (let* ((lisp (environment-variable "PVSLISP"))
	 (last-char (char lisp (1- (length lisp))))
	 (next-to-last-char (char lisp (- (length lisp) 2))))
    (when (and (alpha-char-p last-char)
	       (digit-char-p next-to-last-char))
      last-char)))

(defun pvs-patch< (p1 p2)
  (let ((name1 (pathname-name p1))
	(name2 (pathname-name p2)))
    (or (string= name1 "patch")
	(and (not (string= name2 "patch"))
	     (let* ((suff1 (subseq name1 5))
		    (suff2 (subseq name2 5))
		    (i1 (parse-integer suff1))
		    (i2 (parse-integer suff2)))
	       (cond ((= i1 i2)
		      (pvs-message "Ambiguous patch order - loading ~a before ~a"
			(if (string< suff1 suff2) name1 name2)
			(if (string< suff1 suff2) name2 name1))
		      (string< suff1 suff2))
		     (t (< i1 i2))))))))

(defun valid-pvs-patch-name (p)
  (let ((name (pathname-name p)))
    (or (string= name "patch")
	(and (string= name "patch" :end1 5)
	     (every #'digit-char-p (subseq name 5))))))


;;; Parsing

(defmethod parse-file ((filename string) &optional forced? no-message?)
  (let* ((file (make-specpath filename))
	 (*current-file* filename)
	 (theories (get-theories file)))
    (cond ((not (file-exists-p file))
	   (unless no-message?
	     (pvs-message "PVS file ~a is not in the current context" filename)))
	  ((and (not forced?)
		(gethash filename *pvs-files*)
		(parsed-file? file))
	   (unless no-message?
	     (pvs-message "~a is already parsed" filename))
	   theories)
	  (*in-checker*
	   (pvs-message "Must exit the prover first"))
	  (*in-evaluator*
	   (pvs-message "Must exit the evaluator first"))
	  ((and (null theories)
		(not forced?)
		(valid-binfile? filename)
		(restore-theories filename))
	   (let ((theories (get-theories filename)))
	     (dolist (th theories)
	       (remove-associated-buffers (id th)))
	     (values theories t)))
	  ((adt-generated-file? filename)
	   (let* ((fe (get-context-file-entry filename))
		  (deps (if fe
			    (ce-dependencies fe)
			    (list (adt-generated-file? filename)))))
	     (when deps
	       (dolist (dep deps)
		 (typecheck-file dep forced? nil nil no-message?)))))
	  (t (let ((fe (get-context-file-entry filename)))
	       (when fe (setf (ce-object-date fe) nil)))
	     (let ((theories (parse-file* filename file theories forced?)))
	       (when (eq forced? 'all)
		 (parse-importchain theories))
	       (dolist (th theories)
		 (remove-associated-buffers (id th)))
	       theories)))))

(defun adt-generated-file? (filename)
  (and (> (length filename) 4)
       (string= (subseq filename (- (length filename) 4)) "_adt")
       (let ((fstring (with-open-file (str (make-specpath filename))
			(read-line str)))
	     (alen (length *adt-generated-string*)))
	 (and (> (length fstring) alen)
	      (string= (subseq fstring 0 alen) *adt-generated-string*)
	      (subseq fstring alen)))))

(defvar *parsed-theories* nil)

(defun parse-importchain (theories)
  (let ((*parsed-theories* nil))
    (parse-importchain* theories)))

(defun parse-importchain* (theories)
  (when theories
    (dolist (thname (get-immediate-usings (car theories)))
      (unless (library thname)
	(let ((th (get-theory thname)))
	  (cond ((null th)
		 (let* ((filename (context-file-of thname))
			(nth (if (and filename
				      (file-exists-p (make-specpath filename)))
				 (parse-file filename t nil)
				 (parse-file thname t nil))))
		   (setq *parsed-theories* (append nth *parsed-theories*))
		   (parse-importchain* nth)))
		((not (memq th *parsed-theories*))
		 (let ((nth (parse-file (filename th) t nil)))
		   (setq *parsed-theories* (append nth *parsed-theories*))
		   (parse-importchain* nth)))))))))
		     
  

(defun valid-binfile? (filename)
  (let ((fe (get-context-file-entry filename)))
    (and fe
	 (ce-object-date fe)
	 (let ((specdate (file-write-date (make-specpath filename)))
	       (bindate (file-write-date (make-binpath filename))))
	   (and bindate
		specdate
		(= bindate (ce-object-date fe))
		(<= specdate bindate))))))

(defun parse-file* (filename file theories forced?)
  ;;(save-context)
  (pvs-message "Parsing ~a" filename)
  (multiple-value-bind (new-theories time)
      (let ((*no-obligations-allowed* t))
	(parse :file file))
    (check-for-theory-clashes new-theories filename)
    ;;(check-import-circularities new-theories)
    (update-parsed-file filename file theories new-theories forced?)
    (pvs-message "~a parsed in ~,2,-3f seconds" filename time)
    #+pvsdebug (assert (every #'(lambda (nth) (get-theory (id nth)))
			      new-theories))
    (mapcar #'(lambda (nth) (get-theory (id nth))) new-theories)))

(defun check-for-theory-clashes (new-theories filename)
  (check-for-duplicate-theories new-theories)
  (check-for-prelude-theory-clashes new-theories)
  (check-for-context-theory-clashes new-theories filename))

(defun check-for-duplicate-theories (new-theories)
  (when (cdr new-theories)
    (let ((dup (car (member (car new-theories) (cdr new-theories)
			    :test #'same-id))))
      (when dup
	(parse-error dup
	  "Theory ~a was declared earlier in this file" (id dup)))
      (check-for-duplicate-theories (cdr new-theories)))))

(defun check-for-prelude-theory-clashes (new-theories)
  (when new-theories
    (let* ((theory (car new-theories))
	   (clash (gethash (id theory) *prelude*)))
      (when clash
	(parse-error theory
	  "~a is a prelude ~a and may not be redefined"
	  (id clash) (if (datatype? clash) "datatype" "theory")))
      (check-for-prelude-theory-clashes (cdr new-theories)))))

(defun check-for-context-theory-clashes (new-theories filename)
  (unless *generating-adt*
    (let ((clashes (collect-theory-clashes new-theories filename)))
      (when clashes
	;; clashes is an assoc list with (new-theory . oldfilename) entries
	(unless (pvs-yes-or-no-p
		 "~d theor~@P clash~:[~;es~] with those in other files - continue? "
		 (length clashes) (length clashes) (eql (length clashes) 1))
	  (parse-error (caar clashes)
	    "Theory ~a has been declared previously in file ~a.pvs"
	    (id (caar clashes)) (cdar clashes)))
	;; At some point, should spit out pvs-info here.
	(dolist (clfname (remove-duplicates (mapcar #'cdr clashes)
			   :test #'string=))
	  (dolist (clth (get-theories clfname))
	    (delete-theory clth))
	  (remhash clfname *pvs-files*)
	  (delete-file-from-context clfname))
	(reset-typecheck-caches)))))

(defun check-import-circularities (theories)
  (let ((*modules-visited* nil))
    (check-import-circularities* theories nil)))

(defun check-import-circularities* (theories chain)
  (unless (null theories)
    (cond ((memq (car theories) chain)
	   (let ((dchain (cons (car theories)
			       (ldiff chain (cdr (memq (car theories)
						       chain)))))
		 (*current-context*
		  (make-instance 'context
		    'theory (car theories))))
	     (type-error (car theories)
	       "Circularity found in importings of theor~@P:~
                ~%  ~{~a~^ -> ~}"
	       (length dchain)
	       (mapcar #'id (nreverse dchain)))))
	  (t (unless (or (library-theory? (car theories))
			 (memq (car theories) *modules-visited*))
	       (push (car theories) *modules-visited*)
	       (let* ((imp-names (get-immediate-using-ids (car theories)))
		      (imp-theories (mapcan #'(lambda (id)
						(let ((th (get-theory id)))
						  (when th (list th))))
				      imp-names)))
		 (check-import-circularities* imp-theories
					      (cons (car theories) chain))))
	     (check-import-circularities* (cdr theories) chain)))))


;;; All-importings (list) walks down the immediate-usings of the list of
;;; theories/datatypes, returning the transitive closure of the
;;; immediate-usings.  This is straight-forward, except in the case where
;;; a theory imports the generated theories of a datatype by importing the
;;; datatype.  Thus we want to substitute the generated theories in place
;;; of the datatype, but only if we are not getting the importings for the
;;; datatype itself.  Thus (all-importings "list") ==> NIL,
;;; (all-importings "list_adt") ==> (#<Theory list>), and (all-importings
;;; "foo") contains list, list_adt, list_adt_map, list_adt_reduce, and
;;; list if foo imports (an instance of) list.

(defmethod all-importings ((theory datatype-or-module))
  (let ((*current-context* (saved-context theory))
	(*current-theory* theory))
    (delete theory (all-importings (list theory)))))

(defmethod all-importings ((list list))
  (let ((*theories-visited* nil))
    (declare (special *theories-visited*))
    (mapc #'all-importings* list)
    (remove-if-not #'datatype-or-module?
      *theories-visited*)))

(defun all-importings* (theory)
  (declare (special *theories-visited*))
  (unless (or (null theory)
	      (memq theory *theories-visited*))
    (push theory *theories-visited*)
    (dolist (ith (get-immediate-usings theory))
      (all-importings* (get-theory ith)))))


(defun update-parsed-file (filename file theories new-theories forced?)
  (handle-deleted-theories filename new-theories)
  (when forced?
    (reset-typecheck-caches))
  (let ((mth (update-parsed-theories filename file theories new-theories
				     forced?)))
    (setf (gethash filename *pvs-files*)
	  (cons (file-write-date file) mth)))
  (update-context filename))

(defun update-parsed-theories (filename file oldtheories new-theories forced?
					&optional result)
  (if (null new-theories)
      (nreverse result)
      (let* ((nth (car new-theories))
	     (oth (find nth oldtheories :test #'same-id))
	     (kept? nil))
	(unless (or (null (get-context-file-entry filename))
		    (= (file-write-date file)
		       (ce-write-date (get-context-file-entry filename))))
	  (dolist (ce (pvs-context-entries))
	    (when (and (member filename (ce-dependencies ce) :test #'string=)
		       (not (gethash (ce-file ce) *pvs-files*)))
	      (setf (ce-write-date ce) 0)
	      (setf (ce-object-date ce) 0)
	      (setq *pvs-context-changed* t))
	    (dolist (te (ce-theories ce))
	      (when (and (memq (id nth) (te-dependencies te))
			 (not (get-theory (te-id te))))
		(dolist (fe (te-formula-info te))
		  (when (memq (fe-status fe)
			      '(proved-complete proved-incomplete))
		    (setf (fe-status fe) 'unchecked)
		    (setq *pvs-context-changed* t)))))))
	(setf (filename nth) filename)
	(if (and oth (memq 'typechecked (status oth)))
	    (let ((diffs (or forced? (compare oth nth))))
	      (cond ((null diffs)
		     (setq kept? t)
		     (copy-lex oth nth))
		    (t (reset-typecheck-caches)
		       (when (module? oth)
			 (dolist (ty (nonempty-types oth))
			   (setf (nonempty? ty) nil)))
		       (reset-proof-statuses oth)
		       (when (typep oth 'recursive-type)
			 (let ((gen (make-specpath (id (adt-theory oth)))))
			   (when
			       #+allegro (file-exists-p gen)
			       #-allegro (probe-file gen)
			     (ignore-errors
			       (chmod "a+w" (namestring gen)))
			     (ignore-file-errors
			      (delete-file (namestring gen))))))
		       (untypecheck-usedbys oth)
		       (setf (gethash (id nth) *pvs-modules*) nth))))
	    ;; Don't need to do anything here, since oth was never typechecked.
	    (setf (gethash (id nth) *pvs-modules*) nth))
	(update-parsed-theories filename file
				(remove oth oldtheories) (cdr new-theories)
				forced?
				(cons (if kept? oth nth) result)))))

(defun untypecheck-usedbys (theory)
  (dolist (tid (find-all-usedbys theory))
    (let ((th (get-theory tid)))
      (reset-proof-statuses th)
      (untypecheck-theory th))))

(defun reset-proof-statuses (theory)
  (invalidate-proofs theory))


;;; collect-theory-clashes takes a list of theories and their associated
;;; filename and checks to see whether any of the theories is associated
;;; with a different filename.  It returns an association list of those
;;; new theories that clash and the file containing the old theory.  It
;;; uses the pvs context to determine the clashes.

(defun collect-theory-clashes (new-theories filename &optional result)
  (if (null new-theories)
      (nreverse result)
      (let ((cfile (context-file-of (id (car new-theories)))))
	(collect-theory-clashes
	 (cdr new-theories)
	 filename
	 (if (or (null cfile)
		 (string= cfile filename))
	     result
	     (cons (cons (car new-theories) cfile) result))))))


(defun remove-associated-buffers (theoryid)
  (pvs-buffer (format nil "~a.tccs" theoryid) nil)
  (pvs-buffer (format nil "~a.lisp" theoryid) nil)
  (pvs-buffer (format nil "~a.ppe" theoryid) nil))


#-(or akcl cmu)
(defmethod parse-file ((filename pathname) &optional forced? no-message?)
  (parse-file (pathname-name filename) forced? no-message?))

#+(or akcl cmu)
(defmethod parse-file (filename &optional forced? no-message?)
  (assert (pathnamep pathname))
  (parse-file (pathname-name filename) forced? no-message?))

(defmethod parse-file ((filename symbol) &optional forced? no-message?)
  (parse-file (string filename) forced? no-message?))

(defmethod parse-file ((filename name) &optional forced? no-message?)
  (parse-file (string (id filename)) forced? no-message?))

(defmethod parse-file ((theory module) &optional forced? no-message?)
  (parse-file (id theory) forced? no-message?))

;(defun ps (theoryname &optional forced?)
;  (parse-file theoryname forced? no-message?))


;;; Typechecking files.

(defun typecheck-file (filename &optional forced? prove-tccs? importchain?
				nomsg?)
  (multiple-value-bind (theories restored?)
      (parse-file filename forced? t)
    (let ((*current-file* filename)
	  (*typechecking-module* nil)
	  (*tc-theories* *tc-theories*))
      (when theories
	(cond ((and (not forced?)
		    theories
		    (every #'(lambda (th)
			       (let ((*current-context* (saved-context th))
				     (*current-theory* th))
				 (typechecked? th)))
			   theories))
	       (unless (or nomsg? restored?)
		 (pvs-message
		     "~a ~:[is already typechecked~;is typechecked~]~a"
		   filename
		   restored?
		   (if (and prove-tccs? (not *in-checker*))
		       " - attempting proofs of TCCs" ""))))
	      (*in-checker*
	       (pvs-message "Must exit the prover first"))
	      (*in-evaluator*
	       (pvs-message "Must exit the evaluator first"))
	      (t (pvs-message "Typechecking ~a" filename)
		 (when forced?
		   (delete-generated-adt-files theories))
		 (typecheck-theories filename theories)
		 (assert (every #'typechecked? theories))
		 (update-context filename)))
	(when prove-tccs?
	  (if *in-checker*
	      (pvs-message
		  "Must exit the prover before running typecheck-prove")
	      (if importchain?
		  (prove-unproved-tccs
		   (delete-duplicates (mapcan #'(lambda (th)
						  (let* ((*current-theory* th)
							 (*current-context* (saved-context th)))
						    (collect-theory-usings th)))
					theories)
				      :test #'eq)
		   t)
		  (prove-unproved-tccs theories))))
	theories))))

(defun delete-generated-adt-files (theories)
  (dolist (th theories)
    (when (datatype? th)
      (let* ((adt-file (concatenate 'string (string (id th)) "_adt"))
	     (adt-path (make-specpath adt-file)))
	(when (file-exists-p adt-path)
	  (let ((sname (shortname adt-path))
		(error (nth-value 1 (ignore-errors (delete-file adt-path)))))
	    (if error
		(pvs-message "Error in removing file ~a:~% ~" sname error)
		(pvs-message "Deleted file ~a" sname))))))))

(defun typecheck-theories (filename theories)
  (let ((all-proofs (read-pvs-file-proofs filename))
	(sorted-theories (sort-theories theories)))
    (check-import-circularities sorted-theories)
    (dolist (theory sorted-theories)
      (let ((start-time (get-internal-real-time))
	    (*current-context* (make-new-context theory))
	    (*current-theory* theory)
	    (*old-tcc-names* nil))
	(dolist (u (get-immediate-context-usings theory))
	  (unless (library u)
	    (get-typechecked-theory u theories)))
	(unless (typechecked? theory)
	  (typecheck theory)
	  #+pvsdebug (assert (typechecked? theory))
	  (restore-from-context filename theory all-proofs)
	  ;;	(when (and *prove-tccs* (module? theory))
	  ;;	  (prove-unproved-tccs (list theory))
	  ;;	  (setf (tccs-tried? theory) t))
	  (setf (filename theory) filename)
	  (when (module? theory)
	    (setf (tcc-info theory)
		  (list (car (tcc-info theory))
			(length (remove-if-not #'(lambda (d)
						   (and (formula-decl? d)
							(eq (kind d) 'TCC)
							(proved? d)))
				  (append (assuming theory) (theory theory))))
			(caddr (tcc-info theory))
			nil)))
	  (let* ((tot (car (tcc-info theory)))
		 (prv (cadr (tcc-info theory)))
		 (mat (caddr (tcc-info theory)))
		 (obl (- tot prv mat))
		 (time (realtime-since start-time)))
	    (if (zerop tot)
		(pvs-message "~a typechecked in ~,2,-3fs: No TCCs generated~
                            ~[~:;; ~:*~d conversion~:p~]~[~:;; ~:*~d warning~:p~]~[~:;; ~:*~d msg~:p~]"
		  (id theory) time
		  (length (conversion-messages theory))
		  (length (warnings theory))
		  (length (info theory)))
		(pvs-message
		    "~a typechecked in ~,2,-3fs: ~d TCC~:p, ~
                   ~d proved, ~d subsumed, ~d unproved~
                   ~[~:;; ~:*~d conversion~:p~]~[~:;; ~:*~d warning~:p~]~[~:;; ~:*~d msg~:p~]"
		  (id theory) time tot prv mat obl
		  (length (conversion-messages theory))
		  (length (warnings theory)) (length (info theory))))))))
    (unless *current-context*
      (setq *current-theory* (car (last theories)))))
  (let* ((*current-theory* (car (last theories)))
	 (*current-context* (saved-context *current-theory*)))
    (let ((dep (assoc filename *circular-file-dependencies* :test #'equal)))
      (when dep
	(setq *circular-file-dependencies*
	      (delete dep *circular-file-dependencies*))))
    (let ((deplist (mapcar #'(lambda (d)
			       (list (id d) (filename d)))
		     (circular-file-dependencies filename))))
      (when deplist
	(pvs-warning
	    "Circularity detected in file dependencies:~%~
           ~{  ~{~a from ~a.pvs~}~^, which imports~%~}~%~
           bin files will not be generated for any of these pvs files."
	  deplist))))
  theories)

(defun prove-unproved-tccs (theories &optional importchain?)
  (read-strategies-files)
  (mapc #'prove-unproved-tccs* theories)
  (let ((tot (reduce #'+ (mapcar #'(lambda (th)
				     (or (car (tcc-info th)) 0))
				 theories)))
	(proved (reduce #'+ (mapcar #'(lambda (th)
					(or (cadr (tcc-info th)) 0))
				    theories)))
	(subsumed (reduce #'+ (mapcar #'(lambda (th)
					  (or (caddr (tcc-info th)) 0))
				      theories)))
	;;(trivial (reduce #'+ (mapcar #'(lambda (th)
	;;				 (or (cadddr (tcc-info th)) 0))
	;;			     theories)))
	)
    (if (zerop tot)
	(pvs-message "File ~a typechecked: No TCCs to prove~a"
	  (filename (car theories)) (if importchain? "on importchain" ""))
	(pvs-message
	    "File ~a typechecked:~a ~d TCCs, ~d proved, ~d subsumed, ~d unproved~
             ~[~:;; ~:*~d warning~:p~]~[~:;; ~:*~d msg~:p~]"
	  (filename (car theories))
	  (if importchain? " importchain has" "")
	  tot proved subsumed
	  (- tot proved subsumed)
	  (reduce #'+ (mapcar #'(lambda (th) (length (warnings th))) theories))
	  (reduce #'+ (mapcar #'(lambda (th) (length (info th))) theories))))))

(defun prove-unproved-tccs* (theory)
  (if (tccs-tried? theory)
      (progn
	(pvs-message "TCCs attempted earlier on ~a" (id theory))
	(update-tcc-info theory (collect-tccs theory)))
      (let ((tccs (collect-tccs theory))
	    (*justifications-changed?* nil))
	(unless (every #'proved? tccs)
	  (let ((*current-context* (or (saved-context theory)
				       (context theory)))
		(*current-theory* theory))
	    (mapc #'(lambda (d)
		      (when (tcc? d)
			(let ((*current-context* (context d)))
			  (prove-tcc d))
			(when (proved? d)
			  (incf (cadr (tcc-info theory))))))
		  (append (assuming theory) (theory theory)))))
	(when *justifications-changed?*
	  (save-all-proofs theory))
	(setf (tccs-tried? theory) t)
	(update-tcc-info theory tccs))))

(defun collect-tccs (theory)
  (remove-if-not #'tcc?
    (append (formals theory)
	    (assuming theory)
	    (theory theory))))

(defun update-tcc-info (theory tccs)
  (setf (car (tcc-info theory)) (+ (length tccs) (caddr (tcc-info theory)))
	(cadr (tcc-info theory)) (length (remove-if-not #'proved? tccs))))

(defun proved? (fdecl)
  (memq (proof-status fdecl)
	'(proved proved-complete proved-incomplete)))

(defun unproved? (formula-decl)
  (not (memq (proof-status formula-decl)
	     '(proved proved-complete proved-incomplete))))

(defmethod tccs-tried? ((adt recursive-type))
  t)

(defun prove-tcc (decl)
  (unless (and (default-proof decl)
	       (proved? decl))
    (unless (default-proof decl)
      (make-default-proof decl (tcc-strategy decl))
      (setq *justifications-changed?* t))
    (let* ((*proving-tcc* 'TCC)
	   (proof (rerun-prove decl)))
      (pvs-message
	  "~:[Unable to prove~;Proved~] ~:[~;TCC ~]~a in ~,2,-3f seconds"
	(eq (status-flag proof) '!) (tcc? decl) (id decl)
	(real-proof-time decl))
      ;; Must return non-NIL if proved, NIL otherwise.
      (if (eq (status-flag proof) '!)
	  (setf (proof-status decl) 'proved)
	  (setf (proof-status decl) 'unfinished))
      (eq (status-flag proof) '!))))

(defun tcc-prove (decl context)
  (let ((*suppress-printing* t)
	(*printproofstate* nil)
	(*proving-tcc* 'TCC));;'TCC to save the proof.
    (prove-decl decl
		:strategy `(then ,(tcc-strategy decl) (fail))
		:context context)))

(defmethod tcc-strategy ((decl tcc-decl))
  (list "" (list (class-name (class-of decl)))))

(defmethod tcc-strategy (decl)
  (declare (ignore decl))
  '(tcc))

(defun sort-theories (theories)
  (let ((usings (mapcar #'(lambda (th)
			    (cons th (get-immediate-using-ids th)))
			theories)))
    (sort-theories* usings)))

(defun sort-theories* (usings &optional sorted)
  (if (null usings)
      sorted
      (let ((th (find-if #'(lambda (th)
			     (not (some #'(lambda (u)
					    (memq (id (car th)) (cdr u)))
					usings)))
		  usings
		  :from-end t)))
	(if th
	    (sort-theories* (remove th usings) (cons (car th) sorted))
	    (let ((theories (mapcar #'(lambda (th) (id (car th))) usings)))
	      (type-error (caar usings)
		"Circularity found in importings of theor~@P:~%  ~{~a~^, ~}"
		(length theories) theories))))))

(defmethod get-immediate-using-ids (theory)
  (mapcan #'(lambda (d)
	      (let ((tn (theory-name d)))
		(unless (library tn)
		  (if (eq (id tn) (id theory))
		      (type-error (theory-name d)
			"Theory ~a may not import itself" (id theory))
		      (list (id tn))))))
    (remove-if-not #'mod-or-using? (all-decls theory))))

(defmethod tcc-info ((d recursive-type))
  '(0 0 0))

(defun tc (modname &optional forced?)
  (typecheck-file modname forced?))

(defun tcp (modname &optional forced?)
  (typecheck-file modname forced? t))


;;; prove-untried commands

(defun prove-untried-importchain (theoryname
				  &optional (strategy '(grind)) tccs? exclude)
  (prove*-formulas-importchain theoryname strategy tccs? exclude 'untried))

(defun prove-untried-pvs-file (filename &optional (strategy '(grind)) tccs?)
  (prove*-formulas-pvs-file filename strategy tccs? 'untried))

(defun prove-untried-theory (theoryname &optional (strategy '(grind))
					tccs? filename)
  (prove*-formulas-theory theoryname strategy tccs? filename 'untried))

;;; prove-formulas commands

(defun prove-formulas-importchain (theoryname
				   &optional (strategy '(grind))
				   also-proved? exclude)
  (prove*-formulas-importchain theoryname strategy
			       also-proved? exclude 'formulas))

(defun prove-formulas-pvs-file (filename
				&optional (strategy '(grind)) also-proved?)
  (prove*-formulas-pvs-file filename strategy also-proved? 'formulas))

(defun prove-formulas-theory (theoryname &optional (strategy '(grind))
					 also-proved? filename)
  (prove*-formulas-theory theoryname strategy also-proved? filename 'formulas))

;;; prove-tccs commands

(defun prove-tccs-importchain (theoryname
			       &optional (strategy '(grind))
			       also-proved? exclude)
  (prove*-formulas-importchain theoryname strategy also-proved? exclude 'tccs))

(defun prove-tccs-pvs-file (filename
			    &optional (strategy '(grind)) also-proved?)
  (prove*-formulas-pvs-file filename strategy also-proved? 'tccs))

(defun prove-tccs-theory (theoryname
			  &optional (strategy '(grind)) also-proved? filename)
  (prove*-formulas-theory theoryname strategy also-proved? filename 'tccs))

;;; The generic prove*-formulas- functions

(defun prove*-formulas-importchain (theoryname
				    &optional (strategy '(grind))
				    flag exclude kind)
  (let ((just `("" ,strategy)))
    (multiple-value-bind (msg subjust)
	(check-edited-justification just)
      (when subjust
	(justification-error subjust just msg)))
    (let ((root-theory (get-typechecked-theory theoryname)))
      (if root-theory
	  (let ((*current-context* (context root-theory))
		(*current-theory* root-theory)
		(imports (remove-if #'(lambda (th)
				       (or (from-prelude? th)
					   (typep th '(or library-datatype
							  library-theory))))
			   (collect-theory-usings theoryname exclude)))
		(total-tried 0)
		(total-proved 0))
	    (dolist (th imports)
	      (multiple-value-bind (tried proved)
		  (prove-formulas th just (get-formula-pred kind flag))
		(incf total-tried tried)
		(incf total-proved proved)))
	    (if (zerop total-tried)
		(pvs-message "No formulas attempted")
		(progn
		  (status-proof-importchain theoryname)
		  (pvs-message "~d formulas attempted, ~d proved"
		    total-tried total-proved))))
	  (pvs-message "Can't find theory ~a in the current context"
	    theoryname)))))

(defun prove*-formulas-pvs-file (filename
				 &optional (strategy '(grind)) flag kind)
  (let ((just `("" ,strategy)))
    (multiple-value-bind (msg subjust)
	(check-edited-justification just)
      (when subjust
	(justification-error subjust just msg)))
    (let ((total-tried 0)
	  (total-proved 0))
      (dolist (theory (typecheck-file filename))
	(multiple-value-bind (tried proved)
	    (prove-formulas theory just (get-formula-pred kind flag))
	  (incf total-tried tried)
	  (incf total-proved proved)))
      (if (zerop total-tried)
	  (pvs-message "No formulas attempted")
	  (progn
	    (status-proof-pvs-file filename)
	    (pvs-message "~d formulas attempted, ~d proved"
	      total-tried total-proved))))))

(defun prove*-formulas-theory (theoryname &optional (strategy '(grind))
					  flag filename kind)
  (when filename
    (typecheck-file filename))
  (let ((just `("" ,strategy)))
    (multiple-value-bind (msg subjust)
	(check-edited-justification just)
      (when subjust
	(justification-error subjust just msg)))
    (let ((theory (get-typechecked-theory theoryname)))
      (when theory
	(multiple-value-bind (total-tried total-proved)
	    (prove-formulas theory just (get-formula-pred kind flag))
	  (if (zerop total-tried)
	      (pvs-message "No formulas attempted")
	      (progn
		(status-proof-theory theory)
		(pvs-message "~d formulas attempted, ~d proved"
		  total-tried total-proved))))))))

(defun prove-formulas (theory just &optional formula-pred)
  (read-strategies-files)
  (let ((save-proofs nil)
	(tried-proofs 0)
	(proved-proofs 0))
    (dolist (fmla (provable-formulas (all-decls theory)))
      (when (funcall formula-pred fmla)
	(let ((orig-just (extract-justification-sexp (justification fmla)))
	      (orig-status (proof-status fmla))
	      (orig-dp (decision-procedure-used fmla))
	      (orig-proof-refers-to (proof-refers-to fmla))
	      (orig-real-time (real-time fmla))
	      (orig-run-time (run-time fmla)))
	  (pvs-message "Proving formula ~a" (id fmla))
	  (incf tried-proofs)
	  (setf (justification fmla) just)
	  (setf (proof-status fmla) nil)
	  (rerun-prove fmla)
	  (cond ((proved? fmla)
		 (pvs-message "~a proved - changing strategy to ~a"
		   (id fmla) just)
		 (setq save-proofs t)
		 (incf proved-proofs)
		 (copy-proofs-to-orphan-file
		  (id theory) (list (cons (id fmla) orig-just))))
		(orig-just
		 (pvs-message "~a unproved - keeping original strategy"
		   (id fmla))
		 (setf (justification fmla) orig-just
		       (proof-status fmla) orig-status
		       (decision-procedure-used fmla) orig-dp
		       (proof-refers-to fmla) orig-proof-refers-to
		       (real-time fmla) orig-real-time
		       (run-time fmla) orig-run-time))
		(t (pvs-message
		       "~a unproved - no current strategy so adding new one"
		     (id fmla))
		   (setq save-proofs t))))))
    (cond (save-proofs
	   (save-all-proofs theory))
	  (tried-proofs
	   (pvs-message "Every attempted formula of theory ~a has an existing proof and failed to prove with the given strategy"
	     (id theory)))
	  (t (pvs-message "No formulas attempted from theory ~a"
	       (id theory))))
    (values tried-proofs proved-proofs)))

(defun get-formula-pred (kind flag)
  (case kind
    (untried (if flag #'formula-without-proof? #'nontcc-without-proof?))
    (formulas (if flag #'nontcc? #'unproved-nontcc?))
    (tccs (if flag #'tcc? #'unproved-tcc?))
    (t (error "get-formula-pred: unknown kind ~a" kind))))

(defun formula-without-proof? (fdecl)
  (null (justification fdecl)))

(defun nontcc-without-proof? (fdecl)
  (and (not (tcc? fdecl))
       (null (justification fdecl))))

(defun nontcc? (fdecl)
  (not (tcc? fdecl)))

(defun unproved-nontcc? (fdecl)
  (and (not (tcc? fdecl))
       (not (proved? fdecl))))

(defun unproved-tcc? (fdecl)
  (and (tcc? fdecl)
       (not (proved? fdecl))))



;;; Prettyprinting

(defun prettyprint-region (filename pos1 &optional (pos2 pos1))
  (parse-file filename nil t)
  (let ((start-reg (car pos1))
	(end-reg (car pos2))
	(*no-comments* nil)
	(*ppmacros* t))
    (dolist (theory (reverse (get-theories filename)))
      (let ((start-theory (line-begin (place theory)))
	    (end-theory (line-end (place theory))))
	(cond ((<= end-theory start-reg) nil) ;theory above the region
	      ((>= start-theory end-reg) nil) ;theory below the region
	      ((and (<= start-reg start-theory)
		    (<= end-theory end-reg)) ;theory contained in region
	       (prettyprint-theory (id theory) filename))
	      (t (prettyprint-decls theory pos1 pos2)))))))

(defun prettyprint-decls (theory pos1 pos2)
  (let ((*no-comments* nil)
	(*show-conversions* nil)
	(*ppmacros* t))
    (mapc #'(lambda (d) (prettyprint-decl d theory))
	  (nreverse
	   (chained-decls-list
	    (remove-if #'(lambda (d)
			   (or (> (car pos1) (line-end (place d)))
			       (> (line-begin (place d)) (car pos2))))
	      (remove-if #'generated-by (theory theory))))))
    (mapc #'(lambda (d) (prettyprint-decl d theory))
	  (nreverse
	   (chained-decls-list
	    (remove-if #'(lambda (d)
			   (or (> (car pos1) (line-end (place d)))
			       (> (line-begin (place d)) (car pos2))))
	      (remove-if #'generated-by (assuming theory))))))))

(defun chained-decls-list (decls &optional ldecls decls-list)
  (if (null decls)
      (if ldecls
	  (nreverse (cons (nreverse ldecls) decls-list))
	  (nreverse decls-list))
      (if (or (null ldecls)
	      (and (chain? (car ldecls))
		   (compatible-chain? (car ldecls) (car decls))))
	  (chained-decls-list (cdr decls)
			      (cons (car decls) ldecls)
			      decls-list)
	  (chained-decls-list (cdr decls)
			      (list (car decls))
			      (cons (nreverse ldecls) decls-list)))))

(defun prettyprint-decl (d theory)
  (let* ((*show-conversions* nil)
	 (place (place (if (consp d) (car d) d)))
	 (indent (col-begin place))
	 (dstr (unpindent d indent :string t))
         (dfinal (string-trim '(#\Space #\Tab #\Newline) dstr))
	 (*ppmacros* t))
    (pvs-modify-buffer (shortname *pvs-context-path*)
                       (filename theory)
                       place dfinal)))

(defun prettyprint-theory (theoryname filename)
  (let ((file (or filename
		  (pvs-file-of theoryname))))
    (when file
      (parse-file file nil t)))
  (let* ((theory (get-parsed?-theory theoryname))
	 (*no-comments* nil)
	 (*show-conversions* nil)
	 (*ppmacros* t))
    (when theory
      (let ((string (unparse theory
		      :string t
		      :char-width *default-char-width*)))
	(pvs-modify-buffer (shortname *pvs-context-path*)
			   (filename theory)
			   (place theory)
			   (string-right-trim '(#\space #\tab #\newline)
					      string))))))

(defun prettyprint-pvs-file (filename)
  (let ((theories (parse-file filename nil t))
	(*no-comments* nil)
	(*show-conversions* nil)
	(*ppmacros* t))
    (pvs-buffer (makesym "~a.pvs" filename)
      (format nil "~{~a~^~2%~}"
	(mapcar #'(lambda (th)
		    (unparse th
		      :string t
		      :char-width *default-char-width*))
		theories))
      t)))

(defun prettyprint-theory-instance (theoryname-string
				    &optional context-theoryname)
  (let* ((context-theory (when context-theoryname
			   (get-typechecked-theory context-theoryname)))
	 (*current-context* (context context-theory))
	 (theoryname (pc-parse theoryname-string 'theory-decl-modname)))
    (when (or (actuals theoryname) (mappings theoryname))
      (let ((*generate-tccs* 'none)
	    (*current-theory* (current-theory))
	    (decl (make-instance 'mod-decl
		    'id (makesym "~a_instance" (id theoryname))
		    'modname theoryname)))
	(typecheck-named-theory* (get-typechecked-theory theoryname)
				 theoryname decl)
	(pvs-buffer (makesym "~a.ppi" (id theoryname))
	  (concatenate 'string
	    (format nil
		"% Theory instance for~%  %~a~%"
	      (unpindent theoryname 2 :string t :comment? t))
	    (unparse (generated-theory decl)
	      :string t :char-width *default-char-width*))
	  t)))))

; (defmethod prettyprint (theory)
;   (let ((*no-comments* nil))
;     (prettyprint (get-parsed-theory theory))))

;(defun pp (theory)
;  (prettyprint theory))

;;; View Theory

(defun prettyprint-expanded (theoryref)
  (let ((*no-comments* nil)
	(*unparse-expanded* t))
    (pvs-buffer (format nil "~a.ppe" theoryref)
      (let* ((theory (get-typechecked-theory theoryref))
	     (thstring (unparse theory
			 :string t
			 :char-width *default-char-width*)))
	(unless (recursive-type? theory)
	  (setf (ppe-form theory) (parse :string thstring)))
	thstring)
      t t)))

(defun ppe (theory)
  (prettyprint-expanded theory))


(defun show-tccs (theoryref &optional unproved-only?)
  (let* ((theory (get-typechecked-theory theoryref))
	 (*no-comments* nil))
    (when theory
      (let* ((*comment-on-proof-status* t)
	     (*no-comments* t)
	     (*unparse-expanded* t)
	     (*pp-new-projection-forms* t)
	     (unparsed-a-tcc? nil)
	     (str (string-trim
		   '(#\Space #\Tab #\Newline)
		   (with-output-to-string (out)
		     (dolist (decl (all-decls theory))
		       (dolist (cmt (cdr (assq decl (tcc-comments theory))))
			 (write cmt :stream out :escape nil)
			 (terpri out) (terpri out))
		       (when (and (tcc? decl)
				  (or (not unproved-only?)
				      (unproved? decl)))
			 (unparse decl :stream out)
			 (terpri out) (terpri out)
			 (setq unparsed-a-tcc? t))))))
	     (buffer (format nil "~a.tccs" (id theory))))
	(cond ((not (string= str ""))
	       (let ((*valid-id-check* nil))
		 (setf (tcc-form theory)
		       (if unparsed-a-tcc?
			   (parse :string str :nt 'theory-part)
			   str)))
	       (pvs-buffer buffer str t t))
	      (t (pvs-message "Theory ~a has no TCCs" theoryref)))))))

(defun show-declaration-tccs (bufname origin line &optional unproved-only?)
  (let* ((decl (get-decl-at-origin bufname origin line))
	 (theory (module decl))
	 (tccs (reverse (remove-if (complement #'tcc?) (generated decl))))
	 ;; Even if tccs is null, there might be tcc comments, so we go on.
	 (*comment-on-proof-status* t)
	 (*no-comments* t)
	 (*unparse-expanded* t)
	 (*pp-new-projection-forms* t)
	 (unparsed-a-tcc? nil)
	 (str (string-trim
	       '(#\Space #\Tab #\Newline)
	       (with-output-to-string (out)
		 (dolist (tcc tccs)
		   (dolist (cmt (cdr (assq tcc (tcc-comments theory))))
		     (write cmt :stream out :escape nil)
		     (terpri out) (terpri out))
		   (when (or (not unproved-only?)
			     (unproved? tcc))
		     (unparse tcc :stream out)
		     (terpri out) (terpri out)
		     (setq unparsed-a-tcc? t)))
		 (dolist (cmt (cdr (assq decl (tcc-comments theory))))
		   (write cmt :stream out :escape nil)
		   (terpri out) (terpri out)))))
	 (theory-decl (format nil "~a.~a" (id theory) (decl-to-declname decl)))
	 (buffer (format nil "~a.~a.tccs" (id theory) (decl-to-declname decl))))
    (cond ((not (string= str ""))
	   (let ((*valid-id-check* nil))
	     (setf (tcc-form decl)
		   (if unparsed-a-tcc?
		       (parse :string str :nt 'theory-part)
		       str)))
	   (pvs-buffer buffer str t t)
	   theory-decl)
	  (t (pvs-message "Declaration ~a.~a has no TCCs"
	       (id theory) (decl-to-declname decl))))))

;;; Given a declaration, returns a declname, used to create the
;;; show-declaration-tccs buffer.  For a declaration with an id, this is
;;; the string of the id itself, if it is the only declaration of the
;;; theory with that id.  If there is more than one, then it is suffixed
;;; with "-D", where D is a number.  For importings, the name is simply
;;; IMPORTING-D, etc.
(defmethod decl-to-declname ((decl declaration))
  (let* ((theory (module decl))
	 (decls (remove-if (complement #'(lambda (d)
					   (and (declaration? d)
						(eq (id d) (id decl)))))
		  (all-decls theory)))
	 (pos (when (cdr decls)
		(position decl decls))))
    (assert decls)
    (assert (or (null (cdr decls)) pos))
    (if pos
	(format nil "~a-~d" (id decl) (1+ pos))
	(string (id decl)))))

(defmethod decl-to-declname ((imp importing))
  (let* ((theory (module imp))
	 (imps (remove-if (complement #'importing?) (all-decls theory)))
	 (pos (position decl imps)))
    (assert pos)
    (format nil "IMPORTING-~d" (1+ pos))))

(defun declname-to-decl (declname theory)
  (let ((decl-and-pos
	 (excl:split-regexp "-" declname)))
    (if (string= (car decl-and-pos) "IMPORTING")
	(let ((pos (parse-integer (cdr decl-and-pos)))
	      (imps (remove-if (complement #'importing? (all-decls theory)))))
	  (nth (1- pos) imps))
	(let* ((declid (intern (car decl-and-pos)))
	       (pos (if (cadr decl-and-pos)
			(1- (parse-integer (cadr decl-and-pos)))
			0))
	       (decls (remove-if (complement
				  #'(lambda (d)
				      (and (declaration? d)
					   (eq (id d) declid))))
			(all-decls theory))))
	  (nth pos decls)))))

(defun tcc? (decl)
  (and (formula-decl? decl)
       (eq (kind decl) 'tcc)))


(defun parsed-file? (filename)
  (let ((file (if (pathnamep filename)
		  filename
		  (make-specpath filename))))
    (eql (parsed-date file)
	 (file-write-date file))))

(defmethod parsed? ((mod datatype-or-module))
  (parsed?* mod))

(defmethod parsed? ((modref modname))
  (parsed?* (get-theory modref)))

(defmethod parsed?* ((mod datatype-or-module))
  (or (from-prelude? mod)
      (and (filename mod)
	   (eql (car (gethash (filename mod) *pvs-files*))
		(file-write-date (make-specpath (filename mod)))))))

(defmethod parsed?* ((mod library-theory))
  (parsed-library-file? mod))

(defmethod parsed?* ((mod library-datatype))
  (parsed-library-file? mod))


#-gcl
(defmethod parsed?* ((path pathname))
  (let ((pdate (parsed-date path))
	(fdate (file-write-date path)))
    (and pdate fdate
	 (eql (parsed-date path)
	      (file-write-date path)))))

#+gcl
(defmethod parsed?* (path)
  (assert (pathnamep path))
  (let ((pdate (parsed-date path))
	(fdate (file-write-date path)))
    (and pdate fdate
	 (eql (parsed-date path)
	      (file-write-date path)))))

(defmethod parsed?* ((x null))
  nil)

(defun typechecked-file? (filename)
  (and (parsed-file? filename)
       (every #'(lambda (m)
		  (member 'typechecked (status m)))
	      (get-theories filename))))


;;; Must be a method, since the slot exists for declarations.

(defmethod typechecked? ((theory datatype-or-module))
  (or *in-checker*
      (and (memq 'typechecked (status theory))
	   (saved-context theory)
	   (let* ((*current-context* (saved-context theory))
		  (*current-theory* theory)
		  (importings (all-importings (list theory))))
	     (every #'(lambda (th)
			(and (parsed? th)
			     (memq 'typechecked (status th))))
		    importings)))))

(defmethod typechecked? ((theory module))
  (and (memq 'typechecked (status theory))
       (saved-context theory)
       (let* ((*current-context* (saved-context theory))
	      (*current-theory* theory)
	      (importings (all-importings (list theory))))
	 (every #'(lambda (th)
		    (and (parsed? th)
			 (memq 'typechecked (status th))))
		importings))))

(defmethod typechecked? ((theoryref string))
  (let ((theory (get-theory (pc-parse theoryref 'modname))))
    (and theory
	 (typechecked? theory))))

(defmethod typechecked? (theoryref)
  (let ((theory (get-theory theoryref)))
    (and theory
	 (typechecked? theory))))

(defmethod typechecked? ((tname modname))
  (let ((theory (get-theory tname)))
    (and theory
	 (typechecked? theory))))

(defmethod typechecked? ((theory library-theory))
  t)

(defmethod typechecked? ((theory library-datatype))
  t)

(defun get-theories (filename)
  (let ((fn (if (pathnamep filename)
		(pathname-name filename)
		filename)))
    (or (cdr (gethash fn *pvs-files*))
	(and (equal fn "prelude")
	     *prelude-theories*))))

(defun tca (theory &optional forced?)
  (typecheckall theory forced?))

(defun typecheckall (theory &optional forced?)
  (typecheck-file theory forced? t))


;;; Proving - entrypoints:
;;;  Emacs               Lisp
;;;  -----               ----
;;;  typecheck-prove   - typecheck-file
;;;  prove             - prove-file-at
;;;  redo-proof        - prove-file-at
;;;  prove-theory      - prove-theory
;;;  prove-pvs-file    - prove-pvs-file
;;;  prove-importchain - prove-usingchain
;;;  prove-proofchain  - prove-proofchain
;;;  install-proof     - install-proof


;;; prove-file-at is called from Emacs for a prove command, in which the
;;; cursor should be on a formula in one of the allowable buffers, which
;;; include the PVS file, a tccs or ppe buffer, the prelude file itself,
;;; or a view-prelude-theory buffer.

(defun prove-file-at (name declname line rerun?
			   &optional origin buffer prelude-offset
			   background? display? unproved?)
  ;; Check for old style input - there was no declname then
  (unless (integerp line)
    (setq unproved? display?
	  display? background?
	  background? prelude-offset
	  prelude-offset buffer
	  buffer origin
	  origin rerun?
	  rerun? line
	  line declname
	  declname nil))
  (let ((*to-emacs* background?))
    (if (or *in-checker* *in-evaluator*)
	(pvs-message "Must exit the prover/evaluator first")
	(multiple-value-bind (fdecl place)
	    (formula-decl-to-prove name declname line origin unproved?)
	  (if (and rerun?
		   fdecl
		   (null (justification fdecl)))
	      (pvs-message "Formula ~a has no proof to rerun." (id fdecl))
	      (if fdecl
		  (let ((*current-context* (context fdecl))
			(*current-theory* (module fdecl))
			(*current-system* (if (member origin '("tccs" "ppe"))
					      'pvs
					      (intern origin)))
			(*start-proof-display* display?)
			(ojust (extract-justification-sexp
				(justification fdecl)))
			(decision-procedure (decision-procedure-used fdecl))
			(*justifications-changed?* nil))
		    (read-strategies-files)
		    (let ((proof (cond (background?
					(pvs-prove-decl fdecl t))
				       (t (auto-save-proof-setup fdecl)
					  (prove fdecl
						 :strategy
						 (when rerun? '(rerun)))))))
		      (when (typep proof 'proofstate)
			(setq *last-proof* proof)))
		    (unless (or background?
				(null (default-proof fdecl)))
		      (setf (interactive? (default-proof fdecl)) t))
		    ;; Save the proof if it is different.
		    (unless (or (equal origin "prelude")
				(from-prelude? fdecl))
		      (when (or *justifications-changed?*
				(not (equal ojust
					    (extract-justification-sexp
					     (justification fdecl))))
				(not (eq (decision-procedure-used fdecl)
					 decision-procedure)))
			(save-all-proofs *current-theory*))
		      ;; If the proof status has changed, update the context.
		      (update-context-proof-status fdecl))
		    (remove-auto-save-proof-file)
		    (let ((*to-emacs* t))
		      (pvs-locate buffer fdecl
				  (if prelude-offset
				      (vector (- (line-begin place) prelude-offset)
					      (col-begin place)
					      (- (line-end place) prelude-offset)
					      (col-end place))
				      place))))))))))

(deftype unproved-formula-decl () '(and formula-decl (satisfies unproved?)))

(defun formula-decl-to-prove (name declname line origin &optional unproved?)
  (if (and (member origin '("ppe" "tccs") :test #'string=)
	   (not (get-theory name)))
      (pvs-message "~a is not typechecked" name)
      (case (intern (string-downcase origin))
	(ppe (let* ((theories (ppe-form (get-theory name)))
		    (typespec (if unproved?
				  'unproved-formula-decl
				  'formula-decl))
		    (decl (get-decl-at line typespec theories)))
	       (values (find-if #'(lambda (d)
				    (and (formula-decl? d)
					 (eq (id d) (id decl))))
			 (all-decls (get-theory name)))
		       (place decl))))
	(tccs (let* ((theory (get-theory name))
		     (decls
		      (if declname
			  (tcc-form (declname-to-decl declname theory))
			  (tcc-form theory)))
		     (decl (find-if #'(lambda (d)
					(and (>= (line-end (place d)) line)
					     (or (null unproved?)
						 (unproved? d))))
			     decls)))
		(values (find-if #'(lambda (d) (and (eq (module d) theory)
						    (formula-decl? d)
						    (eq (id d) (id decl))))
			  (all-decls theory))
			(place decl))))
	(prelude (let* ((theory (get-theory name))
			(theories (if (and theory (generated-by theory))
				      (list theory)
				      (remove-if #'generated-by
					*prelude-theories*)))
			(typespec (if unproved?
				      'unproved-formula-decl
				      'formula-decl))
			(decl (get-decl-at line typespec theories)))
		   (values decl (place decl))))
	(t (if (pathname-directory name)
	       (let* ((lpath (get-library-reference
			      (namestring (make-pathname
					   :directory
					   (pathname-directory name)))))
		      (files&theories
		       (or (gethash lpath *prelude-libraries*)
			   (gethash lpath *imported-libraries*))))
		 (if files&theories
		     (let* ((name (pathname-name name))
			    (theories (cdr (gethash name
						    (car files&theories))))
			    (typespec (if unproved?
					  'unproved-formula-decl
					  'formula-decl))
			    (decl (get-decl-at line typespec theories)))
		       (values decl (when decl (place decl))))
		     (pvs-message "Library ~a is not imported" name)))
	       (let* ((theories (typecheck-file name nil nil nil t))
		  (typespec (if unproved?
				'unproved-formula-decl
				'formula-decl))
		  (decl (get-decl-at line typespec theories)))
		 (values decl (when decl (place decl)))))))))


;;; This function is invoked from Emacs by pvs-prove-formula.  It provides
;;; an answer as to whether the proof should be rerun.  It takes a file, a
;;; line number, an optional origin, and an optional flag indicating
;;; whther it should try to rerun.  It returns T if the proof should be
;;; rerun, NO if the proof should not be rerun, and NIL if the formula
;;; declaration could not be found.

(defun rerun-proof-at? (name declname line &optional origin rerun? unproved?)
  (let ((fdecl (formula-decl-to-prove name declname line origin unproved?)))
    (cond ((and fdecl rerun?)
	   (if (justification fdecl)
	       rerun?
	       (pvs-message "Formula has no associated proof")))
	  (fdecl
	   (if (justification fdecl)
	       (and (or (unproved? fdecl)
			(pvs-y-or-n-p-with-timeout
			 "Formula has already been proved: try again? "))
		    (if (pvs-y-or-n-p-with-timeout "Rerun Existing proof? ")
			t 'no))
	       'no))
	  (unproved? (pvs-message "No more unproved formulas below"))
	  (t (pvs-message "Not at a formula declaration")))))

(defun prove-formula (modname formname rerun?)
  (declare (ignore modname))
  (let* ((fid (intern formname))
	 (fdecl (find-if #'(lambda (d) (and (formula-decl? d)
					    (eq (id d) fid)))
		  (all-decls (current-theory))))
	 (strat (when rerun? '(rerun))))
    (cond (fdecl
	   (setq *current-theory* (slot-value fdecl 'module))
	   (prove formname :strategy strat))
	  (t (pvs-message "Formula ~a not found" formname)))))

(defun rerun-proof-of? (modname formname)
  (setq *current-theory* (get-theory modname))
  (let* ((fid (intern formname))
	 (fdecl (find-if #'(lambda (d) (and (formula-decl? d)
					    (eq (id d) fid)))
		  (all-decls (current-theory)))))
    (and fdecl
	 (justification fdecl)
	 (pvs-y-or-n-p "Rerun Existing proof? "))))

(defun prove-next-unproved-formula (name declname line rerun?
					 &optional origin buffer prelude-offset
					 background? display?)
  (prove-file-at name declname line rerun? origin buffer prelude-offset
		 background? display? t))


;;; Non-interactive Proving

(defun prove-theory (theoryname &optional retry? filename use-default-dp?)
  (when filename
    (typecheck-file filename))
  (let ((theory (get-typechecked-theory theoryname)))
    (when theory
      (prove-theories theoryname (list theory) retry? use-default-dp?)
      (status-proof-theory theoryname))))


(defun prove-pvs-file (file retry? &optional use-default-dp?)
  (let ((theories (typecheck-file file))
	(*use-default-dp?* use-default-dp?))
    (prove-theories file theories retry? use-default-dp?)
    (status-proof-pvs-file file)))

(defun prove-pvs-theories (theory-names retry? &optional use-default-dp?)
  (when theory-names
    (let ((theories (mapcar #'get-typechecked-theory theory-names))
	  (*use-default-dp?* use-default-dp?))
      (prove-theories "" theories retry? use-default-dp?)
      (status-proof-theories theories))))

(defun prove-usingchain (theoryname retry? &optional exclude use-default-dp?)
  (let ((theory (get-typechecked-theory theoryname))
	(*use-default-dp?* use-default-dp?))
    (when theory
      (let ((*current-context* (context theory))
	    (*current-theory* theory))
	(prove-theories theoryname
			(remove-if #'(lambda (th)
				       (or (from-prelude? th)
					   (typep th '(or library-datatype
							  library-theory))))
			  (collect-theory-usings theoryname exclude))
			retry?
			use-default-dp?)))
    (status-proof-importchain theoryname)))


(defun prove-proofchain (filename declname line origin retry?
				  &optional use-default-dp?)
  (let ((fdecl (formula-decl-to-prove filename declname line origin)))
    (cond ((null fdecl)
	   (pvs-message "Unable to find formula declaration"))
	  ((null (justification fdecl))
	   (pvs-message "~a has no proof" (id fdecl)))
	  (t (let ((*use-default-dp?* use-default-dp?))
	       (prove-proofchain-decl fdecl retry?))))))

(defun prove-proofchain-decl (fdecl retry?)
  (let ((decls-tried nil) (total 0) (proved 0) (unfin 0)
	(realtime 0) (runtime 0))
    (read-strategies-files)
    (labels ((ppd (decl)
	       (unless (memq decl decls-tried)
		 (let ((*justifications-changed?* nil))
		   (push decl decls-tried)
		   (incf total)
		   (pvs-prove-decl decl retry?)
		   (incf realtime (or (real-proof-time decl) 0))
		   (incf runtime (or (run-proof-time decl) 0))
		   (if (unproved? decl) (incf unfin) (incf proved))
		   (when *justifications-changed?*
		     (save-all-proofs (module decl))))
		 (when (justification decl)
		   (ppds (provable-formulas (get-proofchain decl))))))
	     (ppds (decls)
	       (when decls
		 (ppd (car decls))
		 (ppds (cdr decls)))))
      (ppd fdecl))
    (pvs-buffer "PVS Status"
      (with-output-to-string (out)
	(format out "~2%Proof summary for proofchain for ~a.~a"
	  (id (module fdecl)) (id fdecl))
	(let* ((maxtime (reduce #'max decls-tried
				:key #'(lambda (d)
					 (or (run-proof-time d) 0))
				:initial-value 0))
	       (statuslength 20)
	       (dplength (+ (apply #'max
			      (mapcar #'(lambda (x) (length (string x)))
				*decision-procedures*))
			    2))
	       (timelength (length (format nil "~,2f" maxtime)))
	       (idlength (- 79 4 statuslength dplength timelength 4)))
	  (dolist (decl decls-tried)
	    (format out "~%    ~v,1,0,'.a~19a [~a](~a s)"
	      idlength
	      (id decl)
	      (proof-status-string decl)
	      (if (justification decl)
		  (decision-procedure-used decl)
		  "Untried")
	      (if (run-proof-time decl)
		  (format nil "~v,2f" timelength (run-proof-time decl))
		  (format nil "~v<n/a~>" timelength))))
	  (format out "~%    Totals: ~d formulas, ~d attempted, ~d succeeded ~
                       (~,2,-3f s)"
	    total (+ proved unfin) proved runtime)))
      t)))

(defun pvs-prove-decl (decl retry?)
  (setq *current-theory* (module decl))
  (cond ((and (or (justification decl)
		  (eq (kind decl) 'tcc))
	      (or retry?
		  (unproved? decl)))
	 (let ((*rerunning-proof* (format nil "Proving ~a.~a"
				    (id *current-theory*) (id decl)))
	       (*rerunning-proof-message-time* (get-internal-real-time)))
	   (setf (proof-status decl) 'unproved)
	   (cond ((justification decl)
		  (pvs-message "Rerunning proof of ~a" (id decl))
		  (let ((pstat (rerun-prove decl)))
		    (pvs-message
			"~a ~aproved in ~,2,-3f real, ~,2,-3f cpu seconds"
		      (id decl) (if (unproved? decl) "un" "")
		      (real-proof-time decl) (run-proof-time decl))
		    (when (eq (proof-status decl) 'unproved)
		      (setf (proof-status decl) 'unfinished))
		    (update-context-proof-status decl)
		    pstat))
		 (t (pvs-message "Proving ~a..." (id decl))
		    (prove-tcc decl)))))
	((or (justification decl)
	     (not (unproved? decl)))
	 (pvs-message "~a is already proved" (id decl))
	 nil)
	(t (pvs-message "~a has no proof" (id decl))
	   nil)))


(defun get-proofchain (fdecl)
  (union (refers-to fdecl) (proof-refers-to fdecl)))

(defun prove-theories (name theories retry? &optional use-default-dp?)
  (let ((total 0) (proved 0) (realtime 0) (runtime 0)
	(*use-default-dp?* use-default-dp?))
    (read-strategies-files)
    (dolist (theory theories)
      (let ((*justifications-changed?* nil))
	(dolist (d (provable-formulas theory))
	  (incf total)
	  (pvs-prove-decl d retry?)
	  (when (real-proof-time d)
	    (incf realtime (real-proof-time d)))
	  (when (run-proof-time d)
	    (incf runtime (run-proof-time d)))
	  (unless (unproved? d) (incf proved)))
	(when *justifications-changed?*
	  (save-all-proofs *current-theory*))))
    (pvs-message
	"~a: ~d proofs attempted, ~d proved in ~,2,-3f real, ~,2,-3f cpu seconds"
      name total proved realtime runtime)))



;;; Editing proofs

;(defun pprint-proof-script (s list)
;  (pprint-logical-block (s list :prefix "(" :suffix ")")
;    (pprint-exit-if-list-exhausted)
;    (loop (write (pprint-pop) :stream s)
;	  (pprint-exit-if-list-exhausted)
;	  (write-char #\space s)
;	  (write (pprint-pop) :stream s)
;	  (pprint-newline :linear s))))

(defun edit-proof-at (filename declname line origin buffer
			       prelude-offset full-label)
  (multiple-value-bind (fdecl place)
      (formula-decl-to-prove filename declname line origin)
    (when fdecl
      (setq *edit-proof-info* (list fdecl place buffer prelude-offset)))
    (cond ((and fdecl (justification fdecl))
	   ;;(setq *current-theory* (module fdecl))
	   (pvs-buffer "Proof"
	     (with-output-to-string (out)
	       (format out ";;; Proof ~a for formula ~a.~a~%"
		 (id (default-proof fdecl)) (id (module fdecl)) (id fdecl))
	       (format out
		   ";;; developed with ~a decision procedures~%"
		 (decision-procedure-used fdecl))
	       (write (editable-justification (justification fdecl)
					      nil nil (when full-label ""))
		      :stream out :pretty t :escape t
		      :level nil :length nil
		      :pprint-dispatch *proof-script-pprint-dispatch*))
	     'popto))
	  (fdecl
	   (pvs-buffer "Proof" " " 'popto)
	   (pvs-message "Formula ~a has no proof to edit"
	     (id fdecl)))
	  (t (pvs-message "Unable to find formula declaration")))))


(defun install-proof (tmpfilename name declname line origin buffer prelude-offset)
  ;; If the origin is supplied, simply install the proof.  Otherwise the
  ;; proof is being installed from the Proof buffer, and the declaration
  ;; is gotten from *edit-proof-info*, in this case ask before installing.
  (when (or origin
	    (if *edit-proof-info*
		(prog1 (pvs-y-or-n-p "Install proof on formula ~a? "
				     (id (car *edit-proof-info*)))
		  (pvs-message ""))
		(pvs-message "No proof is being edited.")))
    (let ((sexpr (ignore-errors (with-open-file (in tmpfilename) (read in)))))
      (unless (listp sexpr)
	(justification-error sexpr sexpr "Proof must be a list"))
      (multiple-value-bind (msg subexpr)
	  (check-edited-justification sexpr)
	(if subexpr
	    (justification-error subexpr sexpr msg)
	    (let ((just (revert-justification
			 (complete-checkpointed-proof sexpr))))
	      (multiple-value-bind (fdecl place)
		  (if origin
		      (formula-decl-to-prove name declname line origin)
		      (car *edit-proof-info*))
		(when (and origin fdecl)
		  (setq *edit-proof-info*
			(list fdecl place buffer prelude-offset)))
		(cond ((null fdecl)
		       (pvs-message "Proof is not associated with a formula"))
		      ((equal (extract-justification-sexp (justification fdecl))
			      just)
		       (pvs-message "Proof was not changed")
		       t)
		      ((some #'(lambda (prinfo)
				 (equal (script prinfo) just))
			     (proofs fdecl))
		       (let ((prinfo (find #'(lambda (prinfo)
					       (equal (script prinfo) just))
					   (proofs fdecl))))
			 (setf (default-proof fdecl) prinfo)
			 (unless (from-prelude? (module fdecl))
			     (save-all-proofs (module fdecl)))
			 (pvs-message "Proof installed on ~a as ~a"
			   (id fdecl) (id prinfo))
			 t))
		      (t (let ((prinfo (make-proof-info
					just
					(next-proof-id fdecl)
					(when (default-proof
						(car *edit-proof-info*))
					  (description
					   (default-proof
					     (car *edit-proof-info*)))))))
			   (push prinfo (proofs fdecl))
			   (setf (default-proof fdecl) prinfo)
			   (unless (from-prelude? (module fdecl))
			     (save-all-proofs (module fdecl)))
			   (pvs-message "Proof installed on ~a as ~a"
			     (id fdecl) (id prinfo)))
			 t)))))))))


;;; Called from install-proof by Emacs while in an edit proof buffer.  The
;;; *edit-proof-info* variable must have previously been set by
;;; edit-proof-at.

(defun prove-proof-at (line step? display?)
  (declare (ignore line))
  (let* ((fdecl (car *edit-proof-info*))
	 (*current-theory* (module fdecl)))
    (read-strategies-files)
    (auto-save-proof-setup fdecl)
    (let ((*start-proof-display* display?))    
      (setq *last-proof*
	    (if step?
		(prove (id fdecl))
		(prove (id fdecl) :strategy '(rerun)))))
    ;; Save the proof.
    (unless (from-prelude? fdecl)
      (save-all-proofs *current-theory*)
      ;; If the proof status has changed, update the context.
      (update-context-proof-status fdecl))
    (when (typep fdecl 'tcc-decl)
      (update-tcc-info (module fdecl) (collect-tccs (module fdecl))))
    (remove-auto-save-proof-file)
    (when (default-proof fdecl)
      (setf (interactive? (default-proof fdecl)) t))
    (let* ((*to-emacs* t)
	   (place (second *edit-proof-info*))
	   (buffer (third *edit-proof-info*))
	   (prelude-offset (fourth *edit-proof-info*)))
      (pvs-locate buffer fdecl
		  (if prelude-offset
		      (vector (- (line-begin place) prelude-offset)
			      (col-begin place)
			      (- (line-end place) prelude-offset)
			      (col-end place))
		      place)))))
		   

(defun remove-proof-at (name declname line origin)
  (let ((fdecl (formula-decl-to-prove name declname line origin)))
    (cond ((and fdecl (default-proof fdecl))
	   (let ((prf (default-proof fdecl)))
	     (setf (proofs fdecl) (delete prf (proofs fdecl)))
	     (setf (default-proof fdecl) (car (proofs fdecl)))
	     (when (tcc? fdecl)
	       (setf (tccs-tried? (module fdecl)) nil))
	     (update-context-proof-status fdecl)
	     (save-all-proofs *current-theory*)
	     (pvs-message "Proof ~a removed from ~a"
	       (id prf) (id fdecl))))
	  (fdecl
	   (pvs-message "Formula ~a has no proof to remove" (id fdecl)))
	  (t (pvs-message "Unable to find formula declaration")))))

(defun postpone-occurs-in-justification? (justification)
  (postpone-in? (editable-justification justification)))

(defun postpone-in? (list)
  (and (consp list)
       (or (member '(postpone) list :test #'equal)
	   (postpone-in? (car list))
	   (postpone-in? (cdr list)))))

(defun justification-error (subexpr sexpr msg)
  (let ((pos (or (ignore-errors (matching-position subexpr sexpr "" 0))
		 0))
	(*from-buffer* "Proof"))
    (pvs-error "Proof Syntax Error" (or msg "Proof syntax error")
	       "Proof" (pos-to-place pos sexpr))
    nil))

(defun pos-to-place (pos sexpr)
  (declare (ignore pos sexpr))
  (let ((row 0) (col 0))
;    (dotimes (i pos)
;      (cond ((char= (aref string i) #\newline)
;	     (incf row)
;	     (setq col 0))
;	    (t (incf col))))
    (vector row col)))


(defun matching-position (subexpr expr string pos)
  (if (eq subexpr expr)
      pos
      (and (consp expr)
	   (let ((spos (1+ pos)))
	     (dolist (e expr)
	       (let ((mpos (matching-position subexpr e string spos)))
		 (when mpos (return mpos))
		 (multiple-value-bind (subex npos)
		     (read-from-string (subseq string spos))
		   (assert (equal subex e))
		   (setq spos (+ spos npos
				 (position-if-not
				  #'(lambda (ch)
				      (member ch '(#\space #\tab #\newline)))
				  (subseq string (+ npos spos))))))))))))
      

;;;---------------------------------------------
;;; Theory Commands

;;; Find Theory is done completely in Emacs

;;; New Theory

(defun new-theory (modname)
  ;;(save-some-modules)
  (let ((id (if (stringp modname) (intern modname) modname)))
    (if (gethash id *pvs-modules*)
	(progn ;(pvs-message "Theory already exists")
	       nil)
	(namestring (make-pathname :name modname :type "pvs"
				   :defaults *pvs-context-path*)))))


;;; Delete Theory

(defun delete-pvs-file (filename &optional delete-file?)
  (let ((theories (get-context-theory-names filename)))
    (when delete-file?
      (mapc #'copy-theory-proofs-to-orphan-file theories))
    (dolist (tid theories)
      (let ((theory (get-theory tid)))
	(when theory
	  (when (typechecked? theory)
	    (untypecheck-theory theory))
	  (remhash tid *pvs-modules*))))
    (remhash filename *pvs-files*)
    (delete-file-from-context filename))
  (when delete-file?
    (delete-file (make-specpath filename)))
  (if delete-file?
      (pvs-message "~a has been deleted" filename)
      (pvs-message "~a has been removed from the context" filename)))

(defun delete-theory (theoryref)
  (let ((theory (gethash (ref-to-id theoryref) *pvs-modules*)))
    (when theory
      (copy-theory-proofs-to-orphan-file theoryref)
      (untypecheck-usedbys theory)
      (when (typechecked? theory)
	(untypecheck-theory theory))
      (remhash (id theory) *pvs-modules*)
      (setf (gethash (filename theory) *pvs-files*)
	    (remove theory (gethash (filename theory) *pvs-files*))))))


;;; List Theories

(defun lt (&optional context)
  (list-theories context))

(defun list-theories (&optional context)
  (if (or (null context)
	  (file-equal context *pvs-context-path*))
      (let ((theories nil))
	(maphash #'(lambda (id mod)
		     (declare (ignore mod))
		     (push (string id) theories))
		 *pvs-modules*)
	(sort theories #'string<))
      (let ((path (make-pathname :defaults context
				 :name "context" :type "cxt")))
	(if (file-exists-p path)
	    (let ((ctx (with-open-file (in path) (read in))))
	      (if (and (consp ctx)
		       (equal (car ctx) *pvs-version*))
		  (mapcar #'(lambda (m) (string (car m))) (cdr ctx))
		  (if (pvs-y-or-n-p
		       "Context from an earlier version - list all theory files? ")
		      (mapcar #'pathname-name
			      (directory (make-pathname :defaults path
							:name :wild
							:type "pvs"))))))
	    (if (pvs-y-or-n-p "No context - list all theory files? ")
		(mapcar #'pathname-name (directory path)))))))


;;;---------------------------------------------
;;; Environment Commands

;;; Help

;;; Suspend Pvs - done in Emacs

;;; Exit Pvs

#+lucid
(unless (fboundp 'bye)
  (setf (symbol-function 'bye) (symbol-function 'quit)))

#+excl
(defun bye ()
  (excl:exit))

#+harlequin-common-lisp
(defun bye ()
  (system::bye))

(defun quit (&optional status)
  (declare (ignore status))
  (when (y-or-n-p "Do you really want to kill the PVS process? ")
    (bye)))

(defun exit-pvs ()
  (save-context)
  (bye))

;;; PVS Version

(defun pvs-version ()
  (pvs-message "PVS Version ~a" *pvs-version*))


;;; help-prover

(defun help-prover (&optional name)
  (let ((rule (if (stringp name) (intern (string-downcase name)) '*))
	(*disable-gc-printout* t))
    (pvs-buffer "Prover Help"
      (with-output-to-string (*standard-output*)
	(funcall (help-rule-fun rule) nil))
      'temp t)))

;;; Misc functions

;;; get-parsed-theory gets the parsed theory, but will not save the context
;;; (last argument to parse-file)

(defun get-parsed-theory (theoryref)
  (let ((mod (get-theory theoryref)))
    (cond ((and mod (gethash (id mod) *prelude*))
	   mod)
	  ((and mod (parsed? mod))
	   mod)
	  ((and (name? theoryref)
		(library theoryref))
	   (get-parsed-library-theory theoryref))
	  ((and mod (filename mod))
	   (parse-file (filename mod) nil t)
	   (get-theory theoryref))
	  (t (let ((filename (context-file-of theoryref)))
	       (if (and filename (file-exists-p (make-specpath filename)))
		   (parse-file filename nil nil)
		   (if (file-exists-p (make-specpath theoryref))
		       (parse-file theoryref nil nil)
		       (let ((file
			      (look-for-theory-in-directory-files theoryref)))
			 (if file
			     (parse-file file nil nil)
			     (parse-file theoryref nil nil)))))
	       (let ((pmod (get-theory theoryref)))
		 (or pmod
		     (type-error theoryref
		        "Can't find file for theory ~a" theoryref))))))))

(defun look-for-theory-in-directory-files (theoryref)
  (let ((pvs-files (directory "*.pvs"))
	(files-with-clashes nil)
	(files-with-theoryref nil))
    (dolist (file pvs-files)
      (let ((fname (pathname-name file)))
	(unless (gethash fname *pvs-files*)
	  (let ((theories (ignore-errors (with-no-parse-errors
					  (parse :file file)))))
	    (when (member (ref-to-id theoryref) theories :key #'id)
	      ;; Make sure we're not introducing a name clash
	      ;; E.g., file1 has theories th1 and th2
	      ;;       file2 has theories th2 and th3
	      ;; and we're looking for th3 from file1.
	      (if (some #'(lambda (th)
			    (gethash (id th) *pvs-modules*))
			theories)
		  (push fname files-with-clashes)
		  (push fname files-with-theoryref)))))))
    (cond ((null files-with-theoryref)
	   (when files-with-clashes
	     (type-error theoryref
	       "Theory ~a appears in other files:~%  ~{~a~^, ~}~
              ~%but other theories in those files clash with current theories."
	       theoryref files-with-clashes)))
	  ((cdr files-with-theoryref)
	   (type-error theoryref
	     "Theory ~a appears in more than one file:~%  ~{~a~^, ~}~
              ~%pick one and typecheck it."
	     theoryref files-with-theoryref))
	  (t (car files-with-theoryref)))))

(defun get-parsed-library-theory (theoryname)
  (load-imported-library (library theoryname) theoryname))

(defun get-parsed?-theory (theoryref)
  (let ((theory (get-theory theoryref)))
    (cond ((null theory)
	   (pvs-message "~a is unknown in this context." theoryref))
	  ((gethash (id theory) *prelude*)
	   theory)
	  ((parsed? theory)
	   theory)
	  (t (pvs-message "~a has not been parsed." theoryref)))))

(defun get-typechecked-theory (theoryref &optional theories)
  (or (and (or *in-checker*
	       *generating-adt*)
	   (get-theory theoryref))
      (let ((theory (get-parsed-theory theoryref)))
	(when theory
	  (unless (or *in-checker*
		      (typechecked? theory)
		      (memq theory theories))
	    (let ((*generating-adt* nil))
	      (typecheck-file (filename theory)))))
	theory)))

(defun parsed-date (filename)
  (car (gethash (pathname-name filename) *pvs-files*)))

(defun reset-parsed-date (filename)
  (let ((path (make-specpath filename)))
    (setf (car (gethash filename *pvs-files*))
	  (file-write-date path))))

(defun find-theory-at (file line)
  (let ((theories (get-theories file)))
    (when theories
      (find-theory-at* theories line))))

(defun find-theory-at* (theories line)
  (when theories
    (if (and (<= (starting-row (place (car theories))) line)
	     (<= line (ending-row (place (car theories)))))
	(car theories)
	(find-theory-at* (cdr theories) line))))

(defun get-decl-at (line class theories)
  (when theories
    (let* ((theory (car theories))
	   (decl (find-if #'(lambda (d)
			      (and (typep d class)
				   (place d)
				   (>= (line-end (place d)) line)))
			  (append (assuming theory)
				  (theory theory)))))
      (if decl
	  (values decl theory)
	  (get-decl-at line class (cdr theories))))))

;(defun get-decl-at (line class mod &optional visible-only?)
;  (find-if #'(lambda (d)
;	       (and (if (listp class)
;			(some@ #'(lambda (c) (typep d c)) class)
;			(typep d class))
;		    (or (not (generated-by d)) (not visible-only?))
;		    (>= (car (location d)) line)))
;	   (theory mod)))

(defun get-decls (ref)
  (let ((decls nil))
    (maphash #'(lambda (mid mod)
		 (declare (ignore mid))
		 (when (module? mod)
		   (setq decls
			 (append (remove-if-not
				     #'(lambda (d)
					 (and (declaration? d)
					      (eq (id d) (ref-to-id ref))))
				   (all-decls mod))
				 decls))))
	     *pvs-modules*)
    (maphash #'(lambda (mid mod)
		 (declare (ignore mid))
		 (when (module? mod)
		   (setq decls
			 (append (remove-if-not
				     #'(lambda (d)
					 (and (declaration? d)
					      (eq (id d) (ref-to-id ref))))
				   (all-decls mod))
				 decls))))
	     *prelude*)
    (delete-duplicates decls :test #'eq)))


;;; Returns a list of theories in the transitive closure of the usings
;;; of the specified theoryname.  The theory must be typechecked.

(defun collect-theory-usings (theoryname &optional exclude)
  (let ((theory (get-theory theoryname)))
    (if theory
	(if (typechecked? theory)
	    (let* ((excl-theories (mapcar #'get-theory exclude))
		   (*modules-visited* excl-theories))
	      (collect-theory-usings* theory)
	      (nreverse (remove-if #'(lambda (x) (memq x excl-theories))
			  *modules-visited*)))
	    (pvs-message "Theory ~a has not been typechecked" theoryname))
	(if (get-context-theory-entry theoryname)
	    (pvs-message "Theory ~a has not been parsed" theoryname)
	    (pvs-message "Theory ~a is not in the current context"
	      theoryname)))))

(defun collect-theory-usings* (theory)
  (unless (memq theory *modules-visited*)
    (let ((*current-theory* theory))
      (push theory *modules-visited*)
      (dolist (use (get-immediate-usings theory))
	(let ((th (get-theory use)))
	  (when th
	    (collect-theory-usings* th)))))))


;;; Returns the filenames in the transitive closure of the usings of the
;;; specified filename.  The filenames are strings without the directory
;;; or extension.

(defun collect-file-usings (filename)
  (let ((theories (get-theories filename)))
    (if theories
	(let ((*modules-visited* nil))
	  (mapc #'collect-theory-usings* theories)
	  (remove-duplicates
	   (mapcar #'filename (nreverse *modules-visited*))
	   :from-end t :test #'equal))
	(pvs-message "File ~a.pvs is not known in this context."
	  filename))))

(defun file-and-place (theoryname)
  (let ((theory (get-theory theoryname)))
    (when theory 
      (cons (shortname (make-specpath (filename theory)))
	    (when (parsed? theory) (place-list (place theory)))))))

(defmethod id-place (name)
  (let* ((row (starting-row (place name)))
	 (scol (starting-col (place name)))
	 (ecol (+ scol (length (string (id name))))))
    (vector row scol row ecol)))

(defmethod id-place ((ex fieldappl))
  (let* ((row (ending-row (place ex)))
	 (ecol (ending-col (place ex)))
	 (scol (- ecol (length (string (id ex))))))
    (vector row scol row ecol)))

(defun get-name-at (filename pos)
  (if (parsed-file? filename)
      (let ((theories (get-theories filename))
	    (name nil))
	(mapobject
	 #'(lambda (ex)
	     (or name
		 (and (syntax? ex)
		      (place ex)
		      (not (within-place pos (place ex))))
		 (when (and (name? ex) (place ex))
		   (setq name ex)
		   t)))
	 theories)
	(if (or (actuals name)
		(typep name 'binding))
	    (get-name-at* pos name)
	    name))
      (pvs-message "~a has not been parsed" filename)))

(defun get-name-at* (pos name)
  (cond ((actuals name)
	 (let ((place (place name)))
	   (if (within-place pos place)
	       name
	       (let ((nname nil))
		 (mapobject
		  #'(lambda (ex)
		      (or nname
			  (and (syntax? ex)
			       (place ex)
			       (not (within-place pos (place ex))))
			  (when (and (name? ex) (place ex))
			    (setq nname ex)
			    t)))
		  (actuals name))
		 (if nname
		     (get-name-at* pos nname)
		     name)))))
	((and (typep name 'binding)
	      (declared-type name)
	      (place (declared-type name))
	      (not (chain? name))
	      (within-place pos (place (declared-type name))))
	 (let ((nname nil))
	   (mapobject
	    #'(lambda (ex)
		(or nname
		    (and (syntax? ex)
			 (place ex)
			 (not (within-place pos (place ex))))
		    (when (and (name? ex) (place ex))
		      (setq nname ex)
		      t)))
	    (declared-type name))
	   (if nname
	       (get-name-at* pos nname)
	       name)))
	(t name)))

(defun within-place (pos place)
  (and (<= (starting-row place) (car pos) (ending-row place))
       (if (= (starting-row place) (ending-row place))
	   (<= (starting-col place) (cadr pos) (ending-col place))
	   t)))

(defun show-last-proof (&optional terse?)
  (if *last-proof*
      (pvs-buffer "Proof Display"
	(with-output-to-string (*standard-output*)
	  (let ((*disable-gc-printout* t)
		(*prover-indent* *prover-indent*)
		(*report-mode* terse?)
		(*top-proofstate* *last-proof*)
		(ps (non-strat-subgoal-proofstate *last-proof*)))
	    (report-proof* ps)
	    (when (and (typep *last-proof* 'top-proofstate)
		       (eq (status-flag *last-proof*) '!))
	      (format t "~%Q.E.D."))))
	t t)
      (pvs-message "No proof has been run yet")))

(defun show-expanded-sequent (&optional all?)
  (if (and *in-checker* *ps*)
      (let ((*disable-gc-printout* t))
	(pvs-buffer "Expanded Sequent"
	  (with-output-to-string (*standard-output*)
;	  (unless all?
;	    (format t "%%% Prelude names are not expanded~%")
;	    (format t "%%%    use C-u M-x show-expanded-sequent to see them~2%"))
	    (write (expanded-sequent all?)))
	t))
      (pvs-message "Not in prover")))

(defun expanded-sequent (&optional all?)
  (let ((*current-theory* (unless all? *current-theory*))
	(*parsing-or-unparsing* t))
    (copy *ps*
      'current-goal
      (copy (current-goal *ps*)
	's-forms (mapcar #'(lambda (sf)
			     (copy sf
			       'formula (full-name (formula sf)
						   nil (not all?))))
		   (s-forms (current-goal *ps*)))))))

(defun show-skolem-constants ()
  (if *in-checker*
      (let ((skoconsts (collect-skolem-constants))
	    (*disable-gc-printout* t))
	(if skoconsts
	    (pvs-buffer "Proof Display"
	      (with-output-to-string (*standard-output*)
		(format t "~%Skolem-constant: type")
		(format t "~%---------------------")
		(dolist (sc skoconsts)
		  (format t "~%~a: ~a" (id sc) (type sc))))
	      t)
	    (pvs-message "No Skolem Constants on this branch of the proof")))
      (pvs-message "Not in the prover")))

(defun collect-skolem-constants ()
  (let ((skoconsts nil))
    (maphash #'(lambda (id decls)
		 (declare (ignore id))
		 (dolist (d decls)
		   (when (typep d 'skolem-const-decl)
		     (pushnew d skoconsts))))
	     (current-declarations-hash))
    (sort skoconsts #'string-lessp :key #'id)))

(defun get-patch-version ()
  (when (boundp '*patch-revision*)
    (let ((str (symbol-value '*patch-revision*)))
      (when (search "$Revision: " str)
	(subseq str 11 (- (length str) 2))))))

(defun get-patch-test-version ()
  (when (boundp '*patch-test-revision*)
    (let ((str (symbol-value '*patch-test-revision*)))
      (when (search "$Revision: " str)
	(subseq str 11 (- (length str) 2))))))

(defun get-patch-exp-version ()
  (when (boundp '*patch-exp-revision*)
    (let ((str (symbol-value '*patch-exp-revision*)))
      (when (search "$Revision: " str)
	(subseq str 11 (- (length str) 2))))))

(defun collect-strategy-names (&optional all?)
  (with-open-file (*standard-output* "/dev/null" :direction :output
				     :if-exists :overwrite)
    (read-strategies-files))
  (let ((names nil))
    (maphash #'(lambda (n s)
		 (push (string-downcase (string n)) names))
	     *rulebase*)
    (maphash #'(lambda (n s)
		 (unless (and (not all?)
			      (defhelper-entry? s))
		   (push (string-downcase (string n)) names)))
	     *rules*)
    (maphash #'(lambda (n s)
		 (unless (or (and (not all?)
				  (defhelper-entry? s))
			     (defstep-entry? s))
		   (push (string-downcase (string n)) names)))
	     *steps*)
    (sort names #'string<)))

(defvar *typecheck-formula-decl* nil)

(defun typecheck-formula-decl (formula-decl &optional theory-name context)
  (unless (and *typecheck-formula-decl*
	       (equal formula-decl (car *typecheck-formula-decl*))
	       (equal theory-name (cadr *typecheck-formula-decl*))
	       (or (null theory-name)
		   (let ((th (get-theory theory-name)))
		     (and th
			  (or (from-prelude? th)
			      (= (parsed-date (filename th))
				 (caddr *typecheck-formula-decl*)))))))
    (let* ((*current-theory* (if theory-name
				 (get-typechecked-theory theory-name)
				 (car (last *prelude-theories*))))
	   (*current-context* (or context (copy (context *current-theory*))))
	   (*generate-tccs* 'none)
	   (*from-buffer* "Formula Decl"))
      (pvs-buffer *from-buffer* formula-decl nil t)
      (let ((fdecl (car (pc-parse formula-decl 'theory-elt))))
	(unless (typep fdecl 'formula-decl)
	  (type-error fdecl "Not a formula declaration"))
	(typecheck-decl fdecl)
	(let ((*generate-xref-declaration* fdecl)
	      (*xref-names-seen* nil)
	      (*xref-types-seen* nil))
	  (generate-xref fdecl))
	(setq *typecheck-formula-decl*
	      (list formula-decl
		    theory-name
		    (when (and theory-name
			       (not (from-prelude? *current-theory*)))
		      (parsed-date (filename *current-theory*)))
		    fdecl)))))
  (pvs-message "Formula typechecked")
  (fourth *typecheck-formula-decl*))

(defvar *prove-formula-proof* nil)

(defun prove-formula-decl (formula-decl &optional theory-name strategy)
  (let* ((*to-emacs* t)
	 (*current-theory* (if theory-name
			       (get-typechecked-theory theory-name)
			       (car (last *prelude-theories*))))
	 (*current-context* (copy (context *current-theory*)))
	 (fdecl (typecheck-formula-decl formula-decl theory-name))
	 (*tccforms* nil))
    (typecheck (definition fdecl) :expected *boolean* :tccs 'all)
    (when *tccforms*
      (setq fdecl
	    (typecheck-formula-decl
	     (unparse
		 (copy fdecl
		   'definition (mk-conjunction
				(nconc (mapcar #'(lambda (tcc)
						   (tccinfo-formula tcc))
					 *tccforms*)
				       (list (definition fdecl)))))
	       :string t)
	     theory-name)))
    (setq *prove-formula-proof* nil)
    (when strategy
      (multiple-value-bind (strat err)
	  (if (stringp strategy)
	      (ignore-errors (values (read-from-string strategy)))
	      strategy)
	(let ((just (unless err
		      (or (revert-justification strat)
			  (revert-justification (list "" strat))
			  strat))))
	  (unless just
	    (type-error strategy "Bad form for strategy~%  ~s" strategy))
	  (setf (justification fdecl) just))))
    (setq *to-emacs* nil)
    (read-strategies-files)
    (unwind-protect
	(let ((proof (prove-decl fdecl :strategy (when strategy
						   '(then (rerun) (quit))))))
	  (setq *prove-formula-proof*
		(editable-justification
		 (extract-justification-sexp (justification proof)))))
      (pvs-emacs-eval "(pvs-ready)"))))

(defun get-prove-formula-proof ()
  *prove-formula-proof*)

(defun show-strategy (strat-name)
  (let* ((strat-id (intern (string-downcase strat-name)))
	 (strategy (or (gethash strat-id *rulebase*)
		       (gethash strat-id *steps*)
		       (gethash strat-id *rules*))))
    (if strategy
	(pvs-buffer "Strategy Display"
	  (with-output-to-string (out)
	    (show-strategy* strategy out))
	  t)
	(pvs-message "No such strategy: ~a" strat-id))))
    
(defmethod show-strategy* ((strat rule-entry) out)
  (format out "~(~a~) is a primitive rule:" (name strat))
  (format out "~2%Arguments: ~(~a~)" (append (required-args strat)
					     '(&optional)
					     (optional-args strat)))
  (format out "~2%Definition: A compiled lisp function")
  (format out "~2%Format string: ~s" (format-string strat))
  (format out "~2%Documentation: ~%~a" (docstring strat))
  #+lucid
  (let ((file (ignore-errors (get-source-file (name strat) 'strategy))))
    (when file
      (format out "~2%Defined in file: ~s" (namestring file)))))

(defmethod show-strategy* ((strat defrule-entry) out)
  (format out "~(~a~) is a ~:[strategy~;defined rule~]:"
    (name strat) (gethash (name strat) *rules*))
  (format out "~2%Arguments: ~(~a~)" (formals strat))
  (format out "~2%Definition: ~%")
  (write (defn strat) :stream out :pretty t :level nil :length nil)
  (format out "~2%Format string: ~s" (format-string strat))
  (format out "~2%Documentation: ~%~a" (docstring strat))
  #+lucid
  (let ((file (ignore-errors (get-source-file (name strat) 'strategy))))
    (when file
      (format out "~2%Defined in file: ~s" (namestring file)))))

(defmethod show-strategy* ((strat defstep-entry) out)
  (format out "~(~a~) is a ~:[strategy~;defined rule~]:"
    (name strat) (gethash (name strat) *rules*))
  (format out "~2%Arguments: ~(~a~)" (formals strat))
  (format out "~2%Definition: ~%")
  (write (defn strat) :stream out :pretty t :level nil :length nil)
  (format out "~2%Format string: ~s" (format-string strat))
  (format out "~2%Documentation: ~%~a" (docstring strat))
  #+lucid
  (let ((file (ignore-errors (get-source-file (name strat) 'strategy))))
    (when file
      (format out "~2%Defined in file: ~s" (namestring file)))))
