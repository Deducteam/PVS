;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; macros.lisp -- 
;; Author          : Sam Owre
;; Created On      : Sun Jan  9 18:44:56 1994
;; Last Modified By: Sam Owre
;; Last Modified On: Thu Oct 29 22:44:02 1998
;; Update Count    : 12
;; Status          : Unknown, Use with caution!
;; 
;; HISTORY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Copyright (c) 2002 SRI International, Menlo Park, CA 94025, USA.

(in-package :pvs)

(export '(length= singleton? add-to-alist))

(defmacro tcdebug (ctl &rest args)
  `(when *tcdebug*
     (if *to-emacs*
	 (pvs-message ,ctl ,@args)
	 (format t ,ctl ,@args))))

(defmacro makesym (ctl &rest args)
  `(intern (format nil ,ctl ,@args) :pvs))

(defmacro msgtime (ctl &rest args)
  `(progn (format t ,ctl ,@(butlast args)) (time ,(car (last args)))))

(defmacro length= (l1 l2)
  `(= (length ,l1) (length ,l2)))

(defmacro singleton? (obj)
  `(and (consp ,obj) (null (cdr ,obj))))

;;; Like typep, but a little faster.
;;; Can only be used on instances of classes.

(defmacro typec (inst class-name)
  `(eq (class-name (class-of ,inst)) ,class-name))

(defmacro add-comment (decl ctl &rest args)
  (let ((cdecl (gensym)))
    `(when *typechecking-module*
      (let ((,cdecl (or (car (generated ,decl))
			,decl)))
	(setf (newline-comment ,cdecl)
	      (append (newline-comment ,cdecl)
		      (list (format nil "% ~@?" ,ctl ,@args))))))))

;;; Courtesy of Tim Winkler

;#+gcl
;(defmacro dotimes-fixnum (&rest body)
;  (let ((var (car (car body)))
;	(lim (cadr (car body)))
;	(res (cddr (car body)))
;	(acts (cdr body))
;	(limvar (gensym))
;	(lab (gensym)))
;    `(block ()
;	   (let* ((,limvar ,lim) (,var 0))
;	     (declare (fixnum ,var ,limvar))
;	     (tagbody
;	      ,lab
;	      (if (>= ,var ,limvar) (return (progn ,@res)))
;	      (tagbody ,@acts)
;	      (setq ,var (1+ ,var))
;	      (go ,lab)))))
;  )


;;; Redefine dotimes for GCL - it is WAY too slow otherwise.

#+gcl
(defmacro dotimes ((var form &optional (val nil)) &rest body &environment env)
  (multiple-value-bind (doc decls bod)
      (pcl::extract-declarations body env)
    (declare (ignore doc))
    (let ((limit (gensym))
          (label (gensym)))
      `(let ((,limit ,form)
             (,var 0))
         (declare (fixnum ,limit ,var))
         ,@decls
         (block nil
           (tagbody
            ,label
              (when (>= ,var ,limit) (return-from nil ,val))
              ,@bod
              (setq ,var (the fixnum (1+ ,var)))
              (go ,label)))))))


;;; These macros speed up the making of terms, by going directly to the
;;; makes on the underlying ERGO structures.

(defmacro mk-ergo-term (op args)
  `(term::mk-default-term (oper::mk-oper :op ,op) ,args))

(defmacro mk-ergo-term* (op &rest args)
  `(term::mk-default-term (oper::mk-oper :op ,op) (list ,@args)))

;;; mk-sim-term* is like ERGO's mk-sim-term, but allows &rest args

(defmacro mk-sim-term* (s &rest args)
  `(mk-sim-term ,s (list ,@args)))

#+lucid
(defmacro ignore-file-errors (&rest body)
  `(ignore-errors
    (handler-bind ((lucid::file-protection-error
		    #'(lambda (x)
			(declare (ignore x))
			(invoke-restart (car (compute-restarts))))))
	,@body)))

#+(not lucid)
(defmacro ignore-file-errors (&rest body)
  `(ignore-errors
    ,@body))

(unless (fboundp 'nth-value)
  (defmacro nth-value (n form)
    `(nth ,n (multiple-value-list ,form))))

(defmacro gen-lambda-expr (vsym vtype operator)
  (let ((type (gensym))
	(id (gensym))
	(bd (gensym))
	(nvar (gensym))
	(op (gensym)))
    `(let* ((,type ,vtype)
	    (,op ,operator)
	    (,id (make-new-variable ,vsym (cons ,type ,op)))
	    (,bd (typecheck* (mk-bind-decl ,id ,type ,type) nil nil nil))
	    (,nvar (mk-name-expr ,id nil nil (make-resolution ,bd
					       (current-theory-name) ,type))))
      (beta-reduce (make-lambda-expr (list ,bd)
		     (if (listp ,op)
			 (make!-conjunction*
			  (mapcar #'(lambda (o)
				      (make!-application o ,nvar))
				  ,op))
			 (make!-application ,op ,nvar)))))))

(defmacro gen-forall-expr (vsym vtype operator)
  (let ((type (gensym))
	(id (gensym))
	(bd (gensym))
	(nvar (gensym))
	(op (gensym)))
    `(let* ((,type ,vtype)
	    (,op ,operator)
	    (,id (make-new-variable ,vsym (cons ,type ,op)))
	    (,bd (typecheck* (mk-bind-decl ,id ,type ,type) nil nil nil))
	    (,nvar (mk-name-expr ,id nil nil (make-resolution ,bd nil ,type))))
      (beta-reduce (make-forall-expr (list ,bd)
		     (if (listp ,op)
			 (mk-conjunction
			  (mapcar #'(lambda (o)
				      (mk-application o ,nvar))
				  ,op))
			 (mk-application ,op ,nvar)))))))


(defmacro with-no-type-errors (&rest forms)
  `(let ((*type-error-catch* 'type-error))
    (catch 'type-error
      ,@forms)))

(defmacro with-no-parse-errors (&rest forms)
  `(let ((*parse-error-catch* 'parse-error))
     (catch 'parse-error
       ,@forms)))

;;; with-pvs-context is a macro that temporarily changes the context,
;;; restoring everything to the previous state on exiting.

(defmacro with-pvs-context (lib-ref &rest forms)
  (let ((dir (gentemp))
	(shortdir (gentemp)))
    `(let ((,dir (directory-p (libref-to-pathname ,lib-ref))))
      (if (pathnamep ,dir)
	  (let* ((,shortdir (shortpath ,dir))
		 (*pvs-context-path* ,shortdir)
		 (*default-pathname-defaults* ,shortdir)
		 (*pvs-context-writable* (write-permission? ,shortdir))
		 (*pvs-context* nil)
		 (*pvs-context-changed* nil)
		 (*current-context* nil)
		 (*current-theory* nil)
		 (*all-subst-mod-params-caches* nil)
		 (*file-dependencies* nil))
	    ,@forms)
	  (pvs-message "Library ~a does not exist" ,dir)))))

(defmacro add-to-alist (key entry alist)
  (let ((vkey (gentemp))
	(ventry (gentemp))
	(valist (gentemp))
	(centry (gentemp)))
    `(let* ((,vkey ,key)
	    (,ventry ,entry)
	    (,valist ,alist)
	    (,centry (assoc ,vkey ,valist)))
       (if ,centry
	   (unless (memq ,ventry ,centry)
	     (setf (cdr ,centry) (cons ,ventry (cdr ,centry))))
	   (push (list ,vkey ,ventry) ,alist)))))

(defmacro starting-row (place)
  `(svref ,place 0))

(defmacro starting-col (place)
  `(svref ,place 1))

(defmacro ending-row (place)
  `(svref ,place 2))

(defmacro ending-col (place)
  `(svref ,place 3))

(defmacro line-begin (place)
  `(when ,place (svref ,place 0)))

(defmacro col-begin (place)
  `(when ,place (svref ,place 1)))

(defmacro line-end (place)
  `(when ,place (svref ,place 2)))

(defmacro col-end (place)
  `(when ,place (svref ,place 3)))

(defmacro start-place (place)
  `(list (starting-row ,place) (starting-col ,place)))

(defmacro end-place (place)
  `(list (ending-row ,place) (ending-col ,place)))

#+gcl
(Clines
"#include <signal.h>"
"extern int interrupt_flag;"
"extern int interrupt_enable;"
"extern void (*sigint)();"
)

#+gcl
(defCfun "object enable_interrupts()" 0
" interrupt_enable = TRUE;"
" if (interrupt_flag) agcl_signal(SIGINT, sigint);"
" Creturn(Cnil);"
)

#+gcl
(defentry enable-interrupts () (object enable_interrupts))

#+gcl
(defCfun "object disable_interrupts()" 0
" interrupt_enable = FALSE;"
" Creturn(Cnil);"
)

#+gcl
(defentry disable-interrupts () (object disable_interrupts))

#+gcl
(defmacro with-interrupts-disabled (&rest body)
  `(unwind-protect
       (progn
	 (disable-interrupts)
	 ,@body)
     (enable-interrupts)))

(defmacro add-place (form place)
  (let ((obj (gentemp)))
    `(let ((,obj ,form))
       (setf (place ,obj) ,place)
       ,obj)))

(defmacro def-pvs-term (name term theory &key (nt 'expr) expected)
  (assert (symbolp name) () "NAME should be a symbol")
  (assert (stringp term) () "TERM should be a string")
  (assert (stringp theory) () "THEORY should be a string")
  (eval-when (eval load)
    (let ((var (gensym))
	  (reset-name (intern (format nil "%RESET-~a" name)))
	  (hook (if (gethash (intern theory) *prelude*)
		    '*load-prelude-hook*
		    '*untypecheck-hook*)))
      `(let ((,var nil))
	 (pushnew ',reset-name ,hook)
	 (defun ,name ()
	   (or ,var
	       (let* ((*current-theory* (get-typechecked-theory ,theory))
		      (*current-context* (saved-context *current-theory*))
		      (*generate-tccs* 'none)
		      ,@(when expected
			  `((expected-type
			     (pc-typecheck (pc-parse ,expected 'type-expr))))))
		 (assert *current-context*)
		 (setq ,var (pc-typecheck (pc-parse ,term ',nt)
			      ,@(when expected '(:expected expected-type)))))))
	 (defun ,reset-name ()
	   (setq ,var nil))))))

(defmacro do-all-theories (fn)
  `(progn (maphash #'(lambda (mid theory)
		       (declare (ignore mid))
		       (funcall ,fn theory))
		   *pvs-modules*)
	  (maphash #'(lambda (lib ht)
		       (declare (ignore lib))
		       (maphash #'(lambda (mid theory)
				    (declare (ignore mid))
				    (funcall ,fn theory))
				(cadr ht)))
		   *imported-libraries*)
	  (maphash #'(lambda (lib ht)
		       (declare (ignore lib))
		       (maphash #'(lambda (mid theory)
				    (declare (ignore mid))
				    (funcall ,fn theory))
				(cadr ht)))
		   *prelude-libraries*)
	  (maphash #'(lambda (mid theory)
		       (declare (ignore mid))
		       (funcall ,fn theory))
		   *prelude*)))

(defmacro protect-types-hash (obj &rest forms)
  `(unwind-protect
      (let ((*expression-types* (if *in-typechecker*
				    *expression-types*
				    *empty-expression-types*))
	    (*in-typechecker* (or *in-typechecker*
				  (if (or *in-checker* *in-evaluator*)
				      ,obj
				      t))))
	,@forms)
    (unless *in-typechecker*
      (setq *empty-expression-types* (make-hash-table :test 'eq)))))

(defmacro with-case-insensitive-lower (&rest forms)
  #+(or allegro-v6.0 allegro-v6.2)
  `(unwind-protect
       (progn (excl:set-case-mode :case-insensitive-lower)
	      ,@forms)
     (excl:set-case-mode :case-sensitive-lower))
  #-(or allegro-v6.0 allegro-v6.2)
  `(progn ,@forms))

(defmacro get-declarations (id &optional decl-hash)
  (if decl-hash
      `(get-lhash ,id ,decl-hash)
      `(get-lhash ,id (current-declarations-hash))))

(defsetf get-declarations (id &optional decl-hash) (decl)
  (if decl-hash
      `(pushnew ,decl (get-lhash ,id ,decl-hash) :test #'eq)
      `(pushnew ,decl (get-lhash ,id (current-declarations-hash)) :test #'eq)))

(defmacro put-decl (decl &optional decl-hash)
  (let ((gdecl (gensym)))
    (if decl-hash
	`(let ((,gdecl ,decl))
	   (setf (get-declarations (id ,gdecl) ,decl-hash) ,gdecl))
	`(let ((,gdecl ,decl))
	   (setf (get-declarations (id ,gdecl) (current-declarations-hash))
		 ,gdecl)))))

;; Only used by add-decl, destructively modifies the context
(defun delete-declaration (decl &optional decl-hash)
  (assert (or decl-hash *current-context*))
  (let* ((lht (or decl-hash (current-declarations-hash)))
	 (ht (lhash-table lht)))
    (when (hash-table-p ht)
      (let* ((decls (gethash (id decl) ht)))
	(when (memq decl decls)
	  (if (cdr decls)
	      (setf (gethash (id decl) ht) (delete decl decls))
	      (remhash (id decl) ht)))))
    (when (lhash-next lht)
      (delete-declaration decl (lhash-next lht)))))

(defun do-all-declarations (function &optional decl-hash)
  (assert (or decl-hash *current-context*))
  (let ((lht (or decl-hash (current-declarations-hash))))
    (map-lhash #'(lambda (id decls)
		   (declare (ignore id))
		   (mapc function decls))
	       lht)))


(defmacro get-importings (theory &optional using-hash)
  (if using-hash
      `(get-lhash ,theory ,using-hash)
      `(get-lhash ,theory (current-using-hash))))

(defsetf get-importings (theory &optional using-hash) (using)
  (if using-hash
      `(setf (get-lhash ,theory ,using-hash) ,using)
      `(setf (get-lhash ,theory (current-using-hash)) ,using)))

(defmacro put-importing (inst theory &optional using-hash)
  (if using-hash
      `(pushnew ,inst (get-importings ,theory ,using-hash))
      `(pushnew ,inst (get-importings ,theory (current-using-hash)))))
