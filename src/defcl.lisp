;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; -*- Mode: Lisp -*- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; defcl.lisp -- This provides the a macro that expands into defclass plus
;;               the methods 
;; Author          : Sam Owre
;; Created On      : Tue May 31 01:36:04 1994
;; Last Modified By: Sam Owre
;; Last Modified On: Fri Jul  1 14:02:27 1994
;; Update Count    : 14
;; Status          : Beta
;; 
;; HISTORY 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :pvs)

(export '(defcl))

#+cmu
(defmethod slot-exists-p-using-class (c o s)
  (declare (ignore c o s))
  nil)

#+gcl
(eval-when (eval compile load)
  (defmacro ignore-errors (&body forms)
    `(progn ,@forms)))


(defvar *slot-info* nil
  "An association list mapping classes to superclasses, immediate
unignored slots, saved-slots, and unsaved-slots.")


(defmacro defcl (name classes &rest args)
  (setf args (mapcar #'(lambda (a) (if (consp a) a (list a))) args))
  `(progn ,@(mapcar #'(lambda (a)
			#+allegro `(declaim (function ,(car a) (t)
					     ,(cadr (member :type a))))
			#-allegro `(proclaim '(function ,(car a) (t)
					       ,(cadr (member :type a)))))
		    (remove-if-not #'(lambda (a) (member :type a))
		      args))
    (defclass ,name ,classes
      ,(mapcar #'(lambda (a)
		   (setq a (remove-keyword
			    :parse
			    (remove-keyword
			     :ignore
			     (remove-keyword
			      :ignorc
			      (remove-keyword
			       :fetch-as a)))))
		   (append a (list :accessor (car a)
				   :initarg (car a)
				   :initarg (intern (string (car a))
						    'keyword))
			   (unless (memq :initform a)
			     (list :initform nil))))
	       args))
    (declare-make-instance ,name)
    (proclaim '(inline ,(intern (format nil "~a?" name))))
    (defun ,(intern (format nil "~a?" name)) (obj)
      (typep obj ',name))
    (eval-when (eval compile load)
      (setq *slot-info*
	    (cons (cons ',name
			'(,classes ,args))
		   (delete (assoc ',name *slot-info*)
			   *slot-info*))))
    (defmethod untc*
	,@(when classes (list :around))
	((obj ,name))
	,@(when classes (list '(call-next-method)))
	,@(mapcar #'(lambda (a)
		      (let ((slot (car a)))
			(if (cadr (memq :parse a))
			    `(untc* (slot-value obj ',slot))
			    `(setf (slot-value obj ',slot)
			      ,(cadr (memq :initform a))))))
		  args))
    ))


; (defmacro defcl* (name classes &rest args)
;   (let ((cl (macroexpand `(defcl ,name ,classes ,@args))))
;     (eval (second cl))
;     (eval (sixth cl))   ;; updates *slot-info*
;     (append cl
; 	    (generate-defcl-methods (list name))
; 	    (generate-update-fetched-methods (list name)))))

; (defvar *classes-done* nil)
; (defvar *methods-collected* nil)

; (defun generate-defcl-methods (names)
;   (let ((*classes-done* nil)
; 	(*methods-collected* nil))
;     (generate-defcl-methods* names)
;     *methods-collected*))

; (defun generate-defcl-methods* (names)
;   (when names
;     (let* ((name (car names))
; 	   (class (find-class name)))
;       (unless (memq name *classes-done*)
; 	(push name *classes-done*)
; 	(setq *methods-collected*
; 	      (nconc *methods-collected*
; 		     (list (generate-copy-method name)
; 			   (generate-store-object*-method name)
; 			   ;;(generate-update-fetched-method name)
; 			   )))
; 	(generate-defcl-methods* (mapcar #'class-name
; 				   (class-direct-subclasses class)))))
;     (generate-defcl-methods* (cdr names))))

; (defun generate-update-fetched-methods (names)
;   (let ((*classes-done* nil)
; 	(*methods-collected* nil))
;     (generate-update-fetched-methods* names)
;     (nreverse *methods-collected*)))

; (defun generate-update-fetched-methods* (names)
;   (when names
;     (let* ((name (car names))
; 	   (class (find-class name)))
;       (unless (memq name *classes-done*)
; 	(push name *classes-done*)
; 	(push (generate-update-fetched-method name) *methods-collected*)
; 	(generate-update-fetched-methods* (mapcar #'class-name
; 					    (class-direct-subclasses class)))))
;     (generate-update-fetched-methods* (cdr names))))


;;; lcopy is a lazy copy that only makes a copy if there is a difference

(defun lcopy (obj &rest initargs)
  (if (loop for (key val) on initargs by #'cddr
	    always (eq (slot-value obj key) val))
      obj
      (apply #'copy obj initargs)))

(eval-when (compile load eval)
  (defun remove-keyword (key list)
    (let ((tail (member key list)))
      (if tail
	  (append (ldiff list tail) (cddr tail))
	  list))))

(defun write-deferred-methods-to-file (&optional force?)
  (let ((mfile (format nil "~a/src/pvs-methods.lisp" *pvs-path*))
	(cefile (format nil "~a/src/classes-expr.lisp" *pvs-path*))
	(cdfile (format nil "~a/src/classes-decl.lisp" *pvs-path*))
	(csfile (format nil "~a/src/prover/estructures.lisp" *pvs-path*)))
    (unless (and (not force?)
		 (probe-file mfile)
		 (file-older cefile mfile)
		 (file-older cdfile mfile)
		 (file-older csfile mfile))
      (with-open-file (out mfile :direction :output :if-exists :supersede)
	(write '(in-package :pvs) :stream out)
	(dolist (si *slot-info*)
	  (write-deferred-methods (car si) out))))))

(defun write-deferred-methods (name out)
  (let* ((slots (get-all-slots-of (list name)))
	 (unignored-slots (mapcar #'car (unignored-slots% slots)))
	 (saved-slots (saved-slots% slots))
	 (unsaved-slots (unsaved-slots% slots)))
    (format out "~2%")
    (write `(defmethod copy ((obj ,name) &rest initargs)
	      (with-slots ,unignored-slots obj
		(make-instance ',name
		  ,@(mapcan #'(lambda (sl)
				`(',(car sl)
				  (let ((getfv (getf initargs ',(car sl)
						     '%nogetf)))
				    (if (eq getfv '%nogetf)
					,(if (ignored-slot% sl)
					     (getf (cdr sl) :initform)
					     (car sl))
					getfv))))
			    slots))))
	   :stream out :level nil :length nil :pretty t)
    (format out "~2%")
    (write `(defmethod store-object* ((obj ,name))
	      (reserve-space ,(1+ (length saved-slots))
		(with-slots ,(mapcar #'car saved-slots) obj
		  (push-word (store-obj ',name))
		  ,@(mapcar #'(lambda (a)
				`(push-word (store-obj ,(car a))))
			    saved-slots))))
	   :stream out :level nil :length nil :pretty t)
    (format out "~2%")
    (write `(defmethod update-fetched ((obj ,name))
	      (with-slots (,@(mapcar #'car saved-slots)
			     ,@(mapcar #'car unsaved-slots)) obj
		,@(let ((arg-setters nil))
		    (dotimes (i (length saved-slots))
		      (let ((a (nth i saved-slots)))
			(push `(setf ,(car a)
				     (fetch-obj (stored-word ,(1+ i))))
			      arg-setters)))
		    (dolist (a unsaved-slots)
		      (push `(setf ,(car a)
				   ,(getf (cdr a) :fetch-as))
			    arg-setters))
		    (nreverse arg-setters))))
	   :stream out :level nil :length nil :pretty t)))

(defun get-all-slots-of (classes &optional slots)
  (if (null classes)
      (remove-duplicates slots :key #'car)
      (let ((slot-info (assoc (car classes) *slot-info*)))
	(get-all-slots-of (append (cadr slot-info) (cdr classes))
			  (append (caddr slot-info) slots)))))


(defun unignored-slots% (args)
  (remove-if #'ignored-slot% args))

(defun ignored-slot% (arg)
  (or (cadr (memq :ignore arg))
      (cadr (memq :ignorc arg))))

(defun saved-slots% (args)
  (remove-if #'(lambda (a) (memq :fetch-as a)) args))

(defun unsaved-slots% (args)
  (remove-if-not #'(lambda (a) (memq :fetch-as a)) args))


;;; Grabbed off the net, from jmorrill@bbn.com (Jeff Morrill)
;;; Not used, but may come in handy.

;(defmethod shallow-copy ((object standard-object))
;  (let ((copy (make-instance (class-of object))))
;    (dolist (slotd (class-slots (class-of object)))
;       (let ((name (slot-definition-name slotd)))
;         (setf (slot-value copy name) (slot-value object name))))
;    copy))

;(defmethod eequal (obj1 obj2)
;  (equal obj1 obj2))

#+allegro
(defun memq (elt list)
  (member elt list :test #'eq))

(defun file-older (file1 file2)
  (let ((time1 (file-write-date file1))
	(time2 (file-write-date file2)))
    (or (null time1)
	(null time2)
	(<= time1 time2))))
