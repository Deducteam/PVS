(in-package :pvs)
(eval-when (compile)
  (require :foreign))
(export '(file-exists-p directory-p read-permission? write-permission?
			file-write-time get-file-info))

(eval-when (eval compile load)
(ff:def-foreign-call fileutils___file_exists_p
    ((filename (* :char) simple-string))
  #+(version>= 6) :strings-convert #+(version>= 6) nil
  :arg-checking nil
  :call-direct t
  :returning :int)

(ff:def-foreign-call fileutils___directory_p
    ((filename (* :char) simple-string))
  #+(version>= 6) :strings-convert #+(version>= 6) nil
  :arg-checking nil
  :call-direct t
  :returning :int)

(ff:def-foreign-call fileutils___read_permission_p
    ((filename (* :char) simple-string))
  #+(version>= 6) :strings-convert #+(version>= 6) nil
  :arg-checking nil
  :call-direct t
  :returning :int)

(ff:def-foreign-call fileutils___write_permission_p
    ((filename (* :char) simple-string))
  #+(version>= 6) :strings-convert #+(version>= 6) nil
  :arg-checking nil
  :call-direct t
  :returning :int)

(ff:def-foreign-call fileutils___file_write_time
    ((filename (* :char) simple-string))
  #+(version>= 6) :strings-convert #+(version>= 6) nil
  :arg-checking nil
  :call-direct t
  :returning :int)

(ff:def-foreign-call fileutils___getfileinfo
    ((filename (* :char) simple-string)
     (stat (* :int) (simple-array (signed-byte 32) (2))))
  #+(version>= 6) :strings-convert #+(version>= 6) nil
  :arg-checking nil
  :call-direct t
  :returning :int)
)

;;;

(defmacro expanded-tilde-namestring (filename)
  `(ignore-errors (excl::tilde-expand-unix-namestring (namestring ,filename))))

(defun file-exists-p (filename)
  (let ((exp-file (expanded-tilde-namestring filename)))
    (and exp-file
	 (zerop (fileutils___file_exists_p exp-file)))))

(defun directory-p (filename)
  (when filename
    (let ((filestring (expanded-tilde-namestring filename)))
      (unless (zerop (fileutils___directory_p filestring))
	(pathname (if (char= (char filestring (1- (length filestring))) #\/)
		      filestring
		      (concatenate 'string filestring "/")))))))

(defun read-permission? (filename)
  (zerop (fileutils___read_permission_p
	  (expanded-tilde-namestring filename))))

(defun write-permission? (filename)
  (zerop (fileutils___write_permission_p
	  (expanded-tilde-namestring filename))))

(defconstant u1970 (encode-universal-time 0 0 0 1 1 1970 0))

(defun file-write-time (filename)
  (let ((date (fileutils___file_write_time
	       (expanded-tilde-namestring filename))))
    (unless (zerop date)
      (+ date u1970))))

;;; #(dev inode mtime isdir mode)
(let ((fstat-array
       (make-array 2 :initial-element 0 :element-type 'fixnum)))
  (defun get-file-info (filename)
    (when (zerop (fileutils___getfileinfo
		  (expanded-tilde-namestring filename) fstat-array))
      (list (aref fstat-array 0)
	    (aref fstat-array 1)))))
