(in-package 'pvs)

(defun get-current-enum-types ()
  (let* ((all-enum-type-decls
	  (loop for i-list being each hash-value in
		(declarations-hash *current-context*)
		;;(th . ignore) in (using *current-context*)
		nconc (loop for i in i-list
			    when (and (typep i 'type-decl)
				      (enum-adt? (type-value i)))
			    collect (type-value i))))
	 (enum-types (remove-duplicates all-enum-type-decls
			    :key #'id)))
    enum-types))

(defun make-distinct-lists-from-enum-types ()
  (let ((enum-types (get-current-enum-types)))
    (setq dp::*distinct-lists*
	  (loop for et in enum-types
		collect
		(loop for r in (constructors et)
		      collect (let ((*newdc* t))
				(top-translate-to-prove r)))))))
