(require 'cl)

(defvar pvs-grammar-file "/project/pvs/pvs2.4/src/pvs-gr.txt")

(defun get-pvs-keywords ()
  (let ((keys nil))
    (let ((buf (find-file-noselect pvs-grammar-file)))
      (save-excursion
	(set-buffer buf)
	(goto-char (point-min))
	(while (re-search-forward "'\\([A-Z][^' \n\t]*\\)'" nil t)
	  (let ((key (buffer-substring (match-beginning 1) (match-end 1))))
	    (pushnew (escape-tex-chars key) keys :test 'string=)))))
    (sort* keys 'string<)))

(defun escape-tex-chars (string)
  (if (string-match "^[A-Za-z]" string)
      (let ((pos (- (length string) 1))
	    (chars nil))
	(while (>= pos 0)
	  (let ((ch (aref string pos)))
	    (push ch chars)
	    (when (= ch ?_)
	      (push ?\\ chars))
	    (decf pos)))
	(concat chars))
      (escape-tex-operator-chars string)))

(defun string-to-char-list (string)
  "Return a list of which elements are characters in the STRING."
  (mapcar #'identity string))

(defun escape-tex-operator-chars (string)
  (let ((pos (- (length string) 1))
	(chars nil))
    (while (>= pos 0)
      (setq chars
	    (nconc
	     (string-to-char-list (concat "\\char" (aref string pos)))
	     chars))
      (decf pos))
    (concat chars)))

(defun get-pvs-operators ()
  (let ((keys nil))
    (let ((buf (find-file-noselect pvs-grammar-file)))
      (save-excursion
	(set-buffer buf)
	(goto-char (point-min))
	(while (re-search-forward "'\\([^A-Z ][^'A-Za-z \n\t]*\\)'" nil t)
	  (let ((key (buffer-substring (match-beginning 1) (match-end 1))))
	    (pushnew key keys :test 'string=)))))
    (mapcar 'escape-tex-chars (sort* keys 'string<))))

(defun get-pvs-opsyms ()
  (let ((keys nil))
    (let ((buf (find-file-noselect pvs-grammar-file)))
      (save-excursion
	(set-buffer buf)
	(goto-char (point-min))
	(re-search-forward "^opsym[ \n\t]*::=" nil t)
	(let ((start (point))
	      (end (save-excursion
		     (re-search-forward "::=" nil t)
		     (point))))
	  (while (re-search-forward "'\\([^']*\\)'" end t)
	    (let ((key (buffer-substring-no-properties
			(match-beginning 1) (match-end 1))))
	      (pushnew key keys :test 'string=))))))
    (mapcar 'escape-tex-chars (sort* keys 'string<))))

(defun pvs-keyword-table-5 ()
  (pvs-keyword-table 5))

(defun pvs-keyword-table (ncols)
  (interactive "nNumber of columns")
  (pvs-generate-table (get-pvs-keywords) ncols))

(defun pvs-opsym-table-6 ()
  (pvs-opsym-table 6))

(defun pvs-opsym-table (ncols)
  (interactive "nNumber of columns")
  (pvs-generate-table (get-pvs-opsyms) ncols))

(defun pvs-generate-table (keywords ncold)
  (let* ((colsize (+ (max-string-length keywords) 2))
	 (div (/ (length keywords) ncols))
	 (mod (% (length keywords) ncols))
	 (nrows (+ div (if (= mod 0) 0 1)))
	 (listing ""))
    (dotimes (r nrows)
      (setq listing
	    (concat listing
		    (make-listing-row keywords r nrows ncols colsize div mod))))
    (message listing)))

(defun pvs-operator-table (ncols)
  (pvs-generate-table (get-pvs-operators) ncols))

(defun pvs-operator-table-6 ()
  (pvs-operator-table 6))

(defun max-string-length (strings &optional l)
  (dolist (str strings)
    (let ((ls (length (if (stringp str) str (format "%s" str)))))
      (if (or (null l) (> ls l)) (setq l ls))))
  l)

(defun make-listing-row (list row numrows numcols colsize div mod)
  (let ((lrow "\\\\\n")
	(spaces (make-string colsize ? )))
    (dotimes (i numcols)
      (let* ((c (- numcols i 1))
	     (elt (or (nth (+ (* c numrows) row 1)
			   list)
		      "")))
	(setq lrow
	      (concat (if (zerop i)
			  elt
			  (format "%s &%s" elt "  "))
		      lrow))
	(setq first nil)))
    lrow))

(defun extract-pvs-commands-from-user-guide ()
  (save-excursion
    (let ((cmds nil))
      (set-buffer (find-file-noselect
		   "/project/pvs/doc/user-guide/ug-commands.tex"))
      (while (re-search-forward "\\icmd{\\([^}]*\\)}" nil t)
	(pushnew (intern (buffer-substring (match-beginning 1) (match-end 1)))
		 cmds))
      cmds)))

  
