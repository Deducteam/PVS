;;;
;;; go-pvs.el dave_sc 12/1/98
;;;
;;; Try to determine the version of Emacs being run, setup the load-path,
;;; and load the real pvs-load file from the byte compiled directory.

(setq debug-on-error t)

(defconst pvs-emacs-system
  (cond ((or (string-match "XEmacs 21" (emacs-version))
	     (string-match "^21\..*XEmacs" emacs-version))
	 'xemacs21)
	((string-match "XEmacs 20" (emacs-version))
	 'xemacs20)
	((string-match "XEmacs 19" (emacs-version))
	 'xemacs19)
	((string-match "Emacs 2" (emacs-version))
	 'emacs20)
	((string-match "Emacs 19" (emacs-version))
	 'emacs19)
	(t
	 (message "Your Emacs version is not known by PVS - assuming Emacs 20")
         'emacs20))
  "The version of Emacs in which PVS is running. Set in go-pvs.el.
   Defined as one of (xemacs21 xemacs20 xemacs19 emacs20 emacs19) and defaults
   to emacs20 if the current version cannot be determined.")

(if (getenv "PVSPATH")
    (defconst pvs-path (if (string-match "/$" (getenv "PVSPATH"))
			(substring (getenv "PVSPATH") 0 -1)
			(getenv "PVSPATH"))
      "The pathname of the PVS directory.
       Set in go-pvs.el to be the environment variable PVSPATH,
       which is set by the pvs shell script")
    (error "PVSPATH environment variable must be set"))

(setq load-path
  (append (list pvs-path
	        (concat pvs-path "/emacs/"
			(prin1-to-string pvs-emacs-system)))
	  (when (file-exists-p (concat pvs-path "/emacs/emacs-src"))
		(list (concat pvs-path "/emacs/emacs-src")
		      (concat pvs-path "/emacs/emacs-src/ilisp")))
          load-path))

;;; Maybe check at this point for the correct byte compilation of
;;; pvs-load.elc - if not, can complain now and give instructions for
;;; re-compilation.
 
(load "pvs-load" nil nil nil)
