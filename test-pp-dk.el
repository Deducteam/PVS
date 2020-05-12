;; Emacs script  that loads  a dummy theory,  type checks it  and exports  it to
;; Dedukti. The content of the `pvs' buffer is printed to stdout

(typecheck "lib/simple")
(let* ((fname (cadr command-line-args-left))
       (rdir (concatenate 'string default-directory fname))
       (dir (expand-file-name rdir))
       (thname (caddr command-line-args-left))
       (theoryref (concatenate 'string dir "#" thname)))
  (message "Printing theory %s" theoryref)
  (prettyprint-dedukti theoryref))
(set-buffer "pvs")
(let ((ct (buffer-string)))
  (princ ct))
