;;; pvs2dkwrap.el --- Translate a PVS theory to Dedukti
;;; Commentary:
;; Should be called by PVS, in batch mode. The script takes three arguments:
;; - the filepath where the theory to translate is,
;; - the name of the theory inside this file,
;; - an (optional) output file where to write the translation.
;; Call it with,
;; `pvs -batch -q -v 3 -l test-pp-dk.el -- FILE THEORY OUTPUT’
;;; Code:

(let* ((fname (cadr command-line-args-left))
       (output (cadddr command-line-args-left))
       (rdir (concatenate 'string default-directory fname))
       (dir (expand-file-name rdir))
       (thname (caddr command-line-args-left))
       (theoryref (concatenate 'string dir "#" thname)))
  (message "Printing theory %s" theoryref)
  (prettyprint-dedukti theoryref output))
(set-buffer "pvs")
(let ((ct (buffer-string)))
  (princ ct))
;;; pvs2dkwrap.el ends here
