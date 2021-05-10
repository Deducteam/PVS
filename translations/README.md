Translating to Dedukti/Lambdapi
===============================

This directory contains scripts and tools for the translation of PVS theories
to Dedukti files.

**Warning:** all paths are relative to the environment variable `PVSPATH`.

- `pvs2dk.sh`: translate a theory to a lambdapi file.
- `pvs2dkwrap.el`: calls the emacs command `prettyprint-dedukti` of PVS from the
  command line. It allows to print a theory from the command line (rather than
  from within emacs).
- `lambdapi.pkg`: the module file for lambdapi (required to type check files).
- `lambdapi.mk`: some targets and rules to typecheck lambdapi files.
- `*.patch`: patches that may be apply to the Prelude to translate it.
