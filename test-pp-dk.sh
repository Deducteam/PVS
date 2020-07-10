#!/bin/ksh93

# usage: test-pp-dk.sh [options]
#   -f p, --file p              translate theory from file p
#   -t h, --theory h            translate theory t
#   -o p, --output p            write translation to file p
#   -v n, --verbose n           set verbosity level
set -euo pipefail

theory=""
file=""
output=""
verbose=3

USAGE="[+NAME?test-pp-dk.sh --- Translate a PVS specification to Dedukti]"
USAGE+="[DESCRIPTION?Parse and proofcheck a theory in PVS to translate it "
USAGE+="into Dedukti, an implementation of λΠ/R.]"
USAGE+="[f:file?File containing the theory.]:[path]"
USAGE+="[t:theory?Name of the theory to translate.]:[theory]"
USAGE+="[o:output?Target file of the translation.]:[path]"
USAGE+="[v:verbose]#[verbose:=3?Verbosity level.]"
while getopts "${USAGE}" o; do
    case "$o" in
        f) file="${OPTARG}" ;;
        t) theory="${OPTARG}" ;;
        o) output="${OPTARG}" ;;
        v) verbose="${OPTARG}"
    esac
done

./pvs -batch -q -v "${verbose}" -l test-pp-dk.el -- "${file}" "${theory}" "${output}"
