#!/bin/ksh93

# usage: test-pp-dk.sh [options]
#   -f p, --file p              translate theory from file p
#   -t h, --theory h            translate theory t
#   -o p, --output p            write translation to file p
#   -s p, --specification p     use specification p
#   -v n, --verbose n           set verbosity level

set -eufo pipefail

# Get pvs executable from path, else just call pvs
PVS="${PVS:-pvs}"
PVSWRAP="translations/pvs2dkwrap.el"

theory=""
file=""
output=""
specification=""
verbose=3

USAGE="[-author?Gabriel Hondet <gabriel.hondet@inria.fr>]"
USAGE+="[+NAME?pvs2dk.sh --- Translate a PVS specification to Dedukti]"
USAGE+="[+DESCRIPTION?Parse and proofcheck a theory in PVS to translate it
to Dedukti, an implementation of λΠ/R.

PVS filepaths are ALWAYS relative to the root of PVS. This restriction
is imposed by PVS (which uses a environment variable PVSPATH).

Theories can either be translated one at a time using the -f and -t options,
such as in pvs2dk --file=lib/prelude.pvs --theory=booleans.

A specification can be used with the --specification option to indicate which
theories from which files are to be translated. A specification is a
newline-separated list of entries. An entry which starts with a opening angle
bracket '<' must be followed by a PVS source file: all subsequent theory entries
will be sought in this file. An entry starting with a pound '#' is a comment and
is ignored. Otherwise, an entry which starts by a letter is the name of a theory
in the file indicated by the last file entry. Considering a theory named 'thy',
it is translated to a file 'thy.lp' in the same directory as the
specification.]"
USAGE+="[f:file?File containing the theory.]:[path]"
USAGE+="[t:theory?Name of the theory to translate.]:[theory]"
USAGE+="[o:output?Target file of the translation.]:[path]"
USAGE+="[s:specification?Translate using specification.]:[spec]"
USAGE+="[v:verbose]#[verbose:=3?Verbosity level.]"
USAGE+=$'\n\n\n\n'
while getopts "${USAGE}" o; do
    case "$o" in
        f) file="${OPTARG}" ;;
        t) theory="${OPTARG}" ;;
        o) output="${OPTARG}" ;;
        s) specification="${OPTARG}" ;;
        v) verbose="${OPTARG}"
    esac
done

translate() {
    # Translate pvs files when using specification.
    file="$1"  thy="$2"
    $PVS -batch -q -v "${verbose}" -l "${PVSWRAP}" -- \
        "${file}" "${thy}" "${thy}.lp"
}

if [[ -z "${specification}" ]]; then
    $PVS -batch -q -v "${verbose}" -l "${PVSWRAP}" -- \
        "${file}" "${theory}" "${output}"
else
    LC=1
    while read -r line; do
        if (print -f "$line" | grep -E -q '^<'); then
            file="${line:1}"
            printf 'Reading from PVS source file: %s\n' "${file}"
        elif (print -f "${line}" | grep -E -q '^#'); then
            continue
        elif (print -f "${line}" | grep -E -q '^[a-zA-Z][a-zA-Z0-9_\?]+$')
        then
            printf 'Translating %s\n' "${line}"
            translate "${file}" "${line}"
        else
            printf '[%s:%d]: Invalid line\n' "${specification}" "${LC}"
            exit 1
        fi
        ((LC++))
    done < "${specification}"
fi
