#!/bin/ksh93
set -euo pipefail

theory="simple"
file="lib/simple.pvs"
USAGE="f:t:v#"
while getopts "${USAGE}" o; do
    case "$o" in
        f) file="${OPTARG}" ;;
        t) theory="${OPTARG}" ;;
    esac
done

./pvs -batch -q -v 3 -l test-pp-dk.el -- "${file}" "${theory}"
