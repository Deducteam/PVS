#!/bin/ksh
set -euo pipefail -o noclobber

while read -r line; do
    # Remove comments from line
    nocom=$(print -f "$line" | sed -e 's/^\([^#]*\).*$/\1/' | tr -d '[:space:]')
    if (print -f "${nocom}" | grep -E -q '^-'); then
        out="${nocom:1}.lp"
        [ -r "$out" ] || printf '// Dummy theory\n' > "$out"
    fi
done < 'theories'
