#!/bin/ksh
set -euo pipefail

while read -r line; do
    nocom=$(echo "$line" | sed -e 's/^\([^#]*\).*$/\1/' | tr -d '[:space:]')
    if (print -f "${nocom}" | grep -E -q '^-'); then
        echo "// Dummy theory" > "${nocom:1}.lp"
    fi
done < 'theories'
