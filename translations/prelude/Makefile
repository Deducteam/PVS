PVS2DK = ../pvs2dk.sh
LPC    = lambdapi check

THEORIES != grep -v -E '^-|\#' theories

all: ${THEORIES:C/$/.lpo/}

translate: ${THEORIES:C/$/.lp/}

.for th in ${THEORIES}
${th}.lp:
	PVSPATH=../../ ${PVS2DK} -f lib/prelude.pvs -t ${.TARGET:R} \
-o translations/prelude/${.TARGET} > /dev/null
.endfor

.include "../lambdapi.mk"
