PVS2DK = ../pvs2dk.sh
LPC    = lambdapi check

THEORIES != grep -v -E '^-|\#' theories
PVSPATH  != realpath ../..

all: dummy ${THEORIES:C/$/.lpo/}

.PHONY: dummy
dummy:
	./mk_dummy.sh

translate: ${THEORIES:C/$/.lp/}

.for th in ${THEORIES}
${th}.lp:
	PVSPATH=${PVSPATH} ${PVS2DK} -f ${PVSPATH}/lib/prelude.pvs -t ${.TARGET:R} \
-o ${PVSPATH}/translations/prelude/${.TARGET} > /dev/null
.endfor

.include "../lambdapi.mk"
