PVSPATH != realpath ../..
PVS2DK   = ../pvs2dk.sh

THEORIES =\
naturals \
simple \
eqtype \
decvar \
import \
call_import \
prenex \
thyp_val \
thyp_type_val \
mixedup \
apply_theories \
subtypethy \
NatArray \
NatArrayOps \
vector \
vect_ops \
tuples \
dep_tuple \
linear_form \
tfrom \
constant_param \
exprastype \
depsubtype \
expandeddefs

all: ${THEORIES:C/$/.lpo/}

translate: ${THEORIES:C/$/.lp/}

.for th in ${THEORIES}
${th}.lp:
	PVSPATH=${PVSPATH} ${PVS2DK} -f ${PVSPATH}/lib/simple.pvs -t ${.TARGET:R} \
-o ${PVSPATH}/translations/simple/${.TARGET} > /dev/null
.endfor

.include "../lambdapi.mk"
