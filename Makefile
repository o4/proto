SRC := ${PWD}/proto
OUT := ${PWD}/dist

.DEFAULT_GOAL : hs js 

hs: ${OUT}/hs
js: ${OUT}/js 

${OUT}:; @mkdir $<

${OUT}/js:; agda --js --compile-dir=${OUT} ${SRC}/Everything.agda
${OUT}/hs:; agda   -c --compile-dir=${OUT} ${SRC}/Everything.agda # --ghc-flag="--no-main"

c:; @find . -type f -name '*.agdai' -delete && rm -rf dist/

.PHONY: js c 
