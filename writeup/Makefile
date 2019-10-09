TEX_SRC_FILES := $(wildcard tex/*.tex)
TEX_OUT_FILES := $(subst tex/,out/,$(TEX_SRC_FILES))

STY_SRC_FILES := $(wildcard sty/*.sty)
STY_OUT_FILES := $(subst sty/,out/,$(STY_SRC_FILES))

BIB_SRC_FILES := $(wildcard bib/*.bib)
BIB_OUT_FILES := $(subst bib/,out/,$(BIB_SRC_FILES))

SED_FILES := $(sort $(wildcard sed/*.sed))

# BIBTEX := bibtex
BIBTEX := touch

.PHONY: default
default: main.pdf

.PHONY: again
again:
	rm -f main.pdf
	rm -f out/main.pdf
	make

.PHONY: twice
twice:
	make again
	make again

.PHONY: thrice
thrice:
	make twice
	make again

.PHONY: clean
clean:
	rm -rf out/
	rm -f main.pdf

.PHONY:
debug:

main.pdf: out/main.pdf
	cp out/main.pdf ./

out/%.tex: tex/%.tex $(SED_FILES)
	mkdir -p out
	cp $< $@
	for s in $(SED_FILES) ; do sed -E -i.bu -f $$s $@ ; done

out/%.sty: sty/%.sty
	mkdir -p out
	cp $< $@

out/%.bib: bib/%.bib
	mkdir -p out
	cp $< $@
	for s in $(SED_FILES) ; do sed -E -i.bu -f $$s $@ ; done

out/main.pdf: Makefile $(TEX_OUT_FILES) $(STY_OUT_FILES) $(SED_OUT_FILES) $(BIB_OUT_FILES)
	cd out && pdflatex main.tex && $(BIBTEX) main
