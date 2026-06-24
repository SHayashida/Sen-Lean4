.PHONY: pdf clean

TEXMFVAR ?= /tmp/sen-lean4-m3-texmf-var

pdf:
	mkdir -p $(TEXMFVAR)
	TEXMFVAR=$(TEXMFVAR) latexmk -lualatex -interaction=nonstopmode -halt-on-error main.tex
	test -f main.pdf

clean:
	TEXMFVAR=$(TEXMFVAR) latexmk -C main.tex
	rm -f main.pdf
