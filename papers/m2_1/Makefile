.PHONY: pdf clean

pdf:
	latexmk -pdf -r latexmkrc main.tex
	test -f build/main.pdf

clean:
	latexmk -C -r latexmkrc main.tex
	rm -rf build
