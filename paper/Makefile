.PHONY: pdf clean figures

pdf:
	rm -f main.pdf main.aux main.log main.out main.synctex.gz
	latexmk -pdf -r latexmkrc main.tex

clean:
	latexmk -C -r latexmkrc main.tex
	rm -f main.pdf main.aux main.log main.out main.synctex.gz
	rm -rf build

figures:
	python3 ../scripts/plot_frontier.py --atlas-outdir /tmp/atlas_phase4_paper --outdir figures/generated --format png
