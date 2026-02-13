.PHONY: pdf clean figures

pdf:
	latexmk -pdf -r latexmkrc main.tex

clean:
	latexmk -C -r latexmkrc main.tex
	rm -rf build

figures:
	python3 ../scripts/plot_frontier.py --atlas-outdir /tmp/atlas_phase4_paper --outdir figures/generated --format png
