REPO_ROOT := ../..

.PHONY: pdf clean figures

pdf:
	rm -f main.pdf main.aux main.log main.out main.synctex.gz
	latexmk -pdf -r latexmkrc main.tex

clean:
	latexmk -C -r latexmkrc main.tex
	rm -f main.pdf main.aux main.log main.out main.synctex.gz
	rm -rf build

figures:
	cd $(REPO_ROOT) && python3 scripts/render_paper_assets.py --paper-id m1_5 --mode tiny
