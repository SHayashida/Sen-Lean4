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
	@echo "M2 has no auto-generated figures yet; positive bridge and scope wall are textual."
	@echo "If/when figures are added, wire them through scripts/render_paper_assets.py --paper-id m2."
