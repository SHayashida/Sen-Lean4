.PHONY: all clean

MAIN := main
BUILD_DIR := build
PDF := $(BUILD_DIR)/$(MAIN).pdf

all: $(PDF)

$(PDF): $(MAIN).tex refs.bib
	mkdir -p $(BUILD_DIR)
	TEXINPUTS=.:..: BIBINPUTS=.:..: latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=$(BUILD_DIR) $(MAIN).tex

clean:
	latexmk -C -outdir=$(BUILD_DIR) $(MAIN).tex || true
	rm -rf $(BUILD_DIR)
