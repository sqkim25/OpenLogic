# Makefile for Chemistry: A Reasoning-Move Approach
# Build: make         (builds PDF)
# Clean: make clean   (removes build artifacts)

MAIN = chem-textbook
LATEX = latexmk
FLAGS = -pdf -interaction=nonstopmode -halt-on-error

.PHONY: all clean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex chem-preamble.sty ch-*.tex
	$(LATEX) $(FLAGS) $(MAIN).tex

clean:
	$(LATEX) -C $(MAIN).tex
	rm -f *.aux *.log *.out *.toc *.fls *.fdb_latexmk
