## $Id: Makefile 2572 2012-10-18 14:58:11Z schwicht $

## Makefile for subdirectory doc

all: .dep
	ls -sh

.dep: ref.pdf tutor.pdf cleanup
	touch .dep

ref.pdf: ref.tex minlog.bib
	pdflatex ref >> /dev/null
	bibtex -terse ref
	makeindex -q ref
	pdflatex ref >> /dev/null
	pdflatex ref >> /dev/null

tutor.pdf: tutor.tex minlog.bib
	pdflatex tutor >> /dev/null
	bibtex -terse tutor
	makeindex -q tutor
	pdflatex tutor >> /dev/null
	pdflatex tutor >> /dev/null

clean: 	cleanup
	rm -rf .dep .dep.*
	rm -rf *.dvi *.pdf *.ps
	rm -rf *~ *%
	ls -sh

cleanup:
	rm -rf *.aux *.log *.blg *.bbl *.idx *.toc *.ind *.ilg *.brf *.out
