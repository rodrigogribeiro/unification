default: pdf

clean :
	rm *.pdf
	rm *.toc
	rm *.aux
	rm *.log
	rm *.blg

pdf:  
	pdflatex unify.tex
	bibtex unify
	pdflatex unify.tex
	pdflatex unify.tex
