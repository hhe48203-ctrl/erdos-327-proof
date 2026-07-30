.PHONY: pdf clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	bibtex main
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	mkdir -p ../output/pdf
	cp main.pdf ../output/pdf/erdos-327-variants.pdf

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.pdf
