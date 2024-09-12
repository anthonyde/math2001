.PHONY: all clean

all: hw1.pdf

clean:
	rm -f *.aux *.log *.pdf

%.pdf: %.tex
	pdflatex $^
