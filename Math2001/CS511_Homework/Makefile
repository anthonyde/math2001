.PHONY: all clean

all: hw1.pdf hw2.pdf hw3.pdf hw4.pdf

clean:
	rm -f *.aux *.log *.pdf

%.pdf: %.tex
	pdflatex $^
