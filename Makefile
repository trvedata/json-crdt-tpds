.SUFFIXES: .tex .bib .aux .bbl .dvi .ps .pdf

all:	trvesync.pdf

trvesync.pdf:	trvesync.bbl
	pdflatex trvesync
	pdflatex trvesync

trvesync.bbl:	references.bib trvesync.aux
	bibtex trvesync

trvesync.aux:	*.tex
	pdflatex trvesync

clean:
	rm -f *.{log,aux,out,bbl,blg,dvi,ps,pdf}

edit:
	../trvesync/ruby/bin/crdt-editor -w ws://localhost:8080/events -j 4b87a910194e52e09b11c46757811001 trvesync.tex
