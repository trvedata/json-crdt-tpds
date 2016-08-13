.SUFFIXES: .tex .bib .aux .bbl .dvi .ps .pdf

all:
	echo "You probably want 'make mk' or 'make arb'"

mk:	trvesync.pdf

arb:	trvesync-arb.pdf

%.pdf:	%.bbl
	pdflatex $(@:.pdf=)
	pdflatex $(@:.pdf=)

%.bbl:	references.bib %.aux
	bibtex $(@:.bbl=)

%.aux:	*.tex
	pdflatex $(@:.aux=)

arxiv.tex: trvesync.tex trvesync.bbl
	sed -e '/\\bibliography{references}/ r trvesync.bbl' -e '/\\bibliography{references}/ d' trvesync.tex > arxiv.tex

clean:
	rm -f *.{log,aux,out,bbl,blg,dvi,ps,pdf} arxiv.tex

edit:
	../trvesync/ruby/bin/crdt-editor -w ws://localhost:8080/events -j 4b87a910194e52e09b11c46757811001 trvesync.tex

arbedit:
	ssh -f -L 8085:localhost:8080 trvedata-trvedb.dtg.cl.cam.ac.uk sleep 10
	~/git/op-crdt/ruby/bin/crdt-editor -w ws://localhost:8085/events trvesync-arb.tex
