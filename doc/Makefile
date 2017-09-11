
GAP=gap

gapdoc:
	@echo 'RequirePackage("gapdoc");; MakeGAPDocDoc( "./", "comptom", ["../gap/subgroups.gd","../gap/solvabletom.gd", "../gap/impressions.gd" ], "comptom" );;' | $(GAP) -q -T

clean:
	@rm -f comptom.aux comptom.bbl comptom.blg comptom.idx comptom.ilg comptom.ind comptom.log comptom.pnr comptom.tex comptom.toc comptom.brf comptom.out
	@rm -f *~


spotless: clean
	@rm -f manual.dvi manual.html manual.ps manual.pdf manual.six
	@rm -f chap*.html chap*.txt *.xml.bib
