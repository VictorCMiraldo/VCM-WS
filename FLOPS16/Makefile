all: flops16.tex
	rubber -d -I "$(LATEXLIB)/tex_llncs2e" flops16.tex
	
flops16.tex: flops16.lhs
	lhs2TeX --agda flops16.lhs -o flops16.tex
	
bib: flops16.tex
	bibtex flops16
