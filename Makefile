STYLES := lecturenotes.cls

.PHONY: all clean cleanall

TEX_FILES = $(shell find . -maxdepth 1 -name '*.tex' -type f -not -name '*.lagda.tex')
AGDA_TEX_FILES = $(shell find . -maxdepth 1 -name '*.lagda.tex' -type f | cut -d/ -f2 -)
TEX_FILES += $(AGDA_TEX_FILES:.lagda.tex=.tex)

export TEXINPUTS = .::$TEXMF/tex::../pl-syntax


all: $(TEX_FILES:.tex=.pdf)

%.pdf: %.tex $(STYLES)
	latexmk -pdf -shell-escape -synctex=1 -pdflatex=lualatex $<

%.tex: %.lagda.tex
	agda --latex --latex-dir=. $<


clean:
	@find . \( -name '*.aux'\
		-o -name '*~'\
		-o -name '*.synctex.gz'\
		-o -name '*.blg'\
		-o -name '*.toc'\
		-o -name '*.lot'\
		-o -name '*.fls'\
		-o -name '*.fdb_latexmk'\
		-o -name '*.xcp'\
		-o -name '*.xoj'\
		-o -name '*.lof'\
		-o -name '*.log'\
		-o -name '*.out'\
		\) -type f -not -path "./.git/*" -not -path "./src/*"\
	     -exec sh -c 'echo "REMOVING {}"; rm "{}"' ';'

cleanall:
	@find . \( -name '*.aux'\
		-o -name '*~'\
		-o -name '*.synctex.gz'\
		-o -name '*.blg'\
		-o -name '*.toc'\
		-o -name '*.lot'\
		-o -name '*.fls'\
		-o -name '*.fdb_latexmk'\
		-o -name '*.xcp'\
		-o -name '*.xoj'\
		-o -name '*.lof'\
		-o -name '*.log'\
		-o -name '*.out'\
		-o -name '*.pdf'\
		-o -name '*.dvi'\
		-o -name '*.agdai'\
		-o -name '*.ptb'\
		\) -type f -not -path "./.git/*" -not -path "./src/*"\
	     -exec sh -c 'echo "REMOVING {}"; rm "{}"' ';';
	@find . \( -name 'auto'\
		-o -name '_minted*'\
	        \) -type d -not -path "./.git/*" -not -path "./src/*" -prune\
	     -exec sh -c 'echo "REMOVING {}"; rm -r "{}"' ';'
