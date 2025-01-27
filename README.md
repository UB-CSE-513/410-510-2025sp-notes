# UB CSE 410/510 "Theory of Programming Languages" Class Notes

This contains all of the lecture notes from CSE 410/510 in Spring 2025 (Theory of Programming Languages). The notes were written by Professor Andrew K. Hirsch and members of the class.

## Building

The notes are written in a combination of (lua)latex and literate agda. Both a modern texlive (everything here tested with 2024 texlive) and agda are required. Agda code is rendered in the Fira Code font; this font is also required. On Ubuntu, you can install it using `sudo apt-get install font-firacode`. Other systems have similarly easy installation stories; see [the Fira Code Github page](https://github.com/tonsky/FiraCode).

The easiest way of building the notes is by running `make`. This will build all of the notes into pdf files.

Alternatively, `.tex` files can be built using `latexmk` as follows: `latexmk --pdf -shell-escape --synctex=1 --pdflatex=lualatex $FILE` (replacing `$FILE` with the name of the file you want to build).
In order to build a `.tex` file from a `.lagda.tex` file, you must use `agda` as follows: `agda --latex --latex-dir=. $FILE`.

## Contributing

Students are expected to contribute notes regularly, according to an agreed-upon class schedule.
In order to do so, they should fork this repository and submit a pull request.
All notes should be named `lecXX.tex` or `lecXX.lagda.tex`, depending on whether they are written in pure (lua)latex or in literage agda.
