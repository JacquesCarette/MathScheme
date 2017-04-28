THEORY = T1.tex T2.tex T2a.tex T3.tex T4.tex T5.tex T6.tex T7.tex T8.tex
INFRA = Language.tex NatVar.tex DefiniteDescr.tex Equiv.tex Variables.tex
NUMS = Numerals.tex NumPlus.tex NumPlusTimes.tex

all: formalizing-mk.pdf

formalizing-mk.pdf: formalizing-mk.tex $(THEORY) $(INFRA) app-ctt.tex $(NUMS)
	pdflatex formalizing-mk.tex

T1.tex: T1.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T1.lagda

T2.tex: T2.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T2.lagda

T2a.tex: T2a.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T2a.lagda

T3.tex: T3.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T3.lagda

T4.tex: T4.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T4.lagda

T5.tex: T5.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T5.lagda

T6.tex: T6.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T6.lagda

T7.tex: T7.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T7.lagda

T8.tex: T8.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. T8.lagda

Language.tex: Language.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. Language.lagda

NatVar.tex: NatVar.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. NatVar.lagda

Equiv.tex: Equiv.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. Equiv.lagda

Numerals.tex: Numerals.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. Numerals.lagda

NumPlus.tex: NumPlus.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. NumPlus.lagda

NumPlusTimes.tex: NumPlusTimes.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. NumPlusTimes.lagda

DefiniteDescr.tex: DefiniteDescr.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. DefiniteDescr.lagda

Variables.tex: Variables.lagda
	agda --allow-unsolved-metas --latex -i . --latex-dir=. Variables.lagda

clean:
	rm -f *.{aux,bbl,bcf,blg,fls,flx,ilg,lof,log,lop,ptb,out,toc}

.PHONY: all clean
