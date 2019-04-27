all: WG211-meta-agda.pdf

WG211-meta-agda.pdf: latex/AgdaMeta.tex WG211-meta-agda.tex
	latexmk -pdf -use-make WG211-meta-agda.tex

latex/AgdaMeta.tex: AgdaMeta.lagda
	agda --latex AgdaMeta.lagda
