OUT := body.pdf

build: clean
	# pandoc body.md -f markdown --pdf-engine=lualatex -H h-luatexja.tex -V documentclass=ltjsarticle  -o $(OUT)

	pandoc body.md -o body.pdf --from markdown --template eisvogel --listings --pdf-engine "xelatex" -V CJKmainfont="HiraginoSans-W4"


clean:
	rm -f $(OUT)

open:
	open $(OUT)
