.PHONY: all check

all: output/document.pdf

output/document.pdf: Highway.thy document/root.tex
	isabelle build -c -v -d $(CURDIR) Highway
	touch $@

clean:
	rm -rf output
