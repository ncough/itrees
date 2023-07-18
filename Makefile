all: output/document.pdf

clean:
	rm -rf output

output/document.pdf: 
	isabelle build -D . -c
