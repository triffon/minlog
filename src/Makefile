## $Id: Makefile 2566 2012-10-18 14:51:53Z schwicht $
## Makefile for subdirectory src

all: TAGS .dep.notags


srcs = $(shell ls *.scm)

.dep.notags: minitab.scm

TAGS: $(srcs)
	etags `ls *.scm`

clean:
	rm -rf .dep .dep.*
	rm -rf TAGS
	rm -rf *~ *%
	rm -rf grammar.log

minitab.scm: grammar.scm lalr.scm
	rm -f minitab.scm
	if which petite > /dev/null; then \
		echo "Using petite to build parser..."; \
		petite grammar.scm > grammar.log; \
	elif which mzscheme > /dev/null; then \
		if [ -z "`mzscheme -v | sed -e 's/.*v[456].*//'`" ]; then \
			echo "Using mzscheme (>= v4) to build parser..."; \
			mzscheme -l mzscheme -l r5rs -f grammar.scm > grammar.log; \
		else \
			echo "Using mzscheme (< v4) to build parser..."; \
			mzscheme -f grammar.scm > grammar.log; \
		fi; \
	elif which guile > /dev/null; then \
		echo "Using guile to build parser..."; \
		guile grammar.scm > grammar.log; \
	else \
		echo "Please install either Petite Scheme, MzScheme, or Guile to build the parser!"; \
		false; \
	fi
