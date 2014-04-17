# $Id: Makefile 2603 2013-01-03 18:25:17Z miyamoto $
# Makefile for the examples

# The targets to be tested. Use .FILE.test-passed as target, if
# FILE.scm has to be tested. Use DIR/.TEST as target if a subdir has
# to be tested

all: .TEST

.TEST:	test/.TEST arith/.TEST analysis/.TEST parsing/.TEST
	touch .TEST

# .TEST:	test/.TEST quant/.TEST prop/.TEST hounif/.TEST arith/.TEST \
# 	warshall/.TEST dijkstra/.TEST classical/.TEST dc/.TEST \
# 	bar/.TEST analysis/.TEST # .insertsort.test-passed
# 	touch .TEST

# The relative path to the toplevel Minlog-Dir
TOP= ../


# The recursive calls:

analysis/.TEST: .always
	(cd analysis; $(MAKE) .TEST)

arith/.TEST: .always
	(cd arith; $(MAKE) .TEST)

bar/.TEST: .always
	(cd bar; $(MAKE) .TEST)

test/.TEST: .always
	(cd test; $(MAKE) .TEST)

dc/.TEST: .always
	(cd dc; $(MAKE) .TEST)

classical/.TEST: .always
	(cd classical; $(MAKE) .TEST)

hounif/.TEST: .always
	(cd hounif; $(MAKE) .TEST)

prop/.TEST: .always
	(cd prop; $(MAKE) .TEST)

quant/.TEST: .always
	(cd quant; $(MAKE) .TEST)

warshall/.TEST: .always
	(cd warshall; $(MAKE) .TEST)

dijkstra/.TEST: .always
	(cd dijkstra; $(MAKE) .TEST)


# clean has to be implemented at each level. Always have genericclean as a
# dependency

clean: genericclean
	(cd test; $(MAKE) clean)
	(cd analysis; $(MAKE) clean)
	(cd arith; $(MAKE) clean)

# clean: genericclean
# 	(cd classical; $(MAKE) clean)
# 	(cd hounif; $(MAKE) clean)
# 	(cd prop; $(MAKE) clean)
# 	(cd quant; $(MAKE) clean)
# 	(cd warshall; $(MAKE) clean)
# 	(cd dijkstra; $(MAKE) clean)
# 	(cd bar; $(MAKE) clean)
# 	(cd dc; $(MAKE) clean)
# 	(cd test; $(MAKE) clean)
# 	(cd analysis; $(MAKE) clean)
# 	(cd arith; $(MAKE) clean)

# Now include the standard rules for testing:
include Makefile.template


## How it works:
## entry point is always the target .TEST
## Then for every file we have to produce the file .FILE.test-passed

