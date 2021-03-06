# 2020-09-10
# Makefile for the examples

# The targets to be tested. Use .FILE.test-passed as target, if
# FILE.scm has to be tested. Use DIR/.TEST as target if a subdir has
# to be tested

all: .TEST

.TEST:	test/.TEST arith/.TEST analysis/.TEST classical/.TEST parsing/.TEST \
        quant/.TEST prop/.TEST hounif/.TEST lambda/.TEST pruning/.TEST \
        warshall/.TEST dc/.TEST bar/.TEST fan/.TEST \
        train/.TEST 
	touch .TEST

# .TEST:	test/.TEST arith/.TEST analysis/.TEST classical/.TEST parsing/.TEST \
#         quant/.TEST prop/.TEST hounif/.TEST lambda/.TEST pruning/.TEST \
#         warshall/.TEST dijkstra/.TEST dc/.TEST bar/.TEST fan/.TEST deco/.TEST \
#         train/.TEST 
# 	touch .TEST

# .TEST:	test/.TEST quant/.TEST prop/.TEST hounif/.TEST arith/.TEST \
# 	warshall/.TEST dijkstra/.TEST classical/.TEST dc/.TEST \
# 	bar/.TEST analysis/.TEST # .insertsort.test-passed
# 	touch .TEST

# The relative path to the toplevel Minlog-Dir
TOP= ../


# The recursive calls:

test/.TEST: .always
	(cd test; $(MAKE) .TEST)

arith/.TEST: .always
	(cd arith; $(MAKE) .TEST)

analysis/.TEST: .always
	(cd analysis; $(MAKE) .TEST)

classical/.TEST: .always
	(cd classical; $(MAKE) .TEST)

parsing/.TEST: .always
	(cd parsing; $(MAKE) .TEST)

quant/.TEST: .always
	(cd quant; $(MAKE) .TEST)

prop/.TEST: .always
	(cd prop; $(MAKE) .TEST)

hounif/.TEST: .always
	(cd hounif; $(MAKE) .TEST)

lambda/.TEST: .always
	(cd lambda; $(MAKE) .TEST)

pruning/.TEST: .always
	(cd pruning; $(MAKE) .TEST)

warshall/.TEST: .always
	(cd warshall; $(MAKE) .TEST)

# dijkstra/.TEST: .always
# 	(cd dijkstra; $(MAKE) .TEST)

dc/.TEST: .always
	(cd dc; $(MAKE) .TEST)

bar/.TEST: .always
	(cd bar; $(MAKE) .TEST)

fan/.TEST: .always
	(cd fan; $(MAKE) .TEST)

# deco/.TEST: .always
# 	(cd deco; $(MAKE) .TEST)

train/.TEST: .always
	(cd train; $(MAKE) .TEST)

# clean has to be implemented at each level. Always have genericclean as a
# dependency

clean: genericclean
	(cd test; $(MAKE) clean)
	(cd arith; $(MAKE) clean)
	(cd analysis; $(MAKE) clean)
	(cd classical; $(MAKE) clean)
	(cd parsing; $(MAKE) clean)
	(cd quant; $(MAKE) clean)
	(cd prop; $(MAKE) clean)
	(cd hounif; $(MAKE) clean)
	(cd lambda; $(MAKE) clean)
	(cd pruning; $(MAKE) clean)
	(cd warshall; $(MAKE) clean)
	(cd dc; $(MAKE) clean)
	(cd bar; $(MAKE) clean)
	(cd fan; $(MAKE) clean)
	(cd train; $(MAKE) clean)

# clean: genericclean
# 	(cd test; $(MAKE) clean)
# 	(cd arith; $(MAKE) clean)
# 	(cd analysis; $(MAKE) clean)
# 	(cd classical; $(MAKE) clean)
# 	(cd parsing; $(MAKE) clean)
# 	(cd quant; $(MAKE) clean)
# 	(cd prop; $(MAKE) clean)
# 	(cd hounif; $(MAKE) clean)
# 	(cd lambda; $(MAKE) clean)
# 	(cd warshall; $(MAKE) clean)
# 	(cd dijkstra; $(MAKE) clean)
# 	(cd dc; $(MAKE) clean)
# 	(cd bar; $(MAKE) clean)
# 	(cd fan; $(MAKE) clean)
# 	(cd deco; $(MAKE) clean)
# 	(cd train; $(MAKE) clean)

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

