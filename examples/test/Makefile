# $Id: Makefile 2012-12-31 miyamoto $
# Makefile for test

# The targets to be tested. Use .FILE.test-passed as target, if
# FILE.scm has to be tested. Use DIR/.TEST as target if a subdir has
# to be tested

.TEST:  .typ.test-passed .var.test-passed \
	.pconst.test-passed .psym.test-passed \
	.term.test-passed .formula.test-passed \
	.axiom.test-passed .proof.test-passed \
	.pproof.test-passed .ets.test-passed
	touch .TEST

# The relative path to the toplevel Minlog-Dir
TOP= ../../

# clean has to be implemented at each level. Always have genericclean as a
# dependency

clean: genericclean

#
# Now include the standard rules for testing:
#
include ../Makefile.template


## How it works:
## entry point is always the target .TEST
## Then for every file we have to produce the file .FILE.test-passed

