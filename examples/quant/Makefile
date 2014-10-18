# $Id: Makefile 2156 2008-01-25 13:25:12Z schimans $
# Makefile for quant

# The targets to be tested. Use .FILE.test-passed as target, if
# FILE.scm has to be tested. Use DIR/.TEST as target if a subdir has
# to be tested

.TEST: 	.quant.test-passed .orevkov.test-passed .hofmann.test-passed \
	.lnf.test-passed .los.test-passed
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

