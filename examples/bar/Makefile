# 2020-09-13.
# Makefile for bar

# The targets to be tested. Use .FILE.test-passed as target, if
# FILE.scm has to be tested. Use DIR/.TEST as target if a subdir has
# to be tested

all: .TEST

.TEST: .bar.test-passed .higman01.test-passed .higfin.test-passed
	touch .TEST

# .TEST: .bar.test-passed .higman01.test-passed .higfin.test-passed \
#        .higwqo.test-passed .higman.test-passed
# 	touch .TEST


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

