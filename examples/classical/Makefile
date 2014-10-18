# Makefile for classical

# The targets to be tested. Use .FILE.test-passed as target, if
# FILE.scm has to be tested. Use DIR/.TEST as target if a subdir has
# to be tested

.TEST:  .wftest.test-passed .tape.test-passed .root.test-passed \
        .rev.test-passed .hsh.test-passed .fib.test-passed \
        .euclid.test-passed .gcd.test-passed .dickson.test-passed
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
