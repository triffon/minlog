# 2020-08-15
# Makefile for analysis

# The targets to be tested. Use .FILE.test-passed as target, if
# FILE.scm has to be tested. Use DIR/.TEST as target if a subdir has
# to be tested

.TEST:  .ivt.test-passed .sddiv.test-passed .graydiv.test-passed \
        .sdmult.test-passed .graymult.test-passed .sdlim.test-passed \
        .ishihara.test-passed
	touch .TEST

# .TEST:  .ivt.test-passed .ishihara.test-passed .ratsds.test-passed \
#         .cauchysds.test-passed .average.test-passed \
#         .readwrite.test-passed .gray.test-passed
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

