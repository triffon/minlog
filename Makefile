## $Id: Makefile 2373 2010-04-11 11:21:04Z shuber $
# There are several possibilities to install Minlog:

# INSTALLATION IN CURRENT DIRECTORY
# > make

# INSTALLATION IN LOCAL DIRECTORY (i.e. /usr/local)
# > make install

# INSTALLATION IN SYSTEMS DIRECTORIES (i.e. /usr)
# make install DESTDIR=/usr

INSTALL=install
INSTALL_FILE=$(INSTALL) -D -p -m 644
INSTALL_DIR=$(INSTALL) -p -d -m 755
DESTDIR=/usr/local
PREFIX=
MINLOGDIR=$(DESTDIR)/share/minlog
DOCDIR=$(DESTDIR)/share/doc/minlog
BINDIR=$(DESTDIR)/bin
ELDIR=$(DESTDIR)/share/emacs/site-lisp/minlog

## Makefile for Minlog. As most of the minlog project are just scheme sources
## there's not much to be done. However it's nice to have some form of
## interface for it.
## The semantics of all the Makefiles used is the same:
##  -- .dep    is the file that signals, when the dependencies have been
##             checked for the last time. This file is always younger
##             than the last check of all dependencies in all subdirectories
##  -- clean   the target used to clean up the source. Should also remove
##             all the .dep files.

all: src init.scm minlog minlog.el doc

install: src init.scm minlog minlog.el doc
	$(INSTALL_DIR) $(PREFIX)$(MINLOGDIR) $(PREFIX)$(BINDIR) $(PREFIX)$(ELDIR)
	sed "s%---MINLOGPATH---%"$(MINLOGDIR)"%g; s%---MINLOGELPATH---%"$(ELDIR)"%g" < src/minlog.el > $(PREFIX)$(ELDIR)/minlog.el
	sed "s%---MINLOGPATH---%"$(ELDIR)"%g" < src/minlog > $(PREFIX)$(BINDIR)/minlog
	chmod a+x $(PREFIX)$(BINDIR)/minlog
	sed "s%---MINLOGPATH---%"$(MINLOGDIR)"%g; s%(minlog-load \"examples/\" path))%(load (string-append \""$(DOCDIR)"/examples/\" path)))%g" < src/init.scm > $(PREFIX)$(MINLOGDIR)/init.scm
	(cd src; find . -name '*.scm' -type f -exec $(INSTALL_FILE) {} $(PREFIX)$(MINLOGDIR)/src/{} \;)
	(cd lib; find . -name '*.scm' -type f -exec $(INSTALL_FILE) {} $(PREFIX)$(MINLOGDIR)/lib/{} \;)
	(cd examples; find . -type f -exec $(INSTALL_FILE) {} $(PREFIX)$(DOCDIR)/examples/{} \;)
	(cd doc; find . -name '*.pdf' -type f -exec $(INSTALL_FILE) {} $(PREFIX)$(DOCDIR)/{} \;)

minlog.el: src/minlog.el src
	sed "s%---MINLOGPATH---%`pwd`%g; s%---MINLOGELPATH---%`pwd`%g" < src/minlog.el > minlog.el

minlog: src/minlog src
	sed "s%---MINLOGPATH---%`pwd`%g" < src/minlog > minlog
	chmod a+x minlog

init.scm: src/init.scm src
	sed "s%---MINLOGPATH---%`pwd`%g" < src/init.scm > init.scm

doc: doc/.dep
doc/.dep:
	(cd doc; $(MAKE) .dep)

src: src/.dep.notags
src/.dep.notags:
	(cd src; $(MAKE) .dep.notags)

test: examples/.TEST

newtest:
	(cd examples; $(MAKE) clean)
	($(MAKE) test)

alltest:
	(cd examples; $(MAKE) clean)
	($(MAKE) -k -i test)

examples/.TEST: init.scm
	(cd examples; $(MAKE) .TEST)

clean:
	rm -rf *~
	rm -rf init.scm minlog minlog.el welcome.scm
	(cd src; $(MAKE) clean)
	(cd doc; $(MAKE) clean)
	(cd examples; $(MAKE) clean)
