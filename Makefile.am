##
## For the copyright information for this file, please search up the
## directory tree for the first README file.
##

## begin_variables

EXTRA_DIST =
EXTRA_DIST += $(psli_files)

TMPEXT = .tmp

bin_SCRIPTS =
bin_SCRIPTS += psli

hs_files =

psli_files =
psli_files += $(hs_files)
psli_files += package.yaml
psli_files += stack.yaml

## end_variables

## begin_rules

psli: $(psli_files)
	$(STACK) build
	{ \
	  x=`$(STACK) path --dist-dir` || exit; \
	  cp "$$x"/build/psli/psli $@$(TMPEXT) || exit; \
	  mv $@$(TMPEXT) $@ || exit; \
	}

## end_rules

## begin_includes

include $(srcdir)/build-aux/autogen.am

## end_includes

## begin_includes

include $(srcdir)/build-aux/GATBPS_WGET_RULES.am
include $(srcdir)/build-aux/wget.am

## end_includes
