##
## For the copyright information for this file, please search up the
## directory tree for the first README file.
##

## begin_variables

EXTRA_DIST =
EXTRA_DIST += $(psli_files)

MOSTLYCLEANFILES =
MOSTLYCLEANFILES += psli

TMPEXT = .tmp

bin_SCRIPTS =
bin_SCRIPTS += psli

copy_vpath_files = \
  vpath_files=; \
  for x in $(psli_files); do \
    if test -r $$x; then \
      :; \
    else \
      vpath_files="$$vpath_files $$x"; \
    fi; \
  done; \
  readonly vpath_files; \
  trap 'rm -f $$vpath_files' EXIT; \
  for x in $$vpath_files; do \
    $(MKDIR_P) $$x || exit; \
    rmdir $$x || exit; \
    cp $(srcdir)/$$x $$x || exit; \
  done \
$(empty)

hs_files =

psli_files =
psli_files += $(hs_files)
psli_files += package.yaml
psli_files += stack.yaml

## end_variables

## begin_rules

.PHONY: FORCE
.PHONY: docker

FORCE:

docker: Dockerfile
docker: dist-gzip
	@case '$(DOCKER)' in \
	  '') \
	    printf 'DOCKER is unset\n' >&2; \
	    exit 1; \
	  ;; \
	esac
	{ \
	  $(copy_vpath_files); \
	  $(DOCKER) build -t psl . || exit; \
	}

mostlyclean-local: psli/clean

psli: $(psli_files)
	{ \
	  $(copy_vpath_files); \
	  $(STACK) build || exit; \
	  x=`$(STACK) path --dist-dir` || exit; \
	  cp $$x/build/psli/psli $@$(TMPEXT) || exit; \
	  mv $@$(TMPEXT) $@ || exit; \
	}

psli/clean: FORCE
	{ \
	  $(copy_vpath_files); \
	  $(STACK) clean --full || :; \
	}
	-rm -f psl.cabal stack.yaml.lock

## end_rules

## begin_includes

include $(srcdir)/build-aux/autogen.am

## end_includes

## begin_includes

include $(srcdir)/build-aux/GATBPS_CONFIG_FILE_RULES.am
include $(srcdir)/build-aux/GATBPS_CONFIG_LATER_RULES.am
include $(srcdir)/build-aux/GATBPS_WGET_RULES.am
include $(srcdir)/build-aux/wget.am

## end_includes
