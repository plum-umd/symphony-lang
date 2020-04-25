##
## For the copyright information for this file, please search up the
## directory tree for the first README file.
##

## begin_variables

EXTRA_DIST =
EXTRA_DIST += $(psl_files)
EXTRA_DIST += COMMIT
EXTRA_DIST += DATE
EXTRA_DIST += VERSION

MOSTLYCLEANFILES =
MOSTLYCLEANFILES += psl

TMPEXT = .tmp

bin_PROGRAMS =

copy_vpath_files = \
  vpath_files=; \
  for x in $(psl_files); do \
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
$(prevent_an_empty_line)

stack_check = \
  case '$(STACK_MISSING)' in \
    'yes') \
      printf 'Haskell Stack is not available. Please install it and re-run ./configure.\n' >&2; \
      exit 1; \
    ;; \
  esac \
$(prevent_an_empty_line)

stack_version_check = \
  case '$(STACK_OLD)' in \
    'yes') \
      printf 'Haskell Stack is too old for this project. Please upgrade it and re-run ./configure.\n' >&2; \
      exit 1; \
    ;; \
  esac \
$(prevent_an_empty_line)

hs_files =

libexec_psl_SCRIPTS =
libexec_psl_SCRIPTS += psl

libexec_psldir = $(libexecdir)/psl

nobase_dist_share_psl_DATA =

psl_files =
psl_files += $(hs_files)
psl_files += package.yaml
psl_files += stack.yaml

share_psldir = $(datadir)/psl

## end_variables

## begin_rules

.PHONY: FORCE
.PHONY: docker
.PHONY: resource-estimation.tar.gz/clean

COMMIT:
	bash build-aux/COMMIT.bash >COMMIT$(TMPEXT)
	mv COMMIT$(TMPEXT) COMMIT

DATE:
	sh build-aux/DATE.sh >DATE$(TMPEXT)
	mv DATE$(TMPEXT) DATE

FORCE:

VERSION:
	bash build-aux/VERSION.bash >VERSION$(TMPEXT)
	mv VERSION$(TMPEXT) VERSION

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
	  $(DOCKER) build -t psl:latest . || exit; \
	  $(DOCKER) tag psl:latest psl:$(PACKAGE_VERSION) || exit; \
	}

mostlyclean-local: psl/clean

psl: $(psl_files)
	{ \
	  $(stack_check); \
	  $(stack_version_check); \
	  $(copy_vpath_files); \
	  $(STACK) build || exit; \
	  x=`$(STACK) path --dist-dir` || exit; \
	  cp $$x/build/psl/psl $@$(TMPEXT) || exit; \
	  mv $@$(TMPEXT) $@ || exit; \
	}

psl/clean: FORCE
	{ \
	  case '$(STACK_MISSING)' in \
	    yes) ;; \
	    *) \
	      $(copy_vpath_files); \
	      $(STACK) clean --full || :; \
	    ;; \
	  esac \
	}
	-rm -f psl.cabal stack.yaml.lock

resource-estimation.tar.gz: build-aux/gitbundles/hector-mockups.gitbundle
	rm -f -r $@$(TMPEXT).tmp*
	$(GIT) clone build-aux/gitbundles/hector-mockups.gitbundle $@$(TMPEXT).tmp.repo
	cd $@$(TMPEXT).tmp.repo/resource-estimates && bash package.bash
	cp $@$(TMPEXT).tmp.repo/resource-estimates/resource-estimation.tar.gz $@

resource-estimation.tar.gz/clean: FORCE
	-rm -f $(@D) $(@D)$(TMPEXT).tmp*

## end_rules

## begin_includes

include $(srcdir)/build-aux/autogen.am
include $(srcdir)/src/posix-like/bin/psl.am

## end_includes

## begin_includes

include $(srcdir)/build-aux/GATBPS_CONFIG_FILE_RULES.am
include $(srcdir)/build-aux/GATBPS_CONFIG_LATER_RULES.am
include $(srcdir)/build-aux/GATBPS_CP_RULES.am
include $(srcdir)/build-aux/GATBPS_GIT_ARCHIVE_RULES.am
include $(srcdir)/build-aux/GATBPS_GIT_BUNDLE_RULES.am
include $(srcdir)/build-aux/GATBPS_GIT_CLONE_RULES.am
include $(srcdir)/build-aux/GATBPS_VPATH_SEARCH.am
include $(srcdir)/build-aux/GATBPS_WGET_RULES.am
include $(srcdir)/build-aux/git.am
include $(srcdir)/build-aux/wget.am

## end_includes
