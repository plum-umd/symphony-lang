dnl
dnl For the copyright information for this file, please search up the
dnl directory tree for the first README file.
dnl

[

]AC_INIT(
  [[PSL]],
  [[0.1.0.0]],
  [[]],
  [[psl]],
  [[]])[

]AC_CONFIG_AUX_DIR([build-aux])[
]AC_CONFIG_MACRO_DIR([m4])[
]AC_CONFIG_MACRO_DIRS([m4])[
]AC_CONFIG_SRCDIR([main/PSLI.hs])[

]AM_INIT_AUTOMAKE([
  -Wall
  foreign
  nostdinc
  subdir-objects
  tar-ustar
])[

]DEFINE_ALL[

]dnl begin_includes
[

]m4_include([build-aux/autogen.ac])[

]dnl end_includes
[

]AC_ARG_VAR([STACK], [the command to use to run stack (Haskell build tool)])[

]AC_CHECK_PROGS([STACK], [stack])[

]dnl
dnl AC_CACHE_CHECK(
dnl   [if stack is the correct one],
dnl   [psl_cv_stack_check],
dnl   [
dnl     case "$STACK" in
dnl       "stack") ;;
dnl       *)
dnl 	printf 'no\n'
dnl         AC_MSG_ERROR(
dnl [Cannot find stack.
dnl Installation instructions: https://www.haskell.org/downloads/])
dnl       ;;
dnl     esac
dnl 
dnl     case "`stack --help`" in
dnl       *'The Haskell Tool Stack'*) ;;
dnl       *)
dnl         printf 'no\n'
dnl         AC_MSG_ERROR(
dnl [The "stack" program does not appear to be the correct one.
dnl Try using "./configure STACK=/path/to/stack".])
dnl       ;;
dnl     esac
dnl 
dnl     psl_cv_stack_check=yes
dnl   ])
[

]dnl begin_prerequisites
[

]GATBPS_CONFIG_FILE([Dockerfile])[

]dnl end_prerequisites
[

]dnl begin_prerequisites
[

]GATBPS_CONFIG_FILE_SUBST[
]GATBPS_CONFIG_LATER_SUBST[
]GATBPS_WGET_SUBST[

]dnl end_prerequisites
[

]AC_CONFIG_FILES([Makefile])[

]AC_OUTPUT[

]
