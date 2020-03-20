[

]AC_INIT(
  [[PSL]],
  [[0.0.0]],
  [[]],
  [[psl]],
  [[]])[

]AM_INIT_AUTOMAKE([
  -Wall
  foreign
  nostdinc
  subdir-objects
  tar-ustar
])[

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

]AC_CONFIG_FILES([Makefile])[

]AC_OUTPUT[

]
