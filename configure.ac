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

]AC_CACHE_CHECK(
  [if stack is the correct one],
  [psl_cv_stack_check],
  [
    case "$STACK" in
      "stack") ;;
      *)
	printf 'no\n'
        AC_MSG_ERROR(
[Cannot find stack.
Installation instructions: https://www.haskell.org/downloads/])
      ;;
    esac

    case "`stack --help`" in
      *'The Haskell Tool Stack'*) ;;
      *)
        printf 'no\n'
        AC_MSG_ERROR(
[The "stack" program does not appear to be the correct one.
Try using "./configure STACK=/path/to/stack".])
      ;;
    esac

    psl_cv_stack_check=yes
  ])[

]AC_CONFIG_FILES([Makefile])[

]AC_OUTPUT[

]
