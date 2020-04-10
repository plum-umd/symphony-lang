dnl
dnl For the copyright information for this file, please search up the
dnl directory tree for the first README file.
dnl

[

]AC_INIT(
  [[PSL]],
  m4_esyscmd_s([
    bash build-aux/VERSION.bash
  ])m4_if(m4_sysval, [0], [], [m4_fatal([VERSION.bash failed])]),
  [[]],
  [[psl]],
  [[]])[

]GATBPS_DEFINE_DATE(
  [AC_],
  [PACKAGE_DATE],
  m4_esyscmd_s([
    sh build-aux/DATE.sh
  ])m4_if(m4_sysval, [0], [], [m4_fatal([DATE.sh failed])]))[

]AC_CONFIG_AUX_DIR([build-aux])[
]AC_CONFIG_MACRO_DIR([m4])[
]AC_CONFIG_MACRO_DIRS([m4])[
]AC_CONFIG_SRCDIR([src/PSL.hs])[

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
]m4_include([src/posix-like/bin/psl.ac])[

]dnl end_includes
[

]AC_ARG_VAR([STACK], [the command to use to run stack (Haskell build tool)])[

]AC_CHECK_PROGS([STACK], [stack])[

]AC_CACHE_CHECK(
  [if ${STACK:-stack} is indeed The Haskell Tool Stack],
  [psl_cv_stack_check],
  [[
    psl_cv_stack_check=no
    case "$STACK" in
      ?*)
        STACK_HELP=`eval " $STACK --help" 2>&1`
        printf '%s\n' "$STACK_HELP" >&]AS_MESSAGE_LOG_FD[
        case $STACK_HELP in
          *'The Haskell Tool Stack'*) psl_cv_stack_check=yes ;;
        esac
      ;;
    esac
  ]])[

case $psl_cv_stack_check in
  yes)
    STACK_MISSING=no
  ;;
  *)
    STACK_MISSING=yes
    ]AC_MSG_WARN(
[Haskell Stack is not installed.
Follow these installation instructions: https://www.haskell.org/downloads/.
If it is installed, use "./configure STACK=/path/to/stack".
The Docker image can be built without Stack being installed.])[
  ;;
esac
]AC_SUBST([STACK_MISSING])[

]AC_CACHE_CHECK(
  [if ${STACK:-stack} is new enough],
  [psl_cv_stack_version_check],
  [[
    psl_cv_stack_version_check=no
    case "$psl_cv_stack_check" in
      yes)
        while :; do
          eval " $STACK --numeric-version 2>&1" > conftest_stack_version.txt || break
          STACK_VERSION=`cat conftest_stack_version.txt` || exit $?
          printf '%s\n' "$STACK_VERSION" >&]AS_MESSAGE_LOG_FD[
          grep '^\(0\|[1-9][0-9]*\)\.\(0\|[1-9][0-9]*\)\.\(0\|[1-9][0-9]*\)$' conftest_stack_version.txt >/dev/null
          case $? in
            0) ;;
            1) break ;;
            *) exit $? ;;
          esac
          case "$STACK_VERSION" in
            2.1.[3-9] | 2.1.??* | \
            2.[2-9].* | 2.??*.* | \
            [3-9].*.* | ??*.*.* \
            ) psl_cv_stack_version_check=yes ;;
          esac
          break
        done
      ;;
      esac
  ]])[

case $psl_cv_stack_version_check in
  yes)
    STACK_OLD=no
  ;;
  *)
    STACK_OLD=yes
    ]AC_MSG_WARN(
[Haskell Stack is too old to build this project.
The Docker image can be built without Stack.])[
  ;;
esac
]AC_SUBST([STACK_OLD])[

]dnl begin_includes
[

]GATBPS_CONFIG_FILE([Dockerfile])[
]GATBPS_CONFIG_FILE([package.yaml])[

]dnl end_includes
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
