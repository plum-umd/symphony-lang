dnl
dnl This file was generated by GATBPS 0.1.0-5435+g3887bad2, which was
dnl released on 2020-04-21. Before changing it, make sure
dnl you're doing the right thing. Depending on how GATBPS
dnl is being used, your changes may be automatically lost.
dnl A short description of this file follows.
dnl
dnl Special file: GATBPS_CONFIG_LATER.m4
dnl
dnl For more information, see the GATBPS manual.
dnl
#serial 20200421
AC_DEFUN([GATBPS_CONFIG_LATER], [[{

#
]m4_text_wrap(
  [
    The block that contains this comment is the expansion of the
    GATBPS_CONFIG_LATER macro for the $1 target.
  ],
  [# ],
  [# ],
  [72])[
#]dnl
m4_if(
  m4_eval([$# < 1 || $# > 4]),
  [1],
  [gatbps_fatal([
    GATBPS_CONFIG_LATER requires 1 to 4 arguments
    ($# ]m4_if([$#], [1], [[was]], [[were]])[ given)
  ])])[]dnl
m4_if(
  m4_bregexp([$1], [[^
	 ]]),
  [-1],
  [gatbps_fatal([
    invalid first argument for GATBPS_CONFIG_LATER:
  [--VERBATIM--] "$1"], [
    the first argument must contain at least one character that is not a
    space, tab, or newline character
  ])])[]dnl
m4_if(
  [$2],
  [],
  [],
  [m4_if(
    m4_bregexp([$2], [[^
	 ]]),
    [-1],
    [gatbps_fatal([
      invalid second argument for GATBPS_CONFIG_LATER:
    [--VERBATIM--] "$2"], [
      the second argument must contain at least one character that is
      not a space, tab, or newline character
    ])])])[]dnl
m4_case(
  [$3],
  [], [],
  [clean], [],
  [distclean], [],
  [maintainer-clean], [],
  [mostlyclean], [],
  [gatbps_fatal([
    invalid third argument for GATBPS_CONFIG_LATER:
  [--VERBATIM--] "$3"], [
    the third argument must be either empty, "clean", "distclean",
    "maintainer-clean", or "mostlyclean"
  ])])[]dnl
m4_pushdef(
  [list_4],
  m4_bpatsubst([[[$4]]], [^\(..\)[
	 ]+], [\1]))[]dnl
]m4_ifdef(
  [GATBPS_CONFIG_LATER_check_4],
  [gatbps_fatal([
    GATBPS_CONFIG_LATER_check_4 is already defined
  ])])[dnl
]m4_define(
  [GATBPS_CONFIG_LATER_check_4],
  [m4_if(
    [$#],
    [1],
    [m4_if(
      m4_bregexp([$1], [^[
	 ]+$]),
      [0],
      [gatbps_fatal([
        invalid last subargument of the fourth GATBPS_CONFIG_LATER argument:
      [--VERBATIM--] "$1"], [
        the last subargument must either be empty or contain at least
        one character that is not a space, tab, or newline character
      ])])],
    [m4_if(
      m4_bregexp([$1], [[^
	 ]]),
      [-1],
      [gatbps_fatal([
        invalid non-last subargument of the fourth GATBPS_CONFIG_LATER argument:
      [--VERBATIM--] "$1"], [
        each non-last subargument must contain at least one character
        that is not a space, tab, or newline character
      ])],
      [GATBPS_CONFIG_LATER_check_4(m4_shift($@))])])])[dnl
GATBPS_CONFIG_LATER_check_4(m4_if(,,list_4))[]dnl
m4_pushdef(
  [output_file],
  m4_bpatsubst([[[$1]]], ['], ['\\'']))[]dnl
m4_pushdef(
  [input_file],
  m4_if(
    [$2],
    [],
    [m4_bpatsubst([[[$1.im]]], ['], ['\\''])],
    [m4_bpatsubst([[[$2]]], ['], ['\\''])]))[]dnl
m4_pushdef(
  [child_prerequisites],
  m4_if(
    [$2],
    [],
    [[[[$1.im]]]],
    [[[[$2]]]]))[]dnl
m4_pushdef(
  [clean_target],
  m4_if(
    [$3],
    [],
    [[[mostlyclean]]],
    [[[$3]]]))[]dnl
m4_pushdef(
  [leaf_prerequisites],
  m4_dquote(list_4))[]dnl
m4_pushdef(
  [rule_prerequisites],
  m4_if(
    leaf_prerequisites,
    [],
    [m4_dquote(child_prerequisites)],
    [m4_dquote(leaf_prerequisites)]))[]dnl
]m4_ifdef(
  [GATBPS_CONFIG_LATER_rule_lines],
  [gatbps_fatal([
    GATBPS_CONFIG_LATER_rule_lines is already defined
  ])])[dnl
]m4_define(
  [GATBPS_CONFIG_LATER_rule_lines],
  [m4_if(
    [$1],
    [],
    [],
    [[
]output_file[: ]dnl
m4_bpatsubst([[$1]], ['], ['\\''])[]dnl
GATBPS_CONFIG_LATER_rule_lines(m4_shift($@))])])[dnl
]m4_ifdef(
  [GATBPS_CONFIG_LATER_make_lines],
  [gatbps_fatal([
    GATBPS_CONFIG_LATER_make_lines is already defined
  ])])[dnl
]m4_define(
  [GATBPS_CONFIG_LATER_make_lines],
  [m4_if(
    [$1],
    [],
    [],
    [[
  ]m4_bpatsubst([[$1]], ['], ['\\''])[ \]dnl
GATBPS_CONFIG_LATER_make_lines(m4_shift($@))])])[dnl
[

case "$][{GATBPS_CONFIG_LATER_SCRIPT_MID+is_set}" in
  ?*)
  ;;
  *)
    ]GATBPS_CONFIG_LATER_VAR([bindir])[
  ;;
esac

GATBPS_CONFIG_LATER_RULES="$][{GATBPS_CONFIG_LATER_RULES}"'

]GATBPS_CONFIG_LATER_rule_lines(m4_if(,,rule_prerequisites))[]dnl
m4_if(
  leaf_prerequisites,
  [],
  [],
  [[
	$][(AM@&t@_V_at)$][(GATBPS_RECIPE_MARKER_TOP)
	$][(AM@&t@_V_at)$][(MAKE) \
  $][(AM@&t@_MAKEFLAGS) \]dnl
GATBPS_CONFIG_LATER_make_lines(m4_if(,,child_prerequisites))[
;]])[
	$][(GATBPS_V_CONFIG_LATER)$][(GATBPS_V_NOP)
	$][(AM@&t@_V_at){ \
  for x in \
    $][(MKDIR_P) \
  ; do \
    exit '\''0'\''; \
  done; \
  '\''echo'\'' \
    '\''error:'\'' \
    '\''$][$][(MKDIR_P)'\'' \
    '\''is'\'' \
    '\''not set'\'' \
    1>&2 \
  ; \
  exit '\''1'\''; \
:;}
	$][(AM@&t@_V_at){ \
  x='\'''\''; \
  for y in $][(srcdir); do \
    x="$][$][{x}"'\''x'\''; \
    case "$][$][{x}" in \
      ??*) \
        '\''echo'\'' \
          '\''error:'\'' \
          '\''$][$][(srcdir)'\'' \
          '\''contains multiple words'\'' \
          1>&2 \
        ; \
        exit '\''1'\''; \
      ;; \
    esac; \
  done; \
  case "$][$][{x}" in \
    ?*) \
      exit '\''0'\''; \
    ;; \
  esac; \
  '\''echo'\'' \
    '\''error:'\'' \
    '\''$][$][(srcdir)'\'' \
    '\''is not set'\'' \
    1>&2 \
  ; \
  exit '\''1'\''; \
:;}
	$][(AM@&t@_V_at)rm \
  -f \
  ./]output_file[ \
  ./]output_file['\''.tmp'\'' \
;
	$][(AM@&t@_V_at)$][(MKDIR_P) \
  ./$][(@D) \
;
	$][(AM@&t@_V_at){ \
  ( \
    x=]input_file[; \
    $][(GATBPS_VPATH_SEARCH_TOP) \
      "$][$][{x}" \
    $][(GATBPS_VPATH_SEARCH_BOT); \
    d=$][(GATBPS_VPATH_SEARCH_RESULT); \
    x="$][$][{d}"'/'"$][$][{x}"; \
    readonly '\''x'\''; \
    cp $][$][x $][@.tmp; \
    $][(AWK) \
      $][(GATBPS_CONFIG_LATER_SCRIPT) \
      0<"$][$][{x}" \
      1>./]output_file['\''.tmp'\'' \
    || exit $][$][?; \
    mv \
      -f \
      ./]output_file['\''.tmp'\'' \
      ./]output_file[ \
    || exit $][$][?; \
    exit '\''0'\''; \
  :;); \
  exit_status=$][$][?; \
  readonly '\''exit_status'\''; \
  case "$][$][{exit_status}" in \
    '\''0'\'') \
    ;; \
    *) \
      rm \
        -f \
        ./]output_file[ \
        ./]output_file['\''.tmp'\'' \
      ; \
    ;; \
  esac; \
  exit "$][$][{exit_status}"; \
:;}
	$][(AM@&t@_V_at)$][(GATBPS_RECIPE_MARKER_BOT)

.PHONY: clean-]output_file[

clean-]output_file[:
	-rm \
  -f \
  ./]output_file[ \
  ./]output_file['\''.tmp'\'' \
;

]clean_target[-local: clean-]output_file[

'

]dnl
m4_popdef([rule_prerequisites])[]dnl
m4_popdef([leaf_prerequisites])[]dnl
m4_popdef([clean_target])[]dnl
m4_popdef([child_prerequisites])[]dnl
m4_popdef([input_file])[]dnl
m4_popdef([output_file])[]dnl
m4_popdef([list_4])[]dnl
[:;}]])[]dnl
dnl
dnl The authors of this file have waived all copyright and
dnl related or neighboring rights to the extent permitted by
dnl law as described by the CC0 1.0 Universal Public Domain
dnl Dedication. You should have received a copy of the full
dnl dedication along with this file, typically as a file
dnl named <CC0-1.0.txt>. If not, it may be available at
dnl <https://creativecommons.org/publicdomain/zero/1.0/>.
dnl
