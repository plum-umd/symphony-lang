dnl
dnl This file was generated by GATBPS 0.1.0-5418+g42bd53ab, which was
dnl released on 2020-02-14. Before changing it, make sure
dnl you're doing the right thing. Depending on how GATBPS
dnl is being used, your changes may be automatically lost.
dnl A short description of this file follows.
dnl
dnl Special file: GATBPS_CONFIG_LATER_VAR.m4
dnl
dnl For more information, see the GATBPS manual.
dnl
#serial 20200214
AC_DEFUN([GATBPS_CONFIG_LATER_ADD], [dnl
[GATBPS_CONFIG_LATER_SCRIPT_MID=]dnl
["$][{GATBPS_CONFIG_LATER_SCRIPT_MID}"]dnl
[''\'' ]dnl
[} else if (line_parts[i + 1] == "$1") { ]dnl
[line = line "$2"; ]dnl
[replaced_previous_line_part = 1; ]dnl
['\''']dnl
])[]dnl
AC_DEFUN([GATBPS_CONFIG_LATER_VAR], [[{

#
]m4_text_wrap(
  [
    The block that contains this comment is the expansion of the
    GATBPS_CONFIG_LATER_VAR macro for the $1 variable.
  ],
  [# ],
  [# ],
  [72])[
#]dnl
m4_if(
  m4_eval([$# < 1 || $# > 2]),
  [1],
  [gatbps_fatal([
    GATBPS_CONFIG_LATER_VAR requires 1 to 2 arguments
    ($# ]m4_if([$#], [1], [[was]], [[were]])[ given)
  ])])[]dnl
m4_pushdef(
  [variable_value],
  m4_if(
    m4_eval([$# >= 2]),
    [1],
    [[[$2]]],
    [[[$][($1)]]]))[]dnl
[

case "$][{GATBPS_CONFIG_LATER_SCRIPT_MID+is_set}" in
  ?*)
  ;;
  *)
    ]GATBPS_CONFIG_LATER_ADD([AT], [@])[
    ]GATBPS_CONFIG_LATER_ADD([abs_builddir], [$][(abs_builddir)])[
    ]GATBPS_CONFIG_LATER_ADD([abs_srcdir], [$][(abs_srcdir)])[
    ]GATBPS_CONFIG_LATER_ADD([bindir], [$][(bindir)])[
    ]GATBPS_CONFIG_LATER_ADD([builddir], [$][(builddir)])[
    ]GATBPS_CONFIG_LATER_ADD([datadir], [$][(datadir)])[
    ]GATBPS_CONFIG_LATER_ADD([datarootdir], [$][(datarootdir)])[
    ]GATBPS_CONFIG_LATER_ADD([docdir], [$][(docdir)])[
    ]GATBPS_CONFIG_LATER_ADD([dvidir], [$][(dvidir)])[
    ]GATBPS_CONFIG_LATER_ADD([htmldir], [$][(htmldir)])[
    ]GATBPS_CONFIG_LATER_ADD([includedir], [$][(includedir)])[
    ]GATBPS_CONFIG_LATER_ADD([infodir], [$][(infodir)])[
    ]GATBPS_CONFIG_LATER_ADD([javadir], [$][(javadir)])[
    ]GATBPS_CONFIG_LATER_ADD([libdir], [$][(libdir)])[
    ]GATBPS_CONFIG_LATER_ADD([libexecdir], [$][(libexecdir)])[
    ]GATBPS_CONFIG_LATER_ADD([localedir], [$][(localedir)])[
    ]GATBPS_CONFIG_LATER_ADD([localstatedir], [$][(localstatedir)])[
    ]GATBPS_CONFIG_LATER_ADD([mandir], [$][(mandir)])[
    ]GATBPS_CONFIG_LATER_ADD([oldincludedir], [$][(oldincludedir)])[
    ]GATBPS_CONFIG_LATER_ADD([pdfdir], [$][(pdfdir)])[
    ]GATBPS_CONFIG_LATER_ADD([pkgdatadir], [$][(pkgdatadir)])[
    ]GATBPS_CONFIG_LATER_ADD([pkgincludedir], [$][(pkgincludedir)])[
    ]GATBPS_CONFIG_LATER_ADD([pkglibdir], [$][(pkglibdir)])[
    ]GATBPS_CONFIG_LATER_ADD([pkglibexecdir], [$][(pkglibexecdir)])[
    ]GATBPS_CONFIG_LATER_ADD([pkgsysconfdir], [$][(pkgsysconfdir)])[
    ]GATBPS_CONFIG_LATER_ADD([psdir], [$][(psdir)])[
    ]GATBPS_CONFIG_LATER_ADD([sbindir], [$][(sbindir)])[
    ]GATBPS_CONFIG_LATER_ADD([sharedstatedir], [$][(sharedstatedir)])[
    ]GATBPS_CONFIG_LATER_ADD([srcdir], [$][(srcdir)])[
    ]GATBPS_CONFIG_LATER_ADD([sysconfdir], [$][(sysconfdir)])[
  ;;
esac

]GATBPS_CONFIG_LATER_ADD([$1], variable_value)[

]dnl
m4_popdef([variable_value])[]dnl
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
