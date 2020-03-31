dnl
dnl For the copyright information for this file, please search up the
dnl directory tree for the first README file.
dnl

AC_DEFUN([DEFINE_ALL], [[{

#
# The block that contains this comment is the expansion of the
# DEFINE_ALL macro.
#

]m4_ifdef(
  [DEFINE_ALL_HAS_BEEN_CALLED],
  [gatbps_fatal([
    DEFINE_ALL has already been called
  ])],
  [m4_define([DEFINE_ALL_HAS_BEEN_CALLED])])[

]m4_if(
  m4_eval([$# != 0]),
  [1],
  [gatbps_fatal([
    DEFINE_ALL requires exactly 0 arguments
    ($# ]m4_if([$#], [1], [[was]], [[were]])[ given)
  ])])[

]AC_REQUIRE([DEFINE_ALL_WGET_URLS])[

]dnl begin_prerequisites
[

]AC_REQUIRE([DEFINE_AR])[
]AC_REQUIRE([DEFINE_AWK])[
]AC_REQUIRE([DEFINE_CC])[
]AC_REQUIRE([DEFINE_CXX])[
]AC_REQUIRE([DEFINE_DOCKER])[
]AC_REQUIRE([DEFINE_GIT])[
]AC_REQUIRE([DEFINE_GREP])[
]AC_REQUIRE([DEFINE_LN_S])[
]AC_REQUIRE([DEFINE_MAKEINFO])[
]AC_REQUIRE([DEFINE_MKDIR_P])[
]AC_REQUIRE([DEFINE_OPENSSL])[
]AC_REQUIRE([DEFINE_RANLIB])[
]AC_REQUIRE([DEFINE_SED])[
]AC_REQUIRE([DEFINE_TAR])[
]AC_REQUIRE([DEFINE_WGET])[

]dnl end_prerequisites
[

:;}]])
