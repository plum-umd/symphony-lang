dnl
dnl For the copyright information for this file, please search up the
dnl directory tree for the first README file.
dnl

AC_DEFUN([DEFINE_MKDIR_P], [[{

#
# The block that contains this comment is the expansion of the
# DEFINE_MKDIR_P macro.
#]dnl
m4_ifdef(
  [DEFINE_MKDIR_P_HAS_BEEN_CALLED],
  [gatbps_fatal([
    DEFINE_MKDIR_P has already been called
  ])],
  [m4_define([DEFINE_MKDIR_P_HAS_BEEN_CALLED])])[]dnl
m4_if(
  m4_eval([$# != 0]),
  [1],
  [gatbps_fatal([
    DEFINE_MKDIR_P requires exactly 0 arguments
    ($# ]m4_if([$#], [1], [[was]], [[were]])[ given)
  ])])[]dnl
[

]AC_REQUIRE([GATBPS_PROG_MKDIR_P])[

:;}]])[]dnl
