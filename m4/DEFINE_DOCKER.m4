dnl
dnl For the copyright information for this file, please search up the
dnl directory tree for the first README file.
dnl

AC_DEFUN([DEFINE_DOCKER], [[{

#
# The block that contains this comment is the expansion of the
# DEFINE_DOCKER macro.
#]dnl
m4_ifdef(
  [DEFINE_DOCKER_HAS_BEEN_CALLED],
  [gatbps_fatal([
    DEFINE_DOCKER has already been called
  ])],
  [m4_define([DEFINE_DOCKER_HAS_BEEN_CALLED])])[]dnl
m4_if(
  m4_eval([$# != 0]),
  [1],
  [gatbps_fatal([
    DEFINE_DOCKER requires exactly 0 arguments
    ($# ]m4_if([$#], [1], [[was]], [[were]])[ given)
  ])])[]dnl
[

]AC_REQUIRE([GATBPS_PROG_DOCKER])[

:;}]])[]dnl
