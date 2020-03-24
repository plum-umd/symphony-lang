dnl
dnl This file was generated by GATBPS 0.1.0-5418+g42bd53ab, which was
dnl released on 2020-02-14. Before changing it, make sure
dnl you're doing the right thing. Depending on how GATBPS
dnl is being used, your changes may be automatically lost.
dnl A short description of this file follows.
dnl
dnl Special file: GATBPS_DEFINE_LIB_LDFLAGS.m4
dnl
dnl For more information, see the GATBPS manual.
dnl
#serial 20200214
AC_DEFUN([GATBPS_DEFINE_LIB_LDFLAGS], [[{

#
# The block that contains this comment is the expansion of the
# GATBPS_DEFINE_LIB_LDFLAGS macro.
#]dnl
m4_ifdef(
  [GATBPS_DEFINE_LIB_LDFLAGS_HAS_BEEN_CALLED],
  [gatbps_fatal([
    GATBPS_DEFINE_LIB_LDFLAGS has already been called
  ])],
  [m4_define([GATBPS_DEFINE_LIB_LDFLAGS_HAS_BEEN_CALLED])])[]dnl
m4_if(
  m4_eval([$# != 0]),
  [1],
  [gatbps_fatal([
    GATBPS_DEFINE_LIB_LDFLAGS requires exactly 0 arguments
    ($# ]m4_if([$#], [1], [[was]], [[were]])[ given)
  ])])[]dnl
[

]AC_ARG_VAR(
  [LIB_LDFLAGS],
  [
    extra flags to use with the linker when building libraries
  ])[

:;}]])[]dnl
dnl
dnl The authors of this file have waived all copyright and
dnl related or neighboring rights to the extent permitted by
dnl law as described by the CC0 1.0 Universal Public Domain
dnl Dedication. You should have received a copy of the full
dnl dedication along with this file, typically as a file
dnl named <CC0-1.0.txt>. If not, it may be available at
dnl <https://creativecommons.org/publicdomain/zero/1.0/>.
dnl
