#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

#
# autogen_print_am_header
#

if [[ "$(type -t \
autogen_print_am_header)" != function ]]; then
autogen_print_am_header() {

  if (($# != 0)); then
    barf 'invalid argument count: %d' $#
  fi

  cat <<"EOF"
##
## For the copyright information for this file, please search up the
## directory tree for the first README file.
##

##
## This file was generated by autogen.
##

EOF

}; readonly -f autogen_print_am_header; fi
