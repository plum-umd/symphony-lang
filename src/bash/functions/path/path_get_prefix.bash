#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

#
# path_get_prefix x
#
# Where x is the name of a variable, update x to be all text up to and
# including the last slash. If there is no slash, update x to be empty.
#

if [[ "$(type -t \
path_get_prefix)" != function ]]; then
path_get_prefix() {

  [[ "$1" == x ]] || local -n x="$1"
  x=/$x
  x=${x%/*}/
  x=${x#/}

}; readonly -f path_get_prefix; fi
