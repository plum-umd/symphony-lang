#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

#
# array_contains <name> <value>
#
# Determine whether the array <name> contains <value>. If it does, the
# return status is 0. Otherwise, the return status is 1.
#

if [[ "$(type -t \
array_contains)" != function ]]; then
array_contains() {

  #
  # Before Bash 4.4, "${x[@]}" causes an error when x is an empty array
  # and set -u is enabled. The workaround is to write ${x[@]+"${x[@]}"}
  # instead. See <https://stackoverflow.com/q/7577052>.
  #

  eval '
    local x'$1'
    for x'$1' in ${'$1'[@]+"${'$1'[@]}"}; do
      if [[ "$2" == "$x'$1'" ]]; then
        return 0
      fi
    done
    return 1
  '

}; readonly -f array_contains; fi
