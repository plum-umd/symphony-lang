#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

if [[ "$(type -t \
jq_expect)" != function ]]; then
jq_expect() {

  local x

  case $# in
    0 | 1)
      barf 'invalid argument count: %d' $#
    ;;
  esac

  x=$(jq "$1" "$2")
  readonly x

  case $x in
    "" | false)
      shift 2
      barf "$@"
    ;;
  esac

}; readonly -f jq_expect; fi
