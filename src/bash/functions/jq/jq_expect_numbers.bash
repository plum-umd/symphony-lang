#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

if [[ "$(type -t \
jq_expect_numbers)" != function ]]; then
jq_expect_numbers() {

  case $# in
    2)
    ;;
    *)
      barf 'invalid argument count: %d' $#
    ;;
  esac

  jq_expect_types "$1" "$2" number

}; readonly -f jq_expect_numbers; fi