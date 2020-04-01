#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

if [[ "$(type -t \
jq_expect_nulls_or_null)" != function ]]; then
jq_expect_nulls_or_null() {

  case $# in
    2)
    ;;
    *)
      barf 'invalid argument count: %d' $#
    ;;
  esac

  jq_expect_types_or_null "$1" "$2" null

}; readonly -f jq_expect_nulls_or_null; fi
