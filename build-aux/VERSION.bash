#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

set -e; . src/bash/preludes/standard.bash

if [[ -r VERSION ]]; then
  cat VERSION
  exit
fi

v=$(git describe --match='v*' --long --always)
readonly v

r='^v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.0-(0|[1-9][0-9]*)-g[0-9a-f]+$'
readonly r

if [[ ! "$v" =~ $r ]]; then
  printf 'bad git describe output: %s\n' "$v" >&2
  printf 'did you mess up your v* tag?\n' >&2
  exit 1
fi

printf '%s.%s.%s.%s\n' "${BASH_REMATCH[@]:1:4}"
