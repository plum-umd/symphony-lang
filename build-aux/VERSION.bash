#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

set -e; . src/bash/preludes/standard.bash

r2='^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$'
readonly r2

if [[ -r VERSION ]]; then

  v2=$(cat VERSION)
  readonly v2

  if [[ ! "$v2" =~ $r2 ]]; then
    printf 'bad VERSION file content: %s\n' "$v2" >&2
    exit 1
  fi

else

  v1=$(git describe --match='v*' --long --always)
  readonly v1

  r1='^v(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.0-(0|[1-9][0-9]*)-g[0-9a-f]+$'
  readonly r1

  if [[ ! "$v1" =~ $r1 ]]; then
    printf 'bad git describe output: %s\n' "$v1" >&2
    exit 1
  fi

  v2=${BASH_REMATCH[1]}.${BASH_REMATCH[2]}.${BASH_REMATCH[3]}.${BASH_REMATCH[4]}
  readonly v2

  if [[ ! "$v2" =~ $r2 ]]; then
    printf 'bad computed version number: %s\n' "$v2" >&2
    exit 1
  fi

fi

printf '%s\n' "$v2"
