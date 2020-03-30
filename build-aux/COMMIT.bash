#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

set -e; . src/bash/preludes/standard.bash

r='^[0-9a-f]{40}$'
readonly r

if [[ -r COMMIT ]]; then

  c=$(cat COMMIT)
  readonly c

  if [[ ! "$c" =~ $r ]]; then
    printf 'bad COMMIT file content: %s\n' "$c" >&2
    exit 1
  fi

else

  c=$(git rev-parse HEAD)
  readonly c

  if [[ ! "$c" =~ $r ]]; then
    printf 'bad computed commit hash: %s\n' "$c" >&2
    exit 1
  fi

fi

printf '%s\n' "$c"
