#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

#
# Ensure that the standard prelude chooses `$tmpdir` to be inside the
# current directory. This ensures that we can use `$tmpdir` with the
# `--mount` and `--volume` options of nested `docker` commands.
#

TMPDIR=$PWD
readonly TMPDIR
export TMPDIR

#
#

set -e; . src/bash/preludes/standard.bash

#
# Turn on command tracing so we can see what's going on in the job log
# of the GitLab UI. This prepends a green colored "trace: " heading to
# each traced command, which is similar to how GitLab traces the direct
# job commands in green.
#

PS4='+ \[\e[0;32m\]\[\e[1m\]trace:\[\e[0m\] '
readonly PS4
set -x

#
# Ensure that `apt-get -y` is noninteractive. See `man 7 debconf` on
# Debian (after `apt-get install debconf-doc`) or view it online at
# <https://manpages.debian.org/debconf.7>.
#

DEBIAN_FRONTEND=noninteractive
readonly DEBIAN_FRONTEND
export DEBIAN_FRONTEND

#
# Determine whether we're running on an archivist runner.
#

if test -f /archivist.gitlab-username; then
  archivist=true
else
  archivist=false
fi
readonly archivist

case $archivist in
  true)
    u=$(cat /archivist.gitlab-username)
    docker login \
      --username "$u" \
      --password-stdin \
      registry.stealthsoftwareinc.com \
      </archivist.gitlab-password \
    ;
    unset u
  ;;
esac
