#
# For the copyright information for this file, please search up the
# directory tree for the first README file.
#

if [[ "$(type -t \
ubuntu_install_packages)" != function ]]; then
ubuntu_install_packages() {

  if ! command -v sudo &>/dev/null; then
    printf 'apt-get -qy update && apt-get -qy install sudo\n'
    su -c 'apt-get -qy update && apt-get -qy install sudo'
  fi

  printf 'sudo apt-get -qy update\n'
  sudo apt-get -qy update

  printf 'sudo apt-get -qy install %s\n' "$*"
  sudo apt-get -qy install "$@"

}; readonly -f ubuntu_install_packages; fi
