PSL includes a GNU Autotools based build system that provides a
conventional POSIX-like workflow for building and installation.
There are three main steps to using the build system:

1. Initializing the build system.
2. Configuring the build system.
3. Running the build system.

You should skip the first step if you're working with a distribution
archive, which you would have acquired by downloading an archive file
whose name looks like `psl-A.B.C.D.tar.gz`.
Otherwise, you should be working with the Git repository, which you
would have acquired by running a command like `git clone`.
In this case, you should do the first step.

**IMPORTANT:**
If you downloaded an archive file using a download button on a Git
repository manager like GitLab or GitHub, then it's probably not the
right thing.
These download buttons typically yield source archives, which are only
lightweight snapshots of the Git repository.
You cannot build and install PSL from a source archive.
Please download a distribution archive or clone the Git repository
instead.

Distribution archives are typically used by people who are only
interested in building and installing PSL to use it to develop PSL
programs.
The Git repository is typically used by people who are interested in
doing development work on PSL itself (e.g., the PANTHEON team).

## Initializing the build system

**IMPORTANT:**
You should only do this step if you're working with the Git repository.
You should skip this step if you're working with a distribution archive.

Initializing the build system requires the following tools to already be
installed on your system:

- Bash 4.4 or newer.
- jq 1.5 or newer.
- Git 1.8 or newer.
- GNU Autoconf 2.69 or newer.
- GNU Automake 1.12.6 or newer.
- GNU M4 1.4.16 or newer.

Note that this list of tools is much more developer oriented than the
list of tools required when working with a distribution archive,
reflecting the fact that working with the Git repository is mainly
intended for doing development work on PSL itself.

As an example, here is how you might install these tools on an Ubuntu
system:

```
sudo apt-get -q -y install bash jq git autoconf automake m4
```

After these tools are installed, simply run `./autogen` to initialize
the build system.

## Configuring the build system

Configuring the build system requires the following tools to already be
installed on your system:

- Any C compiler.
- Any Make implementation.

As an example, here is how you might install these tools on an Ubuntu
system:

```
sudo apt-get -q -y install gcc make
```

The following tools can be optionally installed on your system:

- The Haskell Tool Stack 2.1.3 or newer.
  See <https://docs.haskellstack.org/en/stable/install_and_upgrade/> for
  installation instructions.
- Docker 19.03.7 or newer.
  See <https://docs.docker.com/install/> for installation instructions.

Although both of the above tools are optional, you'll certainly want to
install at least one of them, otherwise you won't be able to build and
install anything of interest.
Installing The Haskell Tool Stack is necessary if you want to build and
install the PSL interpreter directly on your system.
Installing Docker is necessary if you want to build and install the PSL
Docker image, which lets you run the PSL interpreter inside a Docker
container.
Note that installing The Haskell Tool Stack is not necessary if you only
want to build and install the PSL Docker image.

After these tools are installed, simply run `./configure` to configure
the build system.

## Running the build system

To build and install the PSL interpreter directly to your system, first
run `make`, then run `make install` with root privilege, which usually
means running `sudo make install`.
After doing this, you can run `psl` to run the PSL interpreter.

To build and install the PSL Docker image, run `make docker`.
After doing this, a Docker image named `psl` will be available.
It will be tagged with both the `latest` tag and the PSL version number.
Inside a Docker container, you can run `psl` to run the PSL interpreter.
