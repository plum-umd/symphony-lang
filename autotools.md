PSL includes an Autotools-based build system that provides a
conventional POSIX-like workflow for building and installation.
There are three main steps to using the build system:

1. Initializing the build system.
2. Configuring the build system.
3. Running the build system.

You should skip the first step if you're working with a distribution
archive, which you would have acquired by downloading and extracting an
archive file whose name looks like `psl-<VERSION>.tar.gz`.
Otherwise, you're working with the Git repository, which you must have
acquired by running `git clone` (or equivalent).
In this case, you cannot skip the first step.

Distribution archives are typically used by people who are only
interested in building and installing PSL to use it to develop PSL
programs.
The Git repository is typically used by people who are interested in
doing development on PSL itself (e.g., the PANTHEON team).

## Initializing the build system

**IMPORTANT:**
You should skip this step if you're working with a distribution archive.

Initializing the build system requires the following tools to be
installed on your system:

- Bash 4.4 or newer.
- jq 1.5 or newer.
- Git 1.8 or newer.
- GNU Autoconf 2.69 or newer.
- GNU Automake 1.12.6 or newer.
- GNU M4 1.4.16 or newer.

Note that this list of tools is much more developer oriented than the
list of tools required by the next step.

To initialize the build system, run the following command:

```
./autogen
```

Be sure to verify that the last line it prints is `success`.

## Configuring the build system

Configuring the build system requires the following tools to be
installed on your system:

- Any C compiler.
- Any `make` implementation.
- The Haskell Tool Stack 2.1.3 or newer.

The following tools are optional:

- Docker 19.03.7 or newer.
  This is necessary if you want to build the PSL Docker image.

To configure the build system, run the following command:

```
./configure
```

There are also many options that can be given to `./configure`, which
can be listed by running `./configure --help`.
Some of these options will be familiar to you if you're familiar with
building and installing other POSIX-like software from source.

The most notable of the options are as follows:

- `./configure STACK='foo'` can be used to specify how to run `stack`.

- `./configure DOCKER='foo'` can be used to specify how to run `docker`.
  For example, you might use `./configure DOCKER='sudo docker'`.

## Running the build system

To run the build system, run the following command:

```
make
```

After doing this, the `psli` interpreter will be available in the
current directory, and you can run it with `./psli`.

To install it to your system, run the following command, replacing
`sudo` with any equivalent if necessary:

```
sudo make install
```

After doing this, you can run `psli` from anywhere.

You can also build the `psl` Docker image by running `make docker`.
