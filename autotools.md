PSL includes an Autotools-based build system that provides a
conventional POSIX-like workflow for building and installing PSL.

Working with this build system differs slightly depending on whether
you're working with the PSL Git repository or with a PSL distribution
archive.
The former you would have acquired by running `git clone`, and the
latter you would have acquired by downloading an archive whose name
looks like `psl-<VERSION>.tar.gz`.

The difference is that when working with the Git repository, you must
manually initialize the build system, whereas with the distribution
archive, the build system comes pre-initialized.
The former is typically used by people who are interested in doing
development work on PSL itself (e.g., the PANTHEON team), whereas the
latter is typically used by people who are only interested in building
and installing PSL and using it to develop PSL programs.

Since the build system works the same way once it's initialized, we'll
first discuss how to initialize it when working with the Git repository.

## Initializing the build system

**IMPORTANT:** If you are working with a distribution archive instead of
the Git repository, you should skip this section.

Initializing the build system requires the following tools to be
installed on your system.
This list of tools is much more developer oriented than the list of
tools required after the build system is initialized:

- Bash 4.4 or newer.
- jq 1.5 or newer.
- Git 1.8 or newer.
- GNU Autoconf 2.69 or newer.
- GNU Automake 1.12.6 or newer.
- GNU M4 1.4.16 or newer.

To initialize the build system, simply run the following command:

```
./autogen
```

Be sure to verify that the last line it prints is `success`.

## Configuring the build system

## Running the build system
