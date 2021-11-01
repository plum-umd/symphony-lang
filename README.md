# Build Instructions

- Install [Vagrant](https://www.vagrantup.com/)
- Create the development environment with `vagrant up`
- SSH into the development environment with `vagrant ssh`

The project directory `symphony-lang` will be mounted as a shared volume
in the virtual machine to `/vagrant`. Any changes you make locally will
be seen there. So, you can modify source code locally and build inside the
virtual machine.

To build inside the virtual machine:

- `make` (this will execute `stack build` using [Stack](https://docs.haskellstack.org/en/stable/README/), and symlink the executable to the project directory as `symphony`)

# Running Examples

- Build Symphony (see above)
- Choose an example from `examples/` (e.g. `examples/basic.sym`)
- Run in _sequential mode_ by executing `symphony example basic`
- Run in _distributed mode_ by executing

```
symphony example -P A basic &
symphony example -P B basic
```

where `A`, `B`, etc. are the parties declared in the example.

# Unicode Instructions

- See https://github.com/davdar/dotfiles/tree/master/unicode
- Good support for vim and emacs
- Minimal support for Atom
- I recommend installing and using XDejaVuSansMono-*.ttf
