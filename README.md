# HTML Docs

- https://plum-umd.github.io/psl/

# Build Instructions

- Install stack
- Install ghcid (via `stack install ghcid`)
- `make run` to run (using `stack ghci`)
- `make dev` for interactive typechecking/running (using `ghcid`)
- `make build` just to build (using `stack build`)

# Running Challenge Problem Solutions

- Build PSL (see above)
- To run a challenge problem solution in `examples/soln.psl`, run
  `psl example soln`

# Unicode Instructions

- See https://github.com/davdar/dotfiles/tree/master/unicode
- Good support for vim and emacs
- Minimal support for Atom
- I recommend installing and using XDejaVuSansMono-*.ttf

# Syntax Highlighting (vim only)

- If you put `vim/X/pantheon.vim` in your `~/.vim/X/` then you will get
  somewhat decent syntax highlighting for *.psl files.

# Syntax Highlighting (emacs only)

- Load `emacs/psl-mode.el` and switch to `psl-mode` when editing *.psl files

# Writeup

- There is a draft formalism in `writeup/` ; just use `make` to build
- The main source file for the writeup is `writeup/tex/main.tex`
- You can see fully expanded latex (after building) in `writeup/out/main.tex`
