# Build Instructions

- Install stack
- Install ghcid (via `stack install ghcid`)
- `make run` to run (using `stack ghci`)
- `make dev` for interactive typechecking/running (using `ghcid`)
- `make build` just to build (using `stack build`)

# Unicode Instructions

- See https://github.com/davdar/dotfiles/tree/master/unicode
- Good support for vim and emacs
- Ghetto support for Atom
- I recommend installing and using MenloX*.ttf — this is a mashup of Menlo and STIX Two Math 

# Syntax Highlighting (vim only)

- If you put `vim/X/pantheon.vim` in your `~/.vim/X/` then you will get
  somewhat decent syntax highlighting for *.psl files.

# Syntax Highlighting (emacs only)

- Load `emacs/psl-mode.el` and switch to `psl-mode` when editing *.psl files

# Writeup

- There is a draft formalism in `writeup/` ; just use `make` to build
- The main source file for the writeup is `writeup/tex/main.tex`
- You can see fully expanded latex (after building) in `writeup/out/main.tex`
