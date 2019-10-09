# BUILD INSTRUCTIONS

- Install stack
- Install ghcid (via `stack install ghcid`)
- `make run` to run (using `stack ghci`)
- `make dev` for interactive typechecking/running (using `ghcid`)
- `make build` just to build (using `stack build`)

# UNICODE INSTRUCTIONS

- See https://github.com/davdar/dotfiles/tree/master/unicode
- Good support for vim and emacs
- Ghetto support for Atom
- I recommend installing and using MenloX*.ttf — this is a mashup of Menlo and STIX Two Math 

# SYNTAX HIGHLIGHTING (VIM ONLY)

- If you put `vim/X/pantheon.vim` in your `~/.vim/X/` then you will get
  somewhat decent syntax highlighting for *.psl files.

# SYNTAX HIGHLIGHTING (EMACS ONLY)

- Load `emacs/psl-mode.el` and switch to `psl-mode` when editing *.psl files

# WRITEUP

- There is a draft formalism in `writeup/` ; just use `make` to build
- The main source file for the writeup is `writeup/tex/main.tex`
- You can see fully expanded latex (after building) in `writeup/out/main.tex`
