# Instructions

- Just run `make` to build.
- If try to `make` again, it will only rebuild if there are changed files.
- If you want to build multiple times (e.g., to build all references and
  bibliography from scratch of after a `make clean`), you can run `make twice`
  or `make thrice`.
- There is a sed-script processing phase. Files in `tex/` are fed into sed
  scripts and the raw latex that comes out is visible in `out/` after building.
