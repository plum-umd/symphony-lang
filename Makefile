E          := SymphonyMain.mainDefault
NAME       := symphony
STACK_ARGS := --extra-include-dirs=/usr/local/include --extra-lib-dirs=/usr/local/lib --trace --ghci-options '-fexternal-interpreter -prof'
STACK_ARGS :=

ARGS       :=

FLAGS      :=

symphony: build
	rm -f symphony
	ln -s `stack path --dist-dir`/build/Symphony/symphony ./

all-examples: symphony
	./symphony example $(FLAGS) msort-dedup-small
	./symphony example $(FLAGS) qsort
	./symphony example $(FLAGS) gcd-gc
	./symphony example $(FLAGS) gcd-bgv
	./symphony example $(FLAGS) karmarkar
	./symphony example $(FLAGS) db-stats

.stack-work:
	stack setup

.PHONY: build
build: .stack-work
	stack build --extra-include-dirs=/usr/local/include --extra-lib-dirs=/usr/local/lib

build-profile: .stack-work
	stack build --profile

.PHONY: dev
dev: .stack-work
	ghcid --command="stack ghci $(STACK_ARGS)" --warnings --test $E

.PHONY: eval
eval: .stack-work
	stack ghci $(STACK_ARGS) --ghci-options '-e $E'

.PHONY: run
run: .stack-work
	stack run -- $(ARGS)

.PHONY: trace
trace: .stack-work
	stack run --trace -- $(ARGS)

.PHONY: profile
profile: .stack-work
	stack run --profile -- $(ARGS) +RTS -p

.PHONY: ghci
ghci: .stack-work
	stack ghci

.PHONY: docs
docs: .stack-work
	stack haddock
	rm -rf ./docs
	cp -r `stack path --local-doc-root` ./docs

.PHONY: clean
clean:
	stack clean --full
	rm -f $(NAME).cabal
	rm -rf docs

.PHONY:
re:
	touch src/Symphony.hs

.PHONY: hoogle
hoogle:
	stack hoogle -- generate --local
	(sleep 1 && open http://localhost:8080/?scope=package%3A$(NAME)) &
	stack hoogle -- server --local --port=8080
