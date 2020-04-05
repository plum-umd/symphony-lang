E          := PSL.mainDefault
STACK_ARGS := --trace --ghci-options '-fexternal-interpreter -prof'
STACK_ARGS := 

ARGS       :=

FLAGS      := 

psl: build
	rm -f psl
	ln -s `stack path --dist-dir`/build/psl/psl ./

all-examples: psl
	./psl example $(FLAGS) euclid
	./psl example $(FLAGS) msort
	./psl example $(FLAGS) qsort-pure
	# ./psl example db-stats
	./psl example $(FLAGS) atq
	./psl example $(FLAGS) karmarkar

.stack-work:
	stack setup

.PHONY: build
build: .stack-work
	stack build

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

.PHONY: doc
doc: .stack-work
	stack haddock
	cp -r `stack path --local-doc-root` ./

.PHONY: clean
clean:
	stack clean --full
	rm -f $(NAME).cabal
	rm -rf doc

.PHONY:
re:
	touch src/PSL.hs

.PHONY: hoogle
hoogle:
	stack hoogle -- generate --local
	(sleep 1 && open http://localhost:8080/?scope=package%3A$(NAME)) &
	stack hoogle -- server --local --port=8080
