E    := PSL.main

.PHONY: dev
dev: .stack-work
	# ghcid --warnings --test $E
	ghcid --command="stack ghci --trace --ghci-options '-fexternal-interpreter -prof'" --warnings --test $E

# ghcid --command="stack ghci --ghci-options -fobject-code" --warnings --test $E

.stack-work:
	stack setup

.PHONY: eval
eval:
	stack ghci --trace --ghci-options '-fexternal-interpreter -prof -e $E'

.PHONY: build
build:
	stack build

.PHONY: run
run:
	# stack run
	# stack ghci --ghci-options -e --ghci-options $E
	stack run

.PHONY: profile
profile:
	stack run --profile -- +RTS -p

.PHONY: trace
trace:
	stack run --trace

.PHONY: ghci
ghci:
	stack ghci

.PHONY: doc
doc:
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
