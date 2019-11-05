E    := PSL.main

.PHONY: dev
dev: .stack-work
	ghcid --warnings --test $E

.stack-work:
	stack setup

.PHONY: run
eval:
	stack ghci --ghci-options -e --ghci-options $E

.PHONY: build
build:
	stack build

.PHONY: run
run:
	# stack run
	stack ghci --ghci-options -e --ghci-options $E

.PHONY: profile
profile:
	stack run --profile -- +RTS -p

.PHONY: trace
trace:
	stack run --profile -- +RTS -xc

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
