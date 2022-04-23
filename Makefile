E          := SymphonyMain.mainDefault
NAME       := symphony
STACK_ARGS := --trace --ghci-options '-fexternal-interpreter -prof'
STACK_ARGS :=

$(NAME): build
	rm -f $(NAME)
	ln -s `stack path --local-install-root`/bin/$(NAME) ./

all-examples: $(NAME)
	./$(NAME) example $(FLAGS) basic
	./$(NAME) example $(FLAGS) gcd

extern/uvmhs/stack.yaml:
	git submodule update --init --recursive $(@D)

.stack-work:
	stack setup

.PHONY: build
build: extern/uvmhs/stack.yaml .stack-work
	stack build
#        stack build --flag symphony:par --extra-lib-dirs=$(CURDIR)/extern/symphony-runtime/target/debug

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
