BACKENDS = util emp

.PHONY: symphony
symphony: build
	rm -f symphony
	ln -s `stack path --dist-dir`/build/Symphony/symphony ./

.PHONY: build
build: .stack-work backends
	stack build

.PHONY: backends
backends: $(BACKENDS)

.PHONY: $(BACKENDS)
$(BACKENDS):
	$(MAKE) -C backends/$@
