.PHONY: all
all: mp-spdz

.PHONY: mp-spdz
mp-spdz:
	$(MAKE) -C symphony-spdz install-spdz SYMPHONY_OUT=$(shell pwd)/out

.PHONY: clean
clean:
	$(MAKE) -C symphony-spdz clean
	rm -rf out
