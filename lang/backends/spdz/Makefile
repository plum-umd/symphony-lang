.PHONY: all
all: out/include/backend-spdz.h out/lib/libbackend-spdz.dylib

out/include/backend-spdz.h: src/backend-spdz.h
	mkdir -p out/include
	cp src/backend-spdz.h out/include/backend-spdz.h

out/lib/libbackend-spdz.dylib: mpspdz src/backend-spdz.o
	mkdir -p out/lib
	g++ -o $@ -shared -Lvendor/out/lib -lmpspdz src/backend-spdz.o

src/backend-spdz.o: src/backend-spdz.cpp
	g++ -o $@ -std=c++11 -Ivendor/out/include -c $^

.PHONY: mpspdz
mpspdz:
	$(MAKE) -C vendor

.PHONY: clean
clean:
	$(MAKE) -C vendor clean
	rm -f src/backend-spdz.o
	rm -rf out
