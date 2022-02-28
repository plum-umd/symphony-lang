.PHONY: all
all: out/include/backend-emp.h out/lib/libbackend-emp.dylib

out/include/backend-emp.h: src/backend-emp.h
	mkdir -p out/include
	cp src/backend-emp.h out/include/backend-emp.h

out/lib/libbackend-emp.dylib: emp src/backend-emp.o
	mkdir -p out/lib
	g++ -o $@ -shared -Lvendor/out/lib -L/usr/local/opt/openssl/lib -lemp-tool -lcrypto src/backend-emp.o

src/backend-emp.o: src/backend-emp.cpp
	g++ -o $@ -std=c++11 -maes -Ivendor/out/include -c $^

.PHONY: emp
emp:
	$(MAKE) -C vendor

.PHONY: clean
clean:
	$(MAKE) -C vendor clean
	rm -f src/backend-emp.o
	rm -rf out
