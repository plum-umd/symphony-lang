.PHONY: all

all: emp-sh2pc

.PHONY: emp-sh2pc
emp-sh2pc: emp-ot symphony-emp-sh2pc/build/Makefile
	$(MAKE) -C symphony-emp-sh2pc/build install

symphony-emp-sh2pc/build/Makefile:
	mkdir -p symphony-emp-sh2pc/build
	cmake -S symphony-emp-sh2pc -B symphony-emp-sh2pc/build -DCMAKE_PREFIX_PATH=.. --install-prefix=$(CURDIR)

.PHONY: emp-ot
emp-ot: emp-tool symphony-emp-ot/build/Makefile
	$(MAKE) -C symphony-emp-ot/build install

symphony-emp-ot/build/Makefile:
	mkdir -p symphony-emp-ot/build
	cmake -S symphony-emp-ot -B symphony-emp-ot/build -DCMAKE_PREFIX_PATH=.. --install-prefix=$(CURDIR)

.PHONY: emp-tool
emp-tool: symphony-emp-tool/build/Makefile
	$(MAKE) -C symphony-emp-tool/build install

symphony-emp-tool/build/Makefile:
	mkdir -p symphony-emp-tool/build
	cmake -S symphony-emp-tool -B symphony-emp-tool/build --install-prefix=$(CURDIR)

.PHONY: clean
clean:
	rm -rf symphony-emp-tool/build
	rm -rf symphony-emp-ot/build
	rm -rf symphony-emp-sh2pc/build
	rm -rf cmake
	rm -rf include
	rm -rf lib
