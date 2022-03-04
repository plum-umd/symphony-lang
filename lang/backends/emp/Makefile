# Artifacts
LIB_NAME    = symphony-emp
SHARED_LIB := lib$(LIB_NAME).dylib
LIBS        = $(SHARED_LIB)

# Dependencies
OPENSSL_ROOT_DIR = /usr/local/opt/openssl
VENDOR_DIR       = vendor
UTIL_ROOT_DIR    = ../util

DEPS_DIRS := $(OPENSSL_ROOT_DIR) $(VENDOR_DIR) $(UTIL_ROOT_DIR)
DEPS       = crypto emp-tool symphony-util

# Input / Output
SOURCE_DIR = src
BUILD_DIR  = build
LIB_DIR    = lib

# Compiler Options
CXX       = g++
CXXFLAGS := -std=c++11 -maes $(addprefix -I, $(addsuffix /include, . $(DEPS_DIRS)))
LDFLAGS  := $(addprefix -L, $(addsuffix /lib, $(DEPS_DIRS)))
LDLIBS   := $(addprefix -l, $(DEPS))

SOURCES = $(shell find $(SOURCE_DIR) -name '*.cpp')
OBJECTS = $(patsubst $(SOURCE_DIR)/%.cpp, $(BUILD_DIR)/%.o, $(SOURCES))

# Build
.PHONY: all
all: $(addprefix $(LIB_DIR)/, $(LIBS))

$(LIB_DIR)/$(SHARED_LIB): vendor util $(OBJECTS) $(LIB_DIR)
	$(CXX) -o $(@F) -shared $(LDFLAGS) $(OBJECTS) $(LDLIBS)
	mv $(@F) $@

$(LIB_DIR):
	mkdir -p $@

$(BUILD_DIR)/%.o: $(SOURCE_DIR)/%.cpp vendor util $(BUILD_DIR)
	$(CXX) -o $@ -c $(CXXFLAGS) $<

$(BUILD_DIR):
	mkdir -p $@

.PHONY: vendor
vendor:
	$(MAKE) -C $(VENDOR_DIR)

.PHONY: util
util:
	$(MAKE) -C $(UTIL_ROOT_DIR)

.PHONY: clean
clean:
	$(MAKE) -C $(VENDOR_DIR) clean
	$(MAKE) -C $(UTIL_ROOT_DIR) clean
	rm -rf $(BUILD_DIR)
	rm -rf $(LIB_DIR)
