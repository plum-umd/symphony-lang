# Artifacts
TARGETS = test

# Dependencies
OPENSSL_ROOT_DIR = /usr/local/opt/openssl
VENDOR_DIR       = ../vendor
UTIL_ROOT_DIR    = ../../util
SYM_EMP_ROOT_DIR = ..

DEPS_DIRS := $(OPENSSL_ROOT_DIR) $(VENDOR_DIR) $(UTIL_ROOT_DIR) $(SYM_EMP_ROOT_DIR)
DEPS       = crypto emp-tool symphony-util symphony-emp

# Input / Output
SOURCE_DIR = src
BUILD_DIR  = build
OUT_DIR    = out

# Compiler Options
CC       = gcc
CFLAGS  := -maes $(addprefix -I, $(addsuffix /include, . $(DEPS_DIRS)))
LDFLAGS := $(addprefix -L, $(addsuffix /lib, $(DEPS_DIRS)))
LDLIBS  := $(addprefix -l, $(DEPS))

SOURCES = $(shell find $(SOURCE_DIR) -name '*.c')
OBJECTS = $(patsubst $(SOURCE_DIR)/%.c, $(BUILD_DIR)/%.o, $(SOURCES))

# Build
.PHONY: all
all: $(addprefix $(SOURCE_DIR)/, $(TARGETS))
