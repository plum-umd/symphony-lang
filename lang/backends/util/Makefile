# Artifacts
LIB_NAME    = symphony-util
SHARED_LIB := lib$(LIB_NAME).dylib
LIBS        = $(SHARED_LIB)

# Dependencies
DEPS_DIRS :=
DEPS       =

# Input / Output
SOURCE_DIR = src
BUILD_DIR  = build

INCLUDE_DIR = include
LIB_DIR     = lib

# Compiler Options
CXX       = g++
CXXFLAGS := -std=c++11 $(addprefix -I, $(addsuffix /include, . $(DEPS_DIRS)))
LDFLAGS  := $(addprefix -L, $(addsuffix /lib, $(DEP_DIRS)))
LDLIBS   := $(addpreifx -l, $(DEPS))

SOURCES = $(shell find $(SOURCE_DIR) -name '*.cpp')
OBJECTS = $(patsubst $(SOURCE_DIR)/%.cpp, $(BUILD_DIR)/%.o, $(SOURCES))

# Build
.PHONY: all
all: $(addprefix $(LIB_DIR)/, $(LIBS))

$(LIB_DIR)/$(SHARED_LIB): $(OBJECTS) $(LIB_DIR)
	$(CXX) -o $(@F) -shared $(LDFLAGS) $(OBJECTS) $(LDLIBS)
	mv $(@F) $@

$(LIB_DIR):
	mkdir -p $@

$(BUILD_DIR)/%.o: $(SOURCE_DIR)/%.cpp $(BUILD_DIR)
	$(CXX) -o $@ -c $(CXXFLAGS) $<

$(BUILD_DIR):
	mkdir -p $@

.PHONY: clean
clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(LIB_DIR)
