#!/bin/sh

SYMPHONY_ROOT=/Users/ian/Projects/symphony/symphony-lang

export DYLD_LIBRARY_PATH=$SYMPHONY_ROOT/lang/backends/emp/vendor/lib
export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:$SYMPHONY_ROOT/lang/backends/emp/lib
export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:$SYMPHONY_ROOT/lang/backends/util/lib
