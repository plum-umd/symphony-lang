#!/bin/bash

DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
echo $DIR

$DIR/../extern/symphony-runtime/scripts/provision-focal64.sh
