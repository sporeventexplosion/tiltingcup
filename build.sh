#!/usr/bin/env bash

set -ex

clang++ -std=c++23 -g -Og -Wall -Wextra -Wimplicit-fallthrough -Wuninitialized -pedantic -o tcup tcup.cc -lsodium
