#!/usr/bin/env bash

set -ex

clang++ -std=c++23 -Og -Wall -Wextra -pedantic -o tcup tcup.cc
