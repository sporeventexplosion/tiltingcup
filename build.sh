#!/usr/bin/env bash

set -ex

clang++ -std=c++23 -g -Og -Wall -Wextra -pedantic -o tcup tcup.cc
