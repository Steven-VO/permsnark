# Copyright (C) 2026 Steven Van Overberghe, Ghent University
# SPDX-License-Identifier: GPL-3.0-or-later
#
# permsnark is compiled for one cycle length n at a time:
#   make permsnark_17      -> ./permsnark_17 (n = 17, order 34)
#   make N=17              -> the same
# The two filters take n at runtime:
#   make permcanon perm2g6
# Options:
#   make ... PORTABLE=1    -> without -march=native (binary runs on other CPUs)
CXX      ?= g++
CXXFLAGS ?= -std=c++20 -O3 -DNDEBUG -Wall -Wextra -Wno-unused-parameter -fno-exceptions
ifndef PORTABLE
CXXFLAGS += -march=native
endif
LDFLAGS  ?= -pthread

# range of n compiled into permcanon
CNMIN ?= 3
CNMAX ?= 32

ifdef N
all: permsnark_$(N)
else
all: permcanon perm2g6
endif

# without a number: say how to do it (make's built-in rule would quietly
# compile every n from 3 to 16, which takes several minutes)
permsnark:
	@echo "permsnark is built for one n at a time, e.g. make permsnark_17 (or make N=17)"; exit 1

permsnark_%: permsnark.cpp
	$(CXX) $(CXXFLAGS) -DNMIN=$* -DNMAX=$* -o $@ $< $(LDFLAGS)

permcanon: permcanon.cpp
	$(CXX) $(CXXFLAGS) -DNMIN=$(CNMIN) -DNMAX=$(CNMAX) -o $@ $< $(LDFLAGS)

perm2g6: perm2g6.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -f permsnark_* permcanon perm2g6

.PHONY: all clean permsnark
