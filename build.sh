#!/bin/sh

# Generate a new makefile for all .v files in the library.
coq_makefile -R "." CoqMTL -o makefile Base.v Control.v $(find Control Misc Parser Theory -name "*v")

# Build the library.
make

# Delete the makefile and related files.
rm makefile makefile.conf
