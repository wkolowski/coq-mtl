#!/bin/sh

# Generate a new makefile for all .v files in the library.
coq_makefile -R "." HSLib -o makefile $(find . -name "*v")

# Build the library.
make

# Delete the makefile and related files.
rm makefile makefile.conf
