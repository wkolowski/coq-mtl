#!/bin/sh

# Generate a picture of the hierarchy of classes and their implementations using GraphViz.
dot Hierarchy.dot -Tpdf -o Hierarchy.pdf

# Compile the thesis.
latexmk -pdf -f -quiet -interaction=nonstopmode
