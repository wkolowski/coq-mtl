#!/bin/sh

# Generate pictures of the hierarchy of classes and their implementations using GraphViz.
# The .pdf one is used in the thesis whereas the .jpg one is used in the README.
dot Hierarchy.dot -Tpdf -o Hierarchy.pdf

# Compile the thesis.
latexmk -pdf -f -quiet -interaction=nonstopmode -shell-escape Thesis.tex

# Compile the slides for thesis defense.
cd Defense
latexmk -pdf -f -quiet -interaction=nonstopmode -shell-escape Slides.tex
