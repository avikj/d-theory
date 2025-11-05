#!/bin/bash

# This script removes generated files.

find . -name "*.agda.err" -delete
find . -name "*.agda.nosafe.err" -delete
find . -name "*.agdai" -delete
find . -name "*.pyc" -delete
find . -name "*.pyo" -delete
find . -name "*.aux" -delete
find . -name "*.log" -delete
find . -name "*.out" -delete
find . -name "*.toc" -delete
find . -name "*.fdb_latexmk" -delete
find . -name "*.fls" -delete
find . -name "*.synctex.gz" -delete
find . -name "*.bbl" -delete
find . -name "*.blg" -delete
rm -f verification_status.log
