#!/bin/bash

# This script verifies all Agda files in the project.

set -e # Exit immediately if a command exits with a non-zero status.

for f in $(find . -name "*.agda"); do
  echo "Verifying $f"
  agda "$f"
done

echo "All Agda files verified successfully."
