#!/bin/bash
set -e

# Create a temporary directory
TMP_DIR=$(mktemp -d)
echo "Temporary directory created at $TMP_DIR"

# Copy the game file to the temporary directory
cp knowledge_weaver.html "$TMP_DIR/index.html"
echo "Copied knowledge_weaver.html to $TMP_DIR/index.html"

# Navigate to the temporary directory
cd "$TMP_DIR"

# Initialize a new git repository
git init
git checkout -b gh-pages

# Add and commit the file
git add index.html
git commit -m "Deploying Knowledge Weaver to GitHub Pages"

# Push to the gh-pages branch
git remote add origin https://github.com/avikj/d-theory.git
git push -f origin gh-pages

# Clean up the temporary directory
rm -rf "$TMP_DIR"

echo "Deployment complete."
