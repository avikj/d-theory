#!/bin/bash

# This script checks all Agda files and logs their status.

LOG_FILE="verification_status.log"
rm -f "$LOG_FILE"

for f in $(find . -name "*.agda"); do
  echo "Checking $f"
  if agda "$f" > /dev/null 2>&1; then
    echo "PASS: $f" >> "$LOG_FILE"
  else
    echo "FAIL: $f" >> "$LOG_FILE"
  fi
done

echo "Verification check complete. Results logged to $LOG_FILE"
