#!/bin/bash
echo "Starting aggressive git-add daemon..."
while true; do
  git add -A > /dev/null 2>&1
  sleep 5
done
