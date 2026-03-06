#!/usr/bin/env bash
# Run from the project root

echo "Discovering InfoGeometry modules..."
MODULES=$(cd lean && find InfoGeometry -name "*.lean" \! -name ".*" | sort)

printf "%-60s %10s\n" "MODULE" "SECONDS"
printf "%-60s %10s\n" "------" "-------"

mkdir -p logs

for FILE in $MODULES; do
    TARGET=$(echo "$FILE" | sed -e 's|\.lean$||' -e 's|/|.|g')
    
    # We run lake build for this single target
    # Time output goes to a temporary file, build log goes to logs/
    /usr/bin/time -f "%e" lake build "$TARGET" > "logs/$TARGET.log" 2> "logs/${TARGET}_time.tmp"
    
    # Check if the build completely failed (i.e. error)
    if [ ${PIPESTATUS[0]} -ne 0 ]; then
        ELAPSED="FAILED"
    else
        ELAPSED=$(tail -n1 "logs/${TARGET}_time.tmp")
    fi
    
    printf "%-60s %10s\n" "$TARGET" "$ELAPSED"
done
echo "Logs saved in logs/"
