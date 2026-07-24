# Lean 25-minute time-boxing alias
# Add to ~/.bashrc or source directly

# 25-minute hard stop (Pomodoro)
alias lean25="timeout 1500 lake build"

# 25-minute with sorry count
alias lean25s="timeout 1500 bash -c 'lake build 2>&1 | grep -c sorry'"

# Quick sorry count
alias sorrycount="lake build 2>&1 | grep -c 'sorry' || echo 0"

# Build with sorry gate (exits 1 if sorries > 0)
alias leansorry="lake build 2>&1 | grep -c 'sorry' | { read n; echo \"Sorries: $n\"; [ \$n -gt 0 ] && exit 1; }"

# Build with max sorry threshold
lean_max_sorry() {
    local max=${1:-0}
    SORRIES=$(lake build 2>&1 | grep -c "sorry" || echo 0)
    echo "Sorries: $SORRIES (max: $max)"
    if [ "$SORRIES" -gt "$max" ]; then
        return 1
    fi
    return 0
}

# Quick AAR log entry
aar() {
    local msg="${1:-No message}"
    echo "## AAR: $(date '+%Y-%m-%d %H:%M')" >> AAR.md
    echo "**Message:** $msg" >> AAR.md
    echo "" >> AAR.md
}

# Build with sorry gate (exits 1 if any sorries)
leang() {
    SORRIES=$(lake build 2>&1 | grep -c "sorry" || echo 0)
    echo "Sorries: $SORRIES"
    if [ "$SORRIES" -gt 0 ]; then
        return 1
    fi
}

# Quick build with time limit
build25() {
    timeout 1500 lake build
}

# AAR template
aar_template() {
    cat > AAR_TEMPLATE.md << 'EOF'
## AAR: [Theorem/Task Name] - $(date '+%Y-%m-%d')

**Planned:** What was the goal?

**Actual:** What actually happened?

**Why:** Why the difference?

**Sustain:** What worked? Keep doing.

**Improve:** What failed? Change for next time.
EOF
    echo "AAR template created: AAR_TEMPLATE.md"
}