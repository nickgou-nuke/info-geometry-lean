#!/usr/bin/env bash
set -euo pipefail

echo "Deduplicating quality tools..."

# Remove duplicate vacuity-linter.py (keep tools/scripts/vacuity-linter.py)
if [ -f "scripts/vacuity-linter.py" ]; then
    echo "Removing duplicate scripts/vacuity-linter.py"
    rm scripts/vacuity-linter.py
fi

if [ -f "src/infogeometry/scripts/vacuity-linter.py" ]; then
    echo "Removing duplicate src/infogeometry/scripts/vacuity-linter.py"
    rm src/infogeometry/scripts/vacuity-linter.py
fi

if [ -f "src/infogeometry/tools/scripts/vacuity-linter.py" ]; then
    echo "Removing duplicate src/infogeometry/tools/scripts/vacuity-linter.py"
    rm src/infogeometry/tools/scripts/vacuity-linter.py
fi

if [ -f "external_refs/auto/scripts/vacuity-linter.py" ]; then
    echo "Removing duplicate external_refs/auto/scripts/vacuity-linter.py"
    rm external_refs/auto/scripts/vacuity-linter.py
fi

# Check for duplicate audit_theory.sh
if [ -f "scripts/quality/audit_theory.sh" ] && [ -f "src/infogeometry/scripts/quality/audit_theory.sh" ]; then
    echo "Checking audit_theory.sh duplicates..."
    # Keep the one in scripts/quality/
    rm src/infogeometry/scripts/quality/audit_theory.sh
fi

# Check for duplicate mathless_proof_audit.py
if [ -f "scripts/quality/mathless_proof_audit.py" ] && [ -f "src/infogeometry/scripts/quality/mathless_proof_audit.py" ]; then
    echo "Checking mathless_proof_audit.py duplicates..."
    rm src/infogeometry/scripts/quality/mathless_proof_audit.py
fi

# Check for duplicate semantic_vacuity_gate.py
if [ -f "tools/quality/semantic_vacuity_gate.py" ] && [ -f "src/infogeometry/tools/quality/semantic_vacuity_gate.py" ]; then
    echo "Checking semantic_vacuity_gate.py duplicates..."
    rm src/infogeometry/tools/quality/semantic_vacuity_gate.py
fi

echo "Deduplication complete. Remaining tools:"
find . -name "*.py" -path "*/quality/*" -o -name "*.py" -path "*/scripts/*" | grep -v ".lake" | grep -v ".venv" | grep -v "__pycache__" | sort

