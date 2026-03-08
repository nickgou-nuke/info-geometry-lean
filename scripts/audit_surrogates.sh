#!/bin/bash
# audit_surrogates.sh
# Audits the info-geometry-lean codebase for mathematical placeholders and surrogates.

echo "### Soundness Audit: Mathematical Surrogates & Placeholders ###"
echo "Searching in lean/InfoGeometry/..."
echo

KEYWORDS="surrogate|scaffold|placeholder|draft|legacy|trivialization|tautology"
FILES=$(grep -rEi "($KEYWORDS)" lean/InfoGeometry/ | cut -d: -f1 | sort | uniq)

for file in $FILES; do
  echo "--- File: $file ---"
  grep -Ei "($KEYWORDS)" "$file" | head -n 5
  echo
done

echo "### Theorem Dependency Check (Flagship) ###"
# Check if flagship theorems depend on these files
FLAGSHIPS="isRicciFlat_of_rnEntropySource sinkhorn_step_kmsClosure_of_control holographicEmergence_package"

for theorem in $FLAGSHIPS; do
  echo "Checking dependencies for $theorem..."
  # This is a simplified check; actual dependency analysis would require Lean's frontend.
  grep -r "$theorem" lean/InfoGeometry/Canonical/ | cut -d: -f1 | xargs grep -lE "import InfoGeometry.(Assumptions|Canonical.*Core)" 2>/dev/null
  echo
done
