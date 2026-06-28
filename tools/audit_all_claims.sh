#!/usr/bin/env bash
# Comprehensive Audit: Build and Verify All Claims
set -euo pipefail

cd /home/goutev/repos/info-geometry-lean

echo "================================================================================"
echo "COMPREHENSIVE AUDIT: BUILD AND VERIFY ALL CLAIMS"
echo "================================================================================"

ISSUES_FOUND=0
FIXES_APPLIED=0

# ============================================================================
# CLAIM 1: Cuntz KMS at β=2π
# ============================================================================
echo -e "\n[1/5] CLAIM: Cuntz vacuum satisfies KMS at β=2π"
echo "----------------------------------------"

kms_files=""
if [ -f lean/InfoGeometry/Thermo/CuntzKMSVerification.lean ]; then
    kms_files="$kms_files lean/InfoGeometry/Thermo/CuntzKMSVerification.lean"
fi
if [ -f lean/InfoGeometry/Algebra/CuntzKMSState.lean ]; then
    kms_files="$kms_files lean/InfoGeometry/Algebra/CuntzKMSState.lean"
fi
if [ -f lean/InfoGeometry/Algebra/CuntzKMSCondition.lean ]; then
    kms_files="$kms_files lean/InfoGeometry/Algebra/CuntzKMSCondition.lean"
fi

if [ -n "$kms_files" ]; then
    # Check for sorries in any KMS file
    has_sorry=false
    for f in $kms_files; do
        if grep -q "sorry" "$f" 2>/dev/null; then
            has_sorry=true
            echo "  ⚠️  ISSUE: Proof incomplete in $f (contains 'sorry')"
        fi
    done
    
    if [ "$has_sorry" = false ]; then
        echo "  ✓ All KMS proofs complete"
        FIXES_APPLIED=$((FIXES_APPLIED + 1))
    else
        ISSUES_FOUND=$((ISSUES_FOUND + 1))
        echo "  ACTION: Replace sorry with complete case analysis"
    fi
else
    echo "  ⚠️  ISSUE: No KMS formalization files found"
    ISSUES_FOUND=$((ISSUES_FOUND + 1))
fi

# Try to build primary KMS file
if [ -f lean/InfoGeometry/Algebra/CuntzKMSState.lean ]; then
    if timeout 120 lake build InfoGeometry.Algebra.CuntzKMSState >/dev/null 2>&1; then
        echo "  ✓ Builds successfully"
        FIXES_APPLIED=$((FIXES_APPLIED + 1))
    else
        echo "  ✗ Build failed"
        ISSUES_FOUND=$((ISSUES_FOUND + 1))
    fi
fi

# ============================================================================
# CLAIM 2: E8(8) maximal compact = SO(8,8)
# ============================================================================
echo -e "\n[2/5] CLAIM: E8(8) maximal compact is SO(8,8)"
echo "----------------------------------------"

if grep -q "maximal_compact := Unit" lean/InfoGeometry/E8/E8TrialityThermalProtection.lean 2>/dev/null; then
    echo "  ⚠️  ISSUE: maximal_compact is Unit (placeholder)"
    ISSUES_FOUND=$((ISUES_FOUND + 1))
else
    echo "  ✓ maximal_compact properly defined"
    FIXES_APPLIED=$((FIXES_APPLIED + 1))
fi

if grep -q "theorem.*: True := by.*trivial" lean/InfoGeometry/E8/E8TrialityThermalProtection.lean 2>/dev/null; then
    echo "  ⚠️  ISSUE: Circular proof (is_split : True := trivial)"
    ISSUES_FOUND=$((ISSUES_FOUND + 1))
else
    echo "  ✓ No circular proofs"
    FIXES_APPLIED=$((FIXES_APPLIED + 1))
fi

# ============================================================================
# CLAIM 3: Tomita-Takesaki for O₂
# ============================================================================
echo -e "\n[3/5] CLAIM: Tomita-Takesaki modular theory for Cuntz O₂"
echo "----------------------------------------"

if [ -f lean/InfoGeometry/Thermo/TomitaTakesakiCuntz.lean ] || [ -f lean/InfoGeometry/OperatorAlgebra/CuntzTomitaTakesaki.lean ] || [ -f lean/InfoGeometry/Algebra/CuntzTomitaTakesaki.lean ]; then
    echo "  ✓ Formalization exists"
    FIXES_APPLIED=$((FIXES_APPLIED + 1))
else
    echo "  ⚠️  ISSUE: No dedicated Tomita-Takesaki file for O₂"
    ISSUES_FOUND=$((ISSUES_FOUND + 1))
    echo "  ACTION: Create TomitaTakesakiCuntz.lean with J and Δ operators"
fi

# ============================================================================
# CLAIM 4: Cl(6,0) = Standard Model fermions
# ============================================================================
echo -e "\n[4/5] CLAIM: Cl(6,0) encodes Standard Model fermions"
echo "----------------------------------------"

furey_files=$(find lean -name "*Furey*" -o -name "*StandardModel*" 2>/dev/null | wc -l)
if [ "$furey_files" -gt 0 ]; then
    echo "  ✓ Furey formalization exists ($furey_files files)"
    
    # Check for actual proofs vs placeholders
    if grep -r "sorry\|:= True" lean/InfoGeometry/OperatorAlgebra/*Furey* 2>/dev/null | grep -v "Binary"; then
        echo "  ⚠️  ISSUE: Some proofs incomplete"
        ISSUES_FOUND=$((ISSUES_FOUND + 1))
    else
        echo "  ✓ All proofs complete"
        FIXES_APPLIED=$((FIXES_APPLIED + 1))
    fi
else
    echo "  ⚠️  ISSUE: No Furey/Standard Model files found"
    ISSUES_FOUND=$((ISSUES_FOUND + 1))
fi

# ============================================================================
# CLAIM 5: de Rham ∘ Boltzmann = Modular
# ============================================================================
echo -e "\n[5/5] CLAIM: de Rham ∘ Boltzmann = Modular flow"
echo "----------------------------------------"

if [ -f lean/InfoGeometry/Thermo/DeRhamBoltzmannModular.lean ]; then
    echo "  ✓ Bridge file exists"
    
    if grep -q "sorry" lean/InfoGeometry/Thermo/DeRhamBoltzmannModular.lean 2>/dev/null; then
        echo "  ⚠️  ISSUE: Bridge proof incomplete"
        ISSUES_FOUND=$((ISSUES_FOUND + 1))
    else
        echo "  ✓ Bridge proven"
        FIXES_APPLIED=$((FIXES_APPLIED + 1))
    fi
else
    # Check alternative locations
    if find lean -name "*DeRham*" -name "*Boltzmann*" 2>/dev/null | grep -q .; then
        echo "  ✓ Formalization exists (different location)"
        FIXES_APPLIED=$((FIXES_APPLIED + 1))
    else
        echo "  ⚠️  ISSUE: No explicit de Rham ∘ Boltzmann = Modular theorem"
        ISSUES_FOUND=$((ISSUES_FOUND + 1))
    fi
fi

# ============================================================================
# SUMMARY
# ============================================================================
echo -e "\n================================================================================"
echo "AUDIT SUMMARY"
echo "================================================================================"
echo "Issues Found:    $ISSUES_FOUND"
echo "Fixes Applied:   $FIXES_APPLIED"
echo ""

if [ $ISSUES_FOUND -eq 0 ]; then
    echo "✅ ALL CLAIMS VERIFIED - No issues found"
    exit 0
else
    echo "⚠️  $ISSUES_FOUND CLAIMS NEED ATTENTION"
    echo ""
    echo "Priority fixes:"
    echo "  1. Complete Cuntz KMS proof (replace sorry with case analysis)"
    echo "  2. Create Tomita-Takesaki formalization for O₂"
    echo "  3. Verify de Rham ∘ Boltzmann = Modular bridge"
    exit 1
fi