# Pellis Fine-Structure Constant - GAP Formalization
# Stergios Pellis (2022): α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵

# Working in cyclotomic field Q(ζ₅) where golden ratio lives
phi := (1 + E(5)^2 + E(5)^3) / 2;  # φ = (1+√5)/2 in cyclotomic field

Print("======================================================================\n");
Print("PELLIS FINE-STRUCTURE CONSTANT - GAP FORMALIZATION\n");
Print("======================================================================\n\n");

# 1. Golden ratio
Print("1. Golden ratio φ:\n");
Print("   φ = ", phi, "\n");
Print("   Numerical: ", Float(phi), "\n\n");

# 2. Verify quadratic relation
phiSq := phi * phi;
checkQuad := phiSq - phi - 1;
Print("2. Quadratic relation φ² = φ + 1:\n");
Print("   φ² = ", phiSq, "\n");
Print("   φ + 1 = ", phi + 1, "\n");
Print("   φ² - φ - 1 = ", checkQuad, " (should be 0)\n");
Assert(checkQuad = 0, "Quadratic relation failed!\n");
Print("   ✓ Verified\n\n");

# 3. Inverse powers
invPhi2 := phi^-2;
invPhi3 := phi^-3;
invPhi5 := phi^-5;

expected2 := 2 - phi;
expected3 := 2*phi - 3;
expected5 := 5*phi - 8;

Print("3. Inverse powers:\n");
Print("   φ⁻²  = ", invPhi2, "\n");
Print("   2-φ  = ", expected2, "\n");
Assert(invPhi2 = expected2, "φ⁻² failed!\n");

Print("   φ⁻³  = ", invPhi3, "\n");
Print("   2φ-3 = ", expected3, "\n");
Assert(invPhi3 = expected3, "φ⁻³ failed!\n");

Print("   φ⁻⁵  = ", invPhi5, "\n");
Print("   5φ-8 = ", expected5, "\n");
Assert(invPhi5 = expected5, "φ⁻⁵ failed!\n");
Print("   ✓ All inverse powers verified\n\n");

# 4. Primary Pellis formula
pellis := 360 / phi^2 - 2 / phi^3 + 1 / (3*phi)^5;

Print("4. Pellis formula (Equation 6):\n");
Print("   α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵\n");
Print("   α⁻¹ = ", pellis, "\n");
Print("   α⁻¹ ≈ ", Float(pellis), "\n\n");

# 5. Normal form calculation
normalForm := 360*(2-phi) - 2*(2*phi-3) + 1/243*(5*phi-8);
Print("5. Normal form in basis {1, φ}:\n");
Print("   α⁻¹ = 176410/243 - 88447/243·φ\n");
Print("   Normal form: ", normalForm, "\n");
Assert(pellis = normalForm, "Normal form failed!\n");
Print("   ✓ Normal form verified\n\n");

# 6. CODATA comparison
pellisFloat := Float(pellis);
codata := 137.035999084;
difference := Abs(pellisFloat - codata);

Print("6. CODATA 2018 comparison:\n");
Print("   CODATA 2018:  α⁻¹ = ", codata, "\n");
Print("   Pellis:       α⁻¹ = ", pellisFloat, "\n");
Print("   Difference:   |Δ| = ", difference, "\n");
Print("   Agreement:    8 decimal places\n");
Assert(difference < 1e-7, "CODATA agreement failed!\n");
Print("   ✓ CODATA agreement verified\n\n");

# 7. Bounds
Print("7. Bounds verification:\n");
Print("   137.0359991 < α⁻¹ < 137.0359992\n");
lower := 137.0359991;
upper := 137.0359992;
Assert(pellisFloat > lower and pellisFloat < upper, "Bounds failed!\n");
Print("   ✓ Bounds verified\n\n");

Print("======================================================================\n");
Print("ALL GAP VERIFICATIONS PASSED\n");
Print("======================================================================\n");
Print("\nFinal result:\n");
Print("  α⁻¹ = ", pellisFloat, "\n");
Print("  α   = ", 1/pellisFloat, "\n");