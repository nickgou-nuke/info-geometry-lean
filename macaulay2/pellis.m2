-- Pellis Fine-Structure Constant - Macaulay2 Formalization
-- Stergios Pellis (2022): α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵

-- Working in the ring QQ[sqrt(5)]

R = QQ[x]/(x^2 - x - 1);  -- Golden ratio ring: x^2 = x + 1

phi = x;  -- φ is the generator satisfying φ² = φ + 1

-- Verify quadratic relation
print "1. Quadratic relation φ² = φ + 1:";
phiSq = phi^2;
print(phiSq);
print(phi + 1);
assert(phiSq == phi + 1);

-- Compute inverse powers using the relation
invPhi2 = 2 - phi;  -- φ⁻² = 2 - φ
invPhi3 = 2*phi - 3;  -- φ⁻³ = 2φ - 3  
invPhi5 = 5*phi - 8;  -- φ⁻⁵ = 5φ - 8

print "\n2. Inverse powers:";
print("φ⁻² = " | toString invPhi2);
print("φ⁻³ = " | toString invPhi3);
print("φ⁻⁵ = " | toString invPhi5);

-- Verify inverses
check2 : phi^2 * invPhi2 == 1;
check3 : phi^3 * invPhi3 == 1;
check5 : phi^5 * invPhi5 == 1;

print("\nVerification:");
print("φ² × φ⁻² = " | toString check2);
print("φ³ × φ⁻³ = " | toString check3);
print("φ⁵ × φ⁻⁵ = " | toString check5);

-- Primary Pellis formula
pellis = 360 * invPhi2 - 2 * invPhi3 + 1/(3^5) * invPhi5;

print "\n3. Pellis formula (Equation 6):";
print("α⁻¹ = 360·φ⁻² - 2·φ⁻³ + (3·φ)⁻⁵");
print("α⁻¹ = " | toString pellis);

-- Normal form: a + b·φ
coeff1 = (360*2 - 2*(-3) + 1/243*(-8)) + 0_QQ;
coeffPhi = (360*(-1) - 2*2 + 1/243*5);

normalForm = coeff1 + coeffPhi * phi;
print("\n4. Normal form in basis {1, φ}:");
print("α⁻¹ = " | toString coeff1 | " + " | toString coeffPhi | "·φ");
print("    = " | toString normalForm);

-- Numerical evaluation
print("\n5. Numerical evaluation:";
 phiNum = (1 + sqrt 5)/2;
 pellisNum = 360/phiNum^2 - 2/phiNum^3 + 1/(3*phiNum)^5;
 print("φ ≈ " | toString(1.0 * phiNum));
 print("α⁻¹ ≈ " | toString(1.0 * pellisNum));
 print("CODATA 2018: 137.035999084");
 print("Difference: " | toString(abs(1.0 * pellisNum - 137.035999084)));
)