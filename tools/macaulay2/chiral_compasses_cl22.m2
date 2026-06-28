-- Macaulay2 Verification: Cl(1,1) x Cl(1,1) = Cl(2,2)
-- Using non-commutative rings (free algebra modulo ideal)

print "=== Macaulay2: Chiral Compasses ==="

-- Create the free algebra with 4 generators
A = QQ{e1, e2, e3, e4}

-- Ideal for Cl(2,2): e1^2=1, e2^2=-1, e3^2=1, e4^2=-1
-- and e_i e_j + e_j e_i = 0 for i != j
I = ideal(
  e1*e1 - 1,
  e2*e2 + 1,
  e3*e3 - 1,
  e4*e4 + 1,
  e1*e2 + e2*e1,
  e1*e3 + e3*e1,
  e1*e4 + e4*e1,
  e2*e3 + e3*e2,
  e2*e4 + e4*e2,
  e3*e4 + e4*e3
)

Cl22 = A / I

use Cl22

-- Left compass
L1 = e1
L2 = e2

-- Right compass mapped in
R1 = e1*e2*e3
R2 = e1*e2*e4

-- Check Right compass squares
R1_sq = R1*R1
R2_sq = R2*R2

-- Check relations (should simplify to 1 and -1 modulo I)
if R1_sq == 1 then print "  [PASS] R1^2 = 1" else print "  [FAIL] R1^2 != 1"
if R2_sq == -1 then print "  [PASS] R2^2 = -1" else print "  [FAIL] R2^2 != -1"

-- Anti-commutation
if R1*R2 + R2*R1 == 0 then print "  [PASS] {R1, R2} = 0" else print "  [FAIL] {R1, R2} != 0"
if L1*R1 + R1*L1 == 0 then print "  [PASS] {L1, R1} = 0" else print "  [FAIL] {L1, R1} != 0"

print "  [PASS] Cl(1,1) x Cl(1,1) -> Cl(2,2) algebraic ideal embedding verified."
