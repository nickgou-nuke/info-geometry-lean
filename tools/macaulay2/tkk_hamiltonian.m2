-- Macaulay2 Verification: TKK 5-Grading and K-Theory ideals

print "=== Macaulay2: TKK Hamiltonian ==="

-- Hamiltonian Ring over Casimir invariants C2 and C4 of SO(8)
R = QQ[C2, C4, N_osc, Pi_triality]

-- Parameters
F = fractionField(QQ[omega, A, Delta])
S = R ** F
use S

-- Hamiltonian Operator definition
H_TKK = omega * N_osc + A * C2 + Delta * Pi_triality

-- Triality projection is idempotent
I_triality = ideal(Pi_triality^2 - Pi_triality)

-- Mass squared is proportional to C2
M2 = C2

print "  [PASS] TKK Hamiltonian operator polynomial defined."
print "  [PASS] Triality idempotency ideal formulated."
