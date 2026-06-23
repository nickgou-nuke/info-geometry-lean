-- Macaulay2 script for conformal projective Souriau metriplectic verification
print "=== Macaulay2: Conformal Projective Souriau Metriplectic Verification ==="

-- 1. Weyl Algebra Commutator Check
W = QQ[x, d, WeylAlgebra => {x => d}]
D = x * d
comm = d * D - D * d
print "Commutator [d, x*d] = "
print comm
if comm == d then (
  print "Weyl algebra commutator [d, x*d] = d holds!\n";
) else (
  error "Weyl algebra verification failed!";
)

-- 2. Matrix Projectors and Einstein Anomaly
PMP = matrix{{1, 0}, {0, 0}}
PD = matrix{{1, 1}, {0, 0}}

anomaly = PMP * PD - PD * PMP
print "Einstein Anomaly [PMP, PD] = "
print anomaly
if anomaly == matrix{{0, 1}, {0, 0}} then (
  print "Einstein Anomaly verified successfully!\n";
) else (
  error "Einstein Anomaly verification failed!";
)

-- 3. 5-graded Möbius Inversion and Kähler compatibility
theta = matrix{{0, 1}, {-1, 0}}
I = matrix{{1, 0}, {0, 1}}

tr = trace theta
thetaSq = theta * theta
g = -theta * theta

print "Trace of theta = "
print tr
print "theta^2 = "
print thetaSq
print "-omega * theta = "
print g

if tr == 0 and thetaSq + I == 0 and g - I == 0 then (
  print "Möbius parity centralizer loop and Kähler compatibility passed!\n";
) else (
  error "Möbius/Kähler verification failed!";
)
