-- Macaulay2 exact-rational certificate for the KL symmetric/antisymmetric decomposition.
-- Run with: M2 --script tools/macaulay2/kl_divergence_decomposition.m2
--
-- Macaulay2 is used here only for the exact algebraic shadow of the decomposition,
-- not for transcendental log evaluation.  The actual logarithmic KL values are
-- checked in the SymPy and Sage certificates.

R = QQ[dpq,dqp]

dsym = (dpq + dqp) / 2
dasym = (dpq - dqp) / 2

assert(sub(dpq - (dsym + dasym), R) == 0_R)
assert(sub(dqp - (dsym - dasym), R) == 0_R)
assert(sub((dpq + dqp)/2 - dsym, R) == 0_R)
assert(sub((dpq - dqp)/2 - dasym, R) == 0_R)
assert(sub(((dqp - dpq)/2) + dasym, R) == 0_R)
print "PASS: exact-rational KL symmetric/antisymmetric algebraic identities"

needsPackage "Dmodules";
W = makeWA(QQ[x]);
xW = W_0; Dx = W_1;
assert(Dx*xW - xW*Dx == 1_W);
print "PASS: Dmodules Weyl commutator [Dx,x] = 1";
print "KL_DIVERGENCE_DECOMPOSITION_MACAULAY2_OK";
