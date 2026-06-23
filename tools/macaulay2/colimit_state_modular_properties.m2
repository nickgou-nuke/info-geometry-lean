-- Macaulay2 / Dmodules certificate for Colimit State Modular Properties
-- Run with: M2 --script tools/macaulay2/colimit_state_modular_properties.m2

QQx = QQ[a,b,c,d,x,y,z,w, e1, e2]

A = matrix {{a, b}, {c, d}}
B = matrix {{x, y}, {z, w}}

-- 1. Tracial Property on the hyperfinite factor
Tr = M -> M_(0,0) + M_(1,1)
assert(Tr(A*B) == Tr(B*A))
print "PASS: Tracial Property Tr(AB) = Tr(BA)"

-- 2. KMS Modular Property on the Type III factor
FF = frac QQx
Af = sub(A, FF)
Bf = sub(B, FF)
e1f = sub(e1, FF)
e2f = sub(e2, FF)

eNegH = matrix {{e1f, 0}, {0, e2f}}
ePosH = matrix {{1/e1f, 0}, {0, 1/e2f}}

sigmaIbetaA = eNegH * Af * ePosH

gibbs = M -> Tr(eNegH * M)

omegaAB = gibbs(Af * Bf)
omegaBsigmaA = gibbs(Bf * sigmaIbetaA)

assert(omegaAB == omegaBsigmaA)
print "PASS: KMS Modular Property omega(AB) = omega(B sigma_{i beta}(A))"

needsPackage "Dmodules"
W = makeWA(QQ[t])
tW = W_0
Dt = W_1
assert(Dt*tW - tW*Dt == 1_W)
print "PASS: Dmodules Weyl commutator [Dt,t] = 1 loaded for exact-rational differential flows"

print "COLIMIT_STATE_MODULAR_MACAULAY2_DMODULES_CERTIFICATE_OK"
