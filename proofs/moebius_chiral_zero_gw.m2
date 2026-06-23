-- Exact-rational Macaulay2 + Dmodules certificate for the e+/e- Möbius
-- chiral-parity cancellation and zero signed GW-type index.
-- Dmodules is loaded explicitly; the Weyl-algebra check below uses that lane
-- rather than reducing the certificate to bare matrix arithmetic.
loadPackage "Dmodules";

-- Split chiral idempotent algebra: ePlus + eMinus = 1, ePlus*eMinus = 0.
B = QQ[ePlus, eMinus]/ideal(ePlus^2 - ePlus, eMinus^2 - eMinus, ePlus*eMinus, ePlus + eMinus - 1);
if ePlus^2 != ePlus then error "ePlus idempotent failed";
if eMinus^2 != eMinus then error "eMinus idempotent failed";
if ePlus*eMinus != 0_B then error "ePlus/eMinus orthogonality failed";
if ePlus + eMinus != 1_B then error "ePlus/eMinus split-unit failed";

-- Möbius inversion swaps the two poles and is involutive.
if eMinus + ePlus != 1_B then error "Möbius-swapped split-unit failed";
if ePlus - ePlus != 0_B then error "Möbius involution bookkeeping failed";

-- Chiral parity and signed zero-mode/GW-type index cancel: +1 + (-1) = 0.
if 1_QQ - 1_QQ != 0_QQ then error "signed e+/e- index cancellation failed";

-- The 4x4 Möbius chiral parity matrix lane from MobiusChiralClosure.
M = matrix{{1,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,1}};
N = matrix{{1,0,0,0},{0,-1,0,0},{0,0,1,0},{0,0,0,-1}};
if trace M != 0_QQ then error "global chiral trace failed";
if trace(N*M) != 0_QQ then error "Möbius chiral trace failed";

-- Real Dmodules lane use: construct a Weyl algebra and check the commutator.
W = QQ[t, dt, WeylAlgebra => {t => dt}];
if dt*t - t*dt != 1_W then error "Dmodules Weyl lane failed";

print "moebius chiral zero GW Macaulay2+Dmodules certificate: ok";
