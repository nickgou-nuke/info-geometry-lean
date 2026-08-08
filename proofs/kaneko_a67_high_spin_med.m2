loadPackage "Dmodules"

W = QQ[VCM, VCr, ell, ls, MED, dVCM, dVCr, dell, dls, dMED,
  WeylAlgebra => {{VCM, dVCM}, {VCr, dVCr}, {ell, dell}, {ls, dls}, {MED, dMED}}]

medRelations = map(W^1, W^1, matrix {{
  MED - (VCM + VCr + ell + ls)
}})

M = coker medRelations

assert(substitute(MED - (VCM + VCr + ell + ls), {
  VCM => -40, VCr => 140, ell => 0, ls => -132, MED => -32
}) == 0)

assert((-95) - (-58) == -37)
assert((-66) - 66 == -132)
assert(280 * (4/2 - 3/2) == 140)
assert(2 + 1 == 3)
assert(140 + (-132) == 8)

print M
exit(0)
