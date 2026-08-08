loadPackage "Dmodules"

W = QQ[mIV, mIS, bAs, bSe, dmIV, dmIS, dbAs, dbSe,
  WeylAlgebra => {{mIV, dmIV}, {mIS, dmIS}, {bAs, dbAs}, {bSe, dbSe}}]

e1Relations = map(W^1, W^2, matrix {{
  10*bAs - (mIV + mIS)^2,
  10*bSe - (mIV - mIS)^2
}})

M = coker e1Relations

assert(substitute(10*bAs - (mIV + mIS)^2, {
  mIV => 29/10000, mIS => 9/10000, bAs => 361/250000000
}) == 0)

assert(substitute(10*bSe - (mIV - mIS)^2, {
  mIV => 29/10000, mIS => 9/10000, bSe => 1/2500000
}) == 0)

assert((361/250000000)/(1/2500000) == 361/100)
assert((9/10000)/(29/10000) == 9/29)

R = QQ[e, rho, DeltaE0, ri, rj]
C = ((67 - 1) * e^2) / (4 * rho * DeltaE0)
oneBody = ri^3 / rho^2
twoBody = ri * rj^2 / rho^3
e1Kernel = C * (oneBody + twoBody)

assert(substitute(e1Kernel, {e => 1, rho => 1, DeltaE0 => 20, ri => 1, rj => 1}) == 33/20)

print M
exit(0)
