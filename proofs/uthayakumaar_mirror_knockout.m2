loadPackage "Dmodules"

W = QQ[deltaS, Rs, ddeltaS, dRs, WeylAlgebra => {{deltaS, ddeltaS}, {Rs, dRs}}]

suppressionRelations = map(W^1, W^1, matrix {{
  Rs - (61/100 - (2/125) * deltaS)
}})

M = coker suppressionRelations

assert(substitute(Rs - (61/100 - (2/125) * deltaS), {
  deltaS => 1916/1000, Rs => 72418/125000
}) == 0)

assert(substitute(Rs - (61/100 - (2/125) * deltaS), {
  deltaS => 1442/100, Rs => 4741/12500
}) == 0)

assert(1226/10 - 1594/10 == -184/5)
assert(abs(97/100 - 1) <= 1/10)

print M
exit(0)
