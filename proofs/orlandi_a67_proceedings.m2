loadPackage "Dmodules"

W = QQ[cForward, cReverse, tau, dcForward, dcReverse, dtau,
  WeylAlgebra => {{cForward, dcForward}, {cReverse, dcReverse}, {tau, dtau}}]

centroidRelations = map(W^1, W^1, matrix {{
  2 * tau - (cReverse - cForward) * (56/100)
}})

M = coker centroidRelations

assert(substitute(2 * tau - (cReverse - cForward) * (56/100), {
  cForward => 409497/100, cReverse => 409805/100, tau => 1078/1250
}) == 0)

assert(10/100 + 84/100 + 6/100 == 1)
assert((13/10) / 1 == 13/10)
assert((81/10) / (17/10) == 81/17)
assert(7/10 < 13/10)
assert(7/10 < 12/4)

print M
exit(0)
