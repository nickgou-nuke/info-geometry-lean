loadPackage "Dmodules"

W = QQ[eps, Rm, deps, dRm, WeylAlgebra => {{eps, deps}, {Rm, dRm}}]

asymmetryRelations = map(W^1, W^1, matrix {{
  Rm * (1 - eps)^2 - (1 + eps)^2
}})

M = coker asymmetryRelations

assert(substitute(Rm * (1 - eps)^2 - (1 + eps)^2, {
  eps => -872/10000, Rm => 1301881/1846881
}) == 0)

assert(substitute(Rm * (1 - eps)^2 - (1 + eps)^2, {
  eps => 120/1000, Rm => 196/121
}) == 0)

etaUniform = ((752/1000) - (410/1000)) / (752/1000)
assert(etaUniform == 171/376)
assert((2/3) * (615/1000) == 41/100)

print M
exit(0)
