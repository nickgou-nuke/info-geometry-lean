loadPackage "Dmodules"

W = QQ[T3, BE1m, BE1p, eps, R, eta, A1, A0, C, rho, dT3, dR,
  WeylAlgebra => {{T3, R}, {dT3, dR}}]

mirrorT3Relation = 2*T3 - (33 - 34)
ratioRelation = R*(1 - eps)^2 - (1 + eps)^2
etaRelation = eta*752 - (752 - 410)
eq60Numerator = eps*(A1 + 3*A0) - 3*C*rho*(eta*A1 - A0)

MirrorE1Module = coker map(W^1, W^4,
  matrix {{mirrorT3Relation, ratioRelation, etaRelation, eq60Numerator}})

assert(substitute(mirrorT3Relation, {T3 => -1/2}) == 0)
assert((14/10000000)/(4/10000000) == 7/2)
assert((37/10000)/(20/10000) == 37/20)
assert((83/10000000)/(14/10000000) == 83/14)
assert((91/10000)/(37/10000) == 91/37)
assert((9/10000)/(29/10000) == 9/29)
assert(834/1000 == 417/500)
assert(190/10000000 < 1/1000)
assert(53/100000 < 1/1000)
assert((752/1000 - 410/1000)/(752/1000) == 171/376)
assert((2/3)*(615/1000) == 410/1000)
assert(((1 - 872/10000)/(1 + 872/10000))^2 == 1301881/1846881)
assert(((1 + 120/1000)/(1 - 120/1000))^2 == 196/121)
assert((67 - 1)/(4*20)*(1 + 1) == 33/20)

print MirrorE1Module
exit(0)
