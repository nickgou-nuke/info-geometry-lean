loadPackage "Dmodules"

W = QQ[Mexp, M01, M10, b, dMexp, dM01, dM10, db,
  WeylAlgebra => {{Mexp, dMexp}, {M01, dM01}, {M10, dM10}, {b, db}}]

mixingRelations = map(W^1, W^1, matrix {{
  b * (M01 + M10) - Mexp
}})

M = coker mixingRelations

assert(substitute(b * (M01 + M10) - Mexp, {
  Mexp => 138/10000, M01 => -228/10000, M10 => 801/10000, b => 46/191
}) == 0)

assert((138/10000 / ((-228/10000) + (801/10000)))^2 == 2116/36481)
assert((162/10000 / ((1086/10000) + (-127/10000)))^2 == 26244/919681)
assert((160/100000 / ((819/100000) + (2533/100000)))^2 == 400/175561)
assert((38/10000 / ((-144/10000) + (-233/10000)))^2 == 1444/142129)

print M
exit(0)
