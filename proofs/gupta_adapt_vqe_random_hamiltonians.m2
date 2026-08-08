loadPackage "Dmodules"

W = QQ[Eexact, Eadapt, delta, dEexact, dEadapt,
  WeylAlgebra => {{Eexact, Eadapt}, {dEexact, dEadapt}}]

relativeErrorRelation = delta * Eexact - (Eexact - Eadapt)
RelativeErrorModule = coker map(W^1, W^1, matrix {{relativeErrorRelation}})

assert(substitute(relativeErrorRelation, {Eadapt => Eexact, delta => 0}) == 0)
assert(20 * 19 * 18 * 17 / 24 == 4845)
assert(20 / 2 == 10)
assert(9 * 20 == 180)
assert((4845 - 180) / 4845 == 311/323)
assert(2 * (18 * 17 / 2) == 306)
assert(10 + 3 * (10 * 9 / 2) == 145)
assert((18 * 17 / 2) + 18 == 171)
assert(2^10 == 1024)
assert(abs(275/100 - 278/100) == 3/100)
assert(9936/10000 >= 993/1000)
assert(9966/10000 >= 993/1000)
assert(2^(2*10 - 1) - 2 == 524286)
assert(2 * (4^(4 - 1) - 1) == 126)

print RelativeErrorModule
exit(0)
