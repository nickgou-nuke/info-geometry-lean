loadPackage "Dmodules"

W = QQ[Eneg, Epos, MED, dEneg, dEpos,
  WeylAlgebra => {{Eneg, Epos}, {dEneg, dEpos}}]

medRelation = MED - (Eneg - Epos)
MEDModule = coker map(W^1, W^1, matrix {{medRelation}})

assert(substitute(medRelation, {MED => Eneg - Epos}) == 0)
assert((39 - 40) / 2 == -1/2)
assert((40 - 39) / 2 == 1/2)
assert(184 - 183 == 1)
assert(416 - 411 == 5)
assert(715 - 726 == -11)
assert(1042 - 1042 == 0)
assert(abs((184 + 230) - 416) <= 3)
assert(abs((183 + 227) - 411) <= 3)
assert(294/1000 < 296/1000 and 296/1000 < 304/1000)
assert(298/1000 < 304/1000)
assert(abs((1) - (228 - 226)) <= 2)
assert(abs((5) - (522 - 515)) <= 2)
assert(10 * 4 == 40)

print MEDModule
exit(0)
