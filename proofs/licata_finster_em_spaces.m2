loadPackage "Dmodules"

W = QQ[k, n, gOrder, piOrder, hRank, stable, dk, dn,
  WeylAlgebra => {{k, n}, {dk, dn}}]

diagonalPiRelation = (k - n) * (piOrder - gOrder)
offDiagonalPiRelation = (k - n) * (piOrder - 1)
sphereCohomologyRelation = (k - n) * hRank
freudenthalBoundary = stable - (2*n - 2 - k)

EMModule = coker map(W^1, W^4,
  matrix {{diagonalPiRelation, offDiagonalPiRelation,
    sphereCohomologyRelation, freudenthalBoundary}})

assert(substitute(diagonalPiRelation, {k => 3, n => 3, piOrder => 7, gOrder => 7}) == 0)
assert(substitute(offDiagonalPiRelation, {k => 2, n => 3, piOrder => 1}) == 0)
assert(substitute(offDiagonalPiRelation, {k => 4, n => 3, piOrder => 1}) == 0)
assert(5 * 1 == 5)
assert(1 * 11 == 11)
assert(1 * 1 == 1)
assert(substitute(sphereCohomologyRelation, {k => 3, n => 4, hRank => 0}) == 0)
assert(substitute(sphereCohomologyRelation, {k => 5, n => 4, hRank => 0}) == 0)
assert(1 + 1 == 2)
assert(2 + 1 == 3)
assert(2 <= 2*2 - 2)
assert(4 <= 2*3 - 2)
assert(not (3 <= 2*2 - 2))

print EMModule
exit(0)
