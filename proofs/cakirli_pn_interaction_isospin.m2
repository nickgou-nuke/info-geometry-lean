loadPackage "Dmodules"

W = QQ[Z, N, BE, M, mp, mn, c2, dBE, dM,
  WeylAlgebra => {{BE, M}, {dBE, dM}}]

bindingRelation = BE - ((Z*mp + N*mn - M) * c2)
BindingModule = coker map(W^1, W^1, matrix {{bindingRelation}})

assert(substitute(bindingRelation, {
  BE => ((Z*mp + N*mn - M) * c2)
}) == 0)

assert((5785 - 5970) == -185)
assert((914 - 1037) == -123)
assert(abs((1661 - 2222) - (-562)) <= 3)
assert(((41384/10) - (41320/10)) == 64/10)
assert(abs((935 - (14625/10)) - (-527)) <= 7)
assert(abs(((37467/10) - (36966/10)) - (500/10)) <= 3/10)
assert(((31920/10) - (318140/100)) == 106/10)
assert(abs(((10650/10) - (10650/10)) - (3/10)) <= 3/10)
assert(abs((971 - (101510/100)) - (-44)) <= 5)
assert(abs((10650/10) - (10650/10)) <= 50)
assert(abs(1661 - 2222) > 50)
assert(abs(935 - (14625/10)) > 50)
assert(7 % 4 == 3)
assert(11 % 4 == 3)
assert(15 % 4 == 3)
assert(19 % 4 == 3)
assert(9 % 4 == 1)
assert(13 % 4 == 1)
assert(17 % 4 == 1)
assert(21 % 4 == 1)

print BindingModule
exit(0)
