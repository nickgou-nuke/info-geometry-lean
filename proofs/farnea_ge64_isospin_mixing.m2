loadPackage "Dmodules"

W = QQ[alpha2, BE164, BE166, delta, q, T3, dAlpha, dBE1,
  WeylAlgebra => {{alpha2, BE164}, {dAlpha, dBE1}}]

eq7Relation = 8*alpha2*BE166 - 3*BE164
quadrupoleRelation = q*(1 + delta^2) - delta^2
T3Relation = 2*T3 - (32 - 32)

Ge64MixingModule = coker map(W^1, W^3,
  matrix {{eq7Relation, quadrupoleRelation, T3Relation}})

assert(32 + 32 == 64)
assert(40 + 32 - 4*2 == 64)
assert(substitute(T3Relation, {T3 => 0}) == 0)
assert(substitute(quadrupoleRelation, {delta => -39/10, q => 1521/1621}) == 0)
assert(54/100 < 80/100)
assert(4 < 242/10 and 242/10 < 431/10)
assert(567 + 130 + 89 == 786)
assert(130 + 89 < 567)
assert((247/1000000000)/(37/10000000) == 247/3700)
assert((606/100)/(39/10000) == 20200/13)
assert((71/100) < (606/100))
assert((1)/(4/10) == 5/2)
assert((2/3)*(1 - (-1))^2 == 8/3)
assert((3/8)*((247/1000000000)/(37/10000000)) == 741/29600)
assert(100*(741/29600) == 741/296)
assert(substitute(eq7Relation, {
  alpha2 => 741/29600,
  BE164 => 247/1000000000,
  BE166 => 37/10000000}) == 0)

print Ge64MixingModule
exit(0)
