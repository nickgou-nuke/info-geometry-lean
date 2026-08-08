loadPackage "Dmodules"

W = QQ[Tz, M, a, b, c, mu, md, iso0, iso3, d, dn, dTz, dM,
  WeylAlgebra => {{Tz, M}, {dTz, dM}}]

immeRelation = M - (a + b*Tz + c*Tz^2)
IMMEModule = coker map(W^1, W^1, matrix {{immeRelation}})

assert(substitute(immeRelation, {Tz => Tz}) == M - a - b*Tz - c*Tz^2)
assert(substitute(immeRelation - substitute(immeRelation, {Tz => -Tz}), {M => 0}) == -2*b*Tz)
assert(substitute((a + b*Tz + c*Tz^2) - (a + b*(-Tz) + c*(-Tz)^2), {Tz => Tz}) == 2*b*Tz)
assert((467/100) - (219/100) == 62/25)
assert(((219/100) + (467/100)) / 2 == 343/100)
assert(((219/100) - (467/100)) / 2 == -31/25)
assert(d*((1/2) + (-1/2)) == 0)
assert((93957/100) - (93828/100) == 129/100)
assert((280894/100) - (280842/100) == 13/25)
assert((466787/100) - (466766/100) == 21/100)
assert((653389/100) - (653424/100) == -7/20)

print IMMEModule
exit(0)
