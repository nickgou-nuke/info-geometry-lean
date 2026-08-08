loadPackage "Dmodules"

W = QQ[Tz, ME, a, b, c, d, dTz, dME,
  WeylAlgebra => {{Tz, ME}, {dTz, dME}}]

immeRelation = ME - (a + b*Tz + c*Tz^2)
cubicRelation = ME - (a + b*Tz + c*Tz^2 + d*Tz^3)
IMMEModule = coker map(W^1, W^2, matrix {{immeRelation, cubicRelation}})

assert(substitute(immeRelation, {ME => a + b*Tz + c*Tz^2}) == 0)
assert(substitute((a + b*Tz + c*Tz^2) - (a + b*(-Tz) + c*(-Tz)^2), {Tz => Tz}) == 2*b*Tz)
assert((467/100) - (219/100) == 62/25)
assert(((219/100) + (467/100)) / 2 == 343/100)
assert(((219/100) - (467/100)) / 2 == -31/25)
assert(782/1000 == 391/500)
assert((0 + 0)/2 - (-57/10) == 57/10)
assert((3/4) - (-3/4) == 3/2)
assert((93957/100) - (93828/100) == 129/100)
assert((280894/100) - (280842/100) == 13/25)
assert((466787/100) - (466766/100) == 21/100)
assert(477 - 0 == 477)
assert(-1298 - 0 == -1298)

print IMMEModule
exit(0)
