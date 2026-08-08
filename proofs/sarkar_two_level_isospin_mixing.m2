loadPackage "Dmodules"

W = QQ[E1, E2, b2, H11, H22, dE1, dE2,
  WeylAlgebra => {{E1, E2}, {dE1, dE2}}]

obsGap = E2 - E1
traceRelation = H11 + H22 - (E1 + E2)
gapRelation = H22 - H11 - (1 - 2*b2) * obsGap
TwoLevelModule = coker map(W^1, W^2, matrix {{traceRelation, gapRelation}})

assert(substitute(traceRelation, {
  H11 => E1 + b2*(E2 - E1),
  H22 => E2 - b2*(E2 - E1)
}) == 0)

assert(substitute(gapRelation, {
  H11 => E1 + b2*(E2 - E1),
  H22 => E2 - b2*(E2 - E1)
}) == 0)

mg24ObsGap = (996719/100) - (982811/100)
mg24B2 = (1 - 3 / mg24ObsGap) / 2
assert(mg24ObsGap == 3477/25)
assert(mg24B2 == 567/1159)
assert((48/100) < mg24B2 and mg24B2 < (49/100))
assert((1 - 2*mg24B2) * mg24ObsGap == 3)
assert((285084/100) - (265244/100) == 992/5)
assert(2688/1000 == 336/125)
assert(2460/1000 == 123/50)

print TwoLevelModule
exit(0)
