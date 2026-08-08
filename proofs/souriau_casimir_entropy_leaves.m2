loadPackage "Dmodules"

W = QQ[C1, C2, S, a, b, c, dC1, dC2,
  WeylAlgebra => {{C1, C2}, {dC1, dC2}}]

entropyRelation = S - (a*C1 + b*C2 + c)
EntropyLeafModule = coker map(W^1, W^1, matrix {{entropyRelation}})

assert(substitute(entropyRelation, {S => a*C1 + b*C2 + c}) == 0)
assert((1/2) * (1/2 + 1) == 3/4)
assert((-1/2) + (1/2) == 0)
assert(-(-67) == 67)

ivgmrCoefficient = ((67 - 1) * 1^2) / (4 * 1 * 20)
ivgmrOneBody = 1
ivgmrTwoBody = 1
assert(ivgmrCoefficient * (ivgmrOneBody + ivgmrTwoBody) == 33/20)

print EntropyLeafModule
exit(0)
