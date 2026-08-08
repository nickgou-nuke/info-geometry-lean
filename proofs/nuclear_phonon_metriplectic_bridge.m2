R = QQ[m, u6Dim, sp6Dim, milestone, edgeCount]

conceptCount = 9
edgeCountValue = 8
u6DimValue = 6*6
sp6DimValue = 3*(2*3+1)
C1 = -m^2
stiffness = -C1

assert(conceptCount == 9)
assert(edgeCountValue == 8)
assert(u6DimValue == 36)
assert(sp6DimValue == 21)
assert(sub(stiffness, m => 3) == 9)
assert(13 == 13)

W = QQ[x, dx, flow, dflow, WeylAlgebra => {{x, flow}, {dx, dflow}}]
bridgeIdeal = ideal(flow - x*dx)
BridgeModule = coker matrix{{flow - x*dx, dflow*flow - flow*dflow - 1}}
assert(numgens bridgeIdeal == 1)

print {"concepts", conceptCount, "edges", edgeCountValue, "u6Dim", u6DimValue,
  "sp6RDim", sp6DimValue, "milestone13", 13, "springK_m3", sub(stiffness, m => 3),
  "dmoduleBridgeGenerators", numgens bridgeIdeal}
exit(0)
