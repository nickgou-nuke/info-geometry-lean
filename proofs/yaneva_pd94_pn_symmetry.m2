R = QQ[q,dq, WeylAlgebra => {q=>dq}]

ZPd94 = 46
NPd94 = 48
APd94 = 94
protonHoles = 50 - ZPd94
neutronHoles = 50 - NPd94
totalHoles = protonHoles + neutronHoles
g92Degeneracy = 10
singleJConfigCount = binomial(g92Degeneracy, protonHoles) * binomial(g92Degeneracy, neutronHoles)
isoscalarDim = 2*0 + 1
isovectorDim = 2*1 + 1
yrast8B = 205
yrast8BLower = yrast8B - 25
yrast8BUpper = yrast8B + 34
gdsNeutronCharge = 84/100
pnDmodule = ideal(q*dq - dq*q - 1)
gds8to6 = 192
g9full14 = 112
g9t0_14 = 82
g9t1_14 = 9
g9full8 = 144
g9t0_8 = 191
g9t1_8 = 11
g9full6 = 398
g9t0_6 = 398
g9t1_6 = 5

assert(ZPd94 + NPd94 == APd94)
assert(NPd94 == ZPd94 + 2)
assert((NPd94 - ZPd94)/2 == 1)
assert(protonHoles == 4 and neutronHoles == 2 and totalHoles == 6)
assert(g92Degeneracy == 10)
assert(singleJConfigCount == 9450)
assert(isoscalarDim == 1 and isovectorDim == 3)
assert(8 == 6 + 2 and 6 == 4 + 2 and 14 == 12 + 2)
assert(yrast8BLower == 180 and yrast8BUpper == 239 and yrast8B < 250)
assert(gdsNeutronCharge == 21/25)
assert(numgens pnDmodule == 1)
assert(yrast8BLower <= gds8to6 and gds8to6 <= yrast8BUpper)
assert(abs(g9full14-g9t0_14) < abs(g9full14-g9t1_14))
assert(abs(g9full8-g9t0_8) < abs(g9full8-g9t1_8))
assert(abs(g9full6-g9t0_6) < abs(g9full6-g9t1_6))

print {
  "A", APd94,
  "Z", ZPd94,
  "N", NPd94,
  "Tz", 1,
  "protonHoles", protonHoles,
  "neutronHoles", neutronHoles,
  "g92Degeneracy", g92Degeneracy,
  "singleJConfigCount", singleJConfigCount,
  "isoscalarDim", isoscalarDim,
  "isovectorDim", isovectorDim,
  "B_E2_8_to_6", yrast8B,
  "table1GDS8to6", gds8to6,
  "table1T0CloserThanT1", true,
  "dmoduleGenerators", numgens pnDmodule,
  "edges", 7
}
