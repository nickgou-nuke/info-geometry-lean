R = QQ[d,k]
tripotentIdeal = ideal(d^3 - d)
assert(degree tripotentIdeal == 3)

su5AdjointDim = 5^2 - 1
spinorDim = 2^5
varlamovEven = binomial(5,0) + binomial(5,2) + binomial(5,4)
varlamovOdd = binomial(5,1) + binomial(5,3) + binomial(5,5)
wittenMoebiusIndex = varlamovEven - varlamovOdd
weylA4Order = 5*4*3*2*1
mobiusGroupOrder = 2

assert(su5AdjointDim == 24)
assert(spinorDim == 32)
assert(varlamovEven == 16)
assert(varlamovOdd == 16)
assert(varlamovEven + varlamovOdd == spinorDim)
assert(wittenMoebiusIndex == 0)
assert(weylA4Order == 120)
assert(mobiusGroupOrder == 2)
assert(-(-k) == k)

W = QQ[k,dk, WeylAlgebra => {k=>dk}]
kleinQuotientDModule = ideal(k*dk + dk*k)
assert(numgens kleinQuotientDModule == 1)

print {
  "su5AdjointDim", su5AdjointDim,
  "spinorDim", spinorDim,
  "varlamovEven", varlamovEven,
  "varlamovOdd", varlamovOdd,
  "wittenMoebiusIndex", wittenMoebiusIndex,
  "weylA4Order", weylA4Order,
  "mobiusGroupOrder", mobiusGroupOrder,
  "tripotentDegree", degree tripotentIdeal,
  "dmoduleGenerators", numgens kleinQuotientDModule,
  "edges", 6
}
