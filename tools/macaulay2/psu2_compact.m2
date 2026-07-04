R = QQ[ur, ui, vr, vi]
uNormSq = ur^2 + ui^2
vNormSq = vr^2 + vi^2
detPoly = uNormSq + vNormSq

unitSphereIdeal = ideal(uNormSq + vNormSq - 1)

testPoly = detPoly - 1

M = matrix{{testPoly}}
N = matrix gens unitSphereIdeal

C = M // N
rem = M % N

print("Quotient matrix: ", C)
print("Remainder: ", rem)

assert(M - C * N == 0)
assert(rem == 0)

print("Proof complete: det - 1 belongs perfectly to the unit sphere ideal.")
