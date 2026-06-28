#!/usr/bin/env python3
from galgebra.ga import Ga
ga = Ga('e1 e2', g=[1,1])
print("type(ga):", type(ga))
print("dir(ga):", [attr for attr in dir(ga) if not attr.startswith('_')])
# Try to see what mv returns
try:
    mv = ga.mv()
    print("mv:", mv)
    print("type(mv):", type(mv))
    if hasattr(mv, '__len__'):
        print("len(mv):", len(mv))
except Exception as e:
    print("mv error:", e)
# Try basis_vectors
try:
    bv = ga.basis_vectors
    print("basis_vectors:", bv)
    print("type(basis_vectors):", type(bv))
except Exception as e:
    print("basis_vectors error:", e)
# Try basis
try:
    basis = ga.basis
    print("basis:", basis)
    print("type(basis):", type(basis))
except Exception as e:
    print("basis error:", e)