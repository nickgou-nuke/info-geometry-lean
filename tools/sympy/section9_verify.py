#!/usr/bin/env python3
"""Section 9: Curvature — SymPy verification"""
import sympy as sp
Id = sp.eye(2)
s1 = sp.Matrix([[0,1],[1,0]])
s2 = sp.Matrix([[0,-sp.I],[sp.I,0]])
s3 = sp.Matrix([[1,0],[0,-1]])
sigma = [Id, s1, s2, s3]
eta = sp.diag(-1,1,1,1)
eps = sp.Matrix([[0,1],[-1,0]])

print("Section 9: Pauli identity")
for A in range(2):
    for B in range(2):
        for Ap in range(2):
            for Bp in range(2):
                lhs = sum(eta[a,b]*sigma[a][A,Ap]*sigma[b][B,Bp] for a in range(4) for b in range(4))
                rhs = -2*eps[A,B]*eps[Ap,Bp]
                assert sp.simplify(lhs-rhs) == 0
print("  σ^aσ^bη_{ab} = -2εε ✓")

print("Lorentz generators σ_{ab}=(i/2)[σ_a,σ_b] traceless:")
for a in range(4):
    for b in range(a+1,4):
        gen = (sp.I/2)*(sigma[a]*sigma[b]-sigma[b]*sigma[a])
        tr = sp.simplify(sp.trace(gen))
        assert tr == 0
print("  All 6 traceless ✓")
print("Section 9 VERIFIED")
