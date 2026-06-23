#!/usr/bin/env python3
import sympy as sp

def main():
    beta, eps = sp.symbols('beta eps')
    c = sp.Matrix([[0, 1], [0, 0]])
    cd = sp.Matrix([[0, 0], [1, 0]])
    I = sp.eye(2)
    Z = sp.zeros(2)
    N = cd*c
    assert c*c == Z
    assert cd*cd == Z
    assert c*cd + cd*c == I
    assert N*N == N
    H = eps*N
    assert H*sp.Matrix([1,0]) == sp.Matrix([0,0])
    assert H*sp.Matrix([0,1]) == eps*sp.Matrix([0,1])
    trace = sp.exp(-beta*0) + sp.exp(-beta*eps)
    assert sp.simplify(trace - (1 + sp.exp(-beta*eps))) == 0
    print('finite single-mode CAR checks ok')

if __name__ == '__main__':
    main()
