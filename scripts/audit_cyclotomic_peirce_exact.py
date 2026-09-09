#!/usr/bin/env python3
"""Exact independent regression tests. These do not execute Lean or certify proof terms."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]


def equal(A: s.Matrix, B: s.Matrix) -> bool:
    return A.shape == B.shape and all(s.expand(a-b) == 0 for a,b in zip(A,B))


def fourier_polynomials() -> dict[str, object]:
    x = s.Symbol('x')
    root = s.I
    poly = [s.expand(sum(root**(-k*m)*x**m for m in range(4))/4) for k in range(4)]
    rem = lambda p: s.rem(s.expand(p), x**4-1, x)
    for j,k in itertools.product(range(4), repeat=2):
        assert rem(poly[j]*poly[k]-(poly[k] if j == k else 0)) == 0
    assert s.expand(sum(poly)-1) == 0
    for k in range(4):
        assert rem(x*poly[k]-root**k*poly[k]) == 0
    assert s.expand(sum(root**k*poly[k] for k in range(4))-x) == 0
    collapsed = [s.rem(p, x*x+1, x) for p in poly]
    assert collapsed == [0, s.Rational(1,2)-s.I*x/2, 0, s.Rational(1,2)+s.I*x/2]
    # The algebraic identities do not imply self-adjointness in an arbitrary frame.
    S = s.Matrix([[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]])
    U = S*s.diag(1,s.I,-1,-s.I)*S.inv()
    P = [sum((root**(-k*m)*U**m for m in range(4)),s.zeros(4))/4 for k in range(4)]
    assert U**4 == s.eye(4)
    assert P[0] != P[0].conjugate().T
    shift=s.Matrix([[0,0,0,1],[1,0,0,0],[0,1,0,0],[0,0,1,0]])
    clock=s.diag(1,s.I,-1,-s.I)
    cp=[sum((root**(-k*m)*clock**m for m in range(4)),s.zeros(4))/4 for k in range(4)]
    for k in range(4):
        assert shift*cp[k] == cp[(k+1)%4]*shift
    assert shift**4 == s.eye(4)
    return {'orthogonality_polynomial_cases':16, 'eigen_polynomial_cases':4,
            'completeness_and_synthesis':True, 'square_minus_one_collapse':True,
            'algebraic_idempotents_need_not_be_selfadjoint':True,
            'cyclic_sector_covariance_cases':4, 'cyclic_shift_fourth_power':'identity'}


def corner_matrices() -> dict[str, object]:
    n=4
    X=s.Matrix(n,n,s.symbols('x0:16'))
    Y=s.Matrix(n,n,s.symbols('y0:16'))
    projectors=[s.diag(1,0,0,0),s.diag(0,1,1,0),s.diag(0,0,0,1),s.zeros(n)]
    blocks=lambda A:[[p*A*q for q in projectors] for p in projectors]
    BX,BY,BXY=blocks(X),blocks(Y),blocks(X*Y)
    assert equal(sum((B for row in BX for B in row),s.zeros(n)),X)
    for i,j in itertools.product(range(4),repeat=2):
        assert equal(sum((BX[i][k]*BY[k][j] for k in range(4)),s.zeros(n)),BXY[i][j])
        assert equal(projectors[i]*BX[i][j]*projectors[j],BX[i][j])
        if i != j:
            assert equal(BX[i][j]*BX[i][j],s.zeros(n))
    # In a block array the corner identity is diag(e_i), not diag(I).
    assert blocks(s.eye(n))[1][1] == projectors[1] != s.eye(n)
    return {'symbolic_product_blocks':16,'reconstruction':True,'zero_projector_allowed':True,
            'off_diagonal_square_zero_cases':12,'corner_identity_not_ambient_identity':True}


def exterior(d: int) -> dict[str, object]:
    n=2**d
    phase=s.diag(*[s.I**mask.bit_count() for mask in range(n)])
    parity=s.diag(*[(-1)**mask.bit_count() for mask in range(n)])
    assert phase**2 == parity and phase**4 == s.eye(n)
    assert phase**2 != -s.eye(n)
    projections=[sum((s.I**(-k*m)*phase**m for m in range(4)),s.zeros(n))/4 for k in range(4)]
    for k in range(4):
        expected=s.diag(*[int(mask.bit_count()%4==k) for mask in range(n)])
        assert projections[k] == expected
    assert projections[0]+projections[2] == (s.eye(n)+parity)/2
    assert projections[1]+projections[3] == (s.eye(n)-parity)/2
    creations=[]
    contractions=[]
    for i in range(d):
        C=s.zeros(n);A=s.zeros(n)
        for mask in range(n):
            sign=(-1)**((mask&((1<<i)-1)).bit_count())
            if mask&(1<<i):
                A[mask^(1<<i),mask]=sign
            else:
                C[mask|(1<<i),mask]=sign
        creations.append(C);contractions.append(A)
        assert phase*C == s.I*C*phase
        assert phase*A == -s.I*A*phase
        assert C*C == s.zeros(n)
        for k in range(4):
            assert C*projections[k] == projections[(k+1)%4]*C
            assert A*projections[k] == projections[(k-1)%4]*A
    plus=(s.eye(n)+parity)/2;minus=(s.eye(n)-parity)/2
    gammas=[C+A for C,A in zip(creations,contractions)]
    for g in gammas:
        assert plus*g*plus == s.zeros(n) and minus*g*minus == s.zeros(n)
    for g,h in itertools.product(gammas,repeat=2):
        assert plus*g*h*minus == s.zeros(n) and minus*g*h*plus == s.zeros(n)
    # Genuine Clifford paravector product on the same positive Clifford action.
    if d==4:
        t=s.Symbol('t')
        vs=s.symbols('v0:4')
        gv=sum((vs[i]*gammas[i] for i in range(d)),s.zeros(n))
        assert equal((t*s.eye(n)+gv)*(t*s.eye(n)-gv),
                     (t*t-sum(v*v for v in vs))*s.eye(n))
    return {'generating_dimension':d,'state_dimension':n,
            'degree_residue_dimensions':[int(s.trace(p)) for p in projections],
            'creation_and_contraction_covariance':True,'projector_ladder_relations':8*d,
            'chiral_vector_and_pair_corners':True}


def hodge() -> dict[str, object]:
    H=s.zeros(6)
    for i in range(3):
        H[i,i+3]=1
        H[i+3,i]=-1
    assert H*H == -s.eye(6)
    P=[sum((s.I**(-k*m)*H**m for m in range(4)),s.zeros(6))/4 for k in range(4)]
    assert P[0] == s.zeros(6) and P[2] == s.zeros(6)
    assert P[1] == (s.eye(6)-s.I*H)/2
    assert P[3] == (s.eye(6)+s.I*H)/2
    return {'hodge_square':-1,'fourier_ranks':[p.rank() for p in P],
            'matches_existing_chiral_formulas':True}


def main() -> None:
    result={'fourier':fourier_polynomials(),'corners':corner_matrices(),
            'exterior':[exterior(d) for d in (3,4,5)], 'hodge':hodge(),
            'all_exact_checks_passed':True,'Lean_kernel_executed':False,
            'method':'Exact SymPy polynomial reduction and native finite matrix arithmetic',
            'limitation':'Independent regressions are not Lean elaboration or a transitive axiom audit.'}
    out=ROOT/'reports/cyclotomic_peirce'
    out.mkdir(parents=True,exist_ok=True)
    (out/'exact-regressions.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
