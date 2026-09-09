#!/usr/bin/env python3
"""Independent exact symbolic regressions, not Lean elaboration or proof auditing."""
from __future__ import annotations
from collections import Counter
from pathlib import Path
import itertools
import json
import sympy as s

ROOT=Path(__file__).resolve().parents[1]

def zero(x): return s.cancel(s.expand(x)) == 0

def meq(a,b): return a.shape==b.shape and all(zero(x-y) for x,y in zip(a,b))

def boundary_checks():
    q=s.Rational
    K=s.Matrix([[q(1,2),q(1,3),q(1,6)],[q(1,4),q(1,2),q(1,4)],
                [q(1,5),q(2,5),q(2,5)]])
    a=s.Matrix([[q(1,3),0,q(2,3)]])
    b=s.Matrix([0,2,1]); back=K*b; fw=a*K
    z=(a*back)[0]
    assert z==(fw*b)[0] and all(x>0 for x in back)
    Kb=s.diag(*[1/x for x in back])*K*s.diag(*b)
    before=a*s.diag(*back)/z;after=fw*s.diag(*b)/z
    assert Kb*s.ones(3,1)==s.ones(3,1)
    assert all(x>=0 for x in Kb)
    assert before*Kb==after
    assert sum(before)==sum(after)==1
    f=s.Matrix([-2,0,5]);avg=(after*f)[0]
    assert -2<=avg<=5
    # General symbolic pairing conservation: no stochasticity is used here.
    A=s.Matrix(3,3,s.symbols('k0:9'));x=s.Matrix(1,3,s.symbols('a0:3'))
    y=s.Matrix(3,1,s.symbols('b0:3'))
    assert zero(((x*A)*y)[0]-(x*(A*y))[0])
    return {'general_pairing_conservation':True,'hard_terminal_zero_component':True,
            'conditioned_step_consistent':True,'conditioned_kernel_stochastic':True}

def memory_checks():
    T=s.Matrix([[s.Rational(1,2),1],[0,s.Rational(1,3)]])
    x=s.Matrix([2,-1]); inputs=[s.Matrix([k,(-1)**k]) for k in range(12)]
    def update(u,x):
        for v in u:x=T*x+v
        return x
    for n in range(13):
        formula=T**n*x+sum((T**(n-1-k)*inputs[k] for k in range(n)),s.zeros(2,1))
        assert update(inputs[:n],x)==formula
        for m in range(n+1):
            assert update(inputs[m:n],update(inputs[:m],x))==formula
    rate,t=s.symbols('rate t',real=True);F=s.Function('F')(t);u=s.symbols('u')
    h=s.exp(-rate*t)*F
    derivative=s.diff(h,t).subs(s.diff(F,t),s.exp(rate*t)*u)
    assert s.simplify(derivative-(-rate*h+u))==0
    shift=s.Matrix([[0,1],[0,0]]);v,w=s.symbols('v w')
    assert shift*shift==s.zeros(2)
    assert (s.eye(2)+v*shift)*(s.eye(2)-v*shift)==s.eye(2)
    assert (s.eye(2)+v*shift)*(s.eye(2)+w*shift)==s.eye(2)+(v+w)*shift
    return {'discrete_convolution_lengths':13,'all_chunk_splits':91,
            'continuous_integrating_factor_derivative':True,'unipotent_inverse_and_addition':True}

def weak_checks():
    ep=s.symbols('epsilon',real=True,nonzero=True)
    psi=s.Matrix([1,0]);phi=s.Matrix([ep,1]);probe=s.Matrix([[0,1],[1,0]])
    overlap=(s.conjugate(phi).T*psi)[0]
    numerator=(s.conjugate(phi).T*probe*psi)[0]
    assert zero(numerator/overlap-1/ep)
    success=overlap**2/(s.conjugate(phi).T*phi)[0]
    assert zero(success/ep**2-1/(1+ep**2))
    ident=(s.conjugate(phi).T*s.eye(2)*psi)[0]/overlap
    assert ident==1
    return {'Pauli_weak_value':'1/epsilon','identity_weak_value':1,
            'success_weighted_square':'1/(1+epsilon^2)'}

def gauge_checks():
    q=s.Rational
    g=[s.Matrix([[1,2],[0,1]]),s.diag(2,q(1,2)),s.Matrix([[0,-1],[1,0]])]
    U=[[s.Matrix([[1,i+j],[0,1]])*s.diag(j+1,q(1,j+1)) for j in range(3)] for i in range(3)]
    K=s.Matrix([[q(1,2),q(1,4),q(1,4)],[q(1,3)]*3,[1,0,0]])
    x=[s.Matrix([i+1,2-i]) for i in range(3)]
    Ug=[[g[i]*U[i][j]*g[j].inv() for j in range(3)] for i in range(3)]
    for i in range(3):
        result=sum((K[i,j]*Ug[i][j]*g[j]*x[j] for j in range(3)),s.zeros(2,1))
        assert result==g[i]*sum((K[i,j]*U[i][j]*x[j] for j in range(3)),s.zeros(2,1))
    for i,j,k in itertools.product(range(3),repeat=3):
        assert Ug[i][j]*Ug[j][k]-Ug[i][k]==g[i]*(U[i][j]*U[j][k]-U[i][k])*g[k].inv()
        assert (g[i]*g[j].inv())*(g[j]*g[k].inv())==g[i]*g[k].inv()
    avg=s.ones(2)/2
    assert avg*s.Matrix([1,-1])==s.zeros(2,1) and avg.det()==0
    return {'all_node_covariance':3,'path_defect_covariance':27,'pure_frame_flatness':27,
            'normalized_average_is_singular':True}

def graph_checks():
    B=s.Matrix(2,3,s.symbols('B0:6',real=True))
    d=s.zeros(5);d[3:5,0:3]=B;cod=d.T;D=d+cod;G=s.diag(1,1,1,-1,-1)
    assert d*d==cod*cod==s.zeros(5)
    assert D*D==d*cod+cod*d
    assert D*G+G*D==s.zeros(5)
    assert D*D==s.diag(B.T*B,B*B.T)
    x=s.Matrix(3,1,s.symbols('x0:3',real=True))
    energy=sum(v*v for v in B*x)
    assert zero(energy-(x.T*B.T*B*x)[0])
    incidence=s.Matrix([[-1,1,0],[0,-1,1]])
    assert incidence*s.ones(3,1)==s.zeros(2,1)
    return {'generic_rectangular_differential_squared':0,'codifferential_squared':0,
            'Dirac_Laplacian_blocks':True,'Dirac_is_odd':True,'energy_identity':True,
            'path_graph_constant_kernel':True}

def root_checks():
    positive=[(1,0),(0,1),(1,1),(2,1),(3,1),(3,2)]
    roots=positive+[(-m,-n) for m,n in positive]
    counts=Counter(n for m,n in roots)
    length=lambda m,n:2*m*m-6*m*n+6*n*n
    s1=lambda m,n:(-m+3*n,n)
    s2=lambda m,n:(m,m-n)
    assert dict(counts)=={0:2,1:4,2:1,-1:4,-2:1}
    assert Counter(length(*r) for r in roots)=={2:6,6:6}
    for reflect in (s1,s2):
        assert set(reflect(*r) for r in roots)==set(roots)
        assert all(length(*reflect(*r))==length(*r) for r in roots)
        weights={r:s.Symbol('w'+str(k),positive=True) for k,r in enumerate(roots)}
        Z=sum(weights.values())
        Zp=sum(weights[reflect(*r)] for r in roots)
        assert Zp==Z
        for r in roots:assert weights[reflect(*r)]/Zp==weights[reflect(*r)]/Z
    assert length(0,1)==6 and length(1,0)==2
    return {'root_count':12,'grade_counts':dict(sorted(counts.items())),
            'length_counts':{2:6,6:6},'two_Weyl_permutation_normalizations':True,
            'root_length_is_not_grade':True}

def pairing_checks():
    xi,re,im=s.symbols('xi re im',real=True);Delta=re+s.I*im;E=s.symbols('E')
    H=s.Matrix([[xi,Delta],[s.conjugate(Delta),-xi]])
    assert H.adjoint()==H
    assert meq(H*H,(xi**2+re**2+im**2)*s.eye(2))
    assert zero((H-E*s.eye(2)).det()-(E**2-xi**2-re**2-im**2))
    T,z=s.symbols('T z',real=True)
    assert zero((1-T*z*z)-((1-T)+T*(1-z*z)))
    return {'Hermitian_pairing_block':True,'spectral_square':True,'characteristic_polynomial':True,
            'radicand_nonnegative_decomposition':'(1-T)+T*cos(phi/2)^2',
            'no_topological_classification_tested':True}

def main():
    report={'boundary':boundary_checks(),'memory':memory_checks(),'weak_value':weak_checks(),
            'gauge':gauge_checks(),'graph':graph_checks(),'roots':root_checks(),'pairing':pairing_checks(),
            'all_checks_passed':True,'Lean_kernel_executed':False,
            'method':'Exact symbolic and rational arithmetic; finite algebra regressions only'}
    out=ROOT/'reports/streaming_boundary/exact-regressions.json';out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

