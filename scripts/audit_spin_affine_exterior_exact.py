#!/usr/bin/env python3
"""Exact independent algebra regressions. These are NOT Lean kernel checks."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]

def zero(x):
    return s.cancel(s.expand(x)) == 0

def mat_eq(A, B):
    return A.shape == B.shape and all(zero(a-b) for a,b in zip(A,B))

# A small free associative algebra: scalar coefficients commute, operator words do not.
def add(*xs):
    out={}
    for x in xs:
        for w,c in x.items(): out[w]=out.get(w,0)+c
    return out

def scale(c,x): return {w:c*a for w,a in x.items()}
def mul(x,y):
    out={}
    for u,a in x.items():
        for v,b in y.items(): out[u+v]=out.get(u+v,0)+a*b
    return out

def eq(x,y): return all(zero(add(x,scale(-1,y)).get(w,0)) for w in set(x)|set(y))
def comm(x,y): return add(mul(x,y),scale(-1,mul(y,x)))

def affine_checks():
    M=s.Matrix(3,3,s.symbols('m0:9',real=True))
    b=s.symbols('b0:3',real=True)
    X=[{(i,):s.Integer(1)} for i in range(3)]; unit={():s.Integer(1)}
    Y=[add(*(scale(M[i,j],X[j]) for j in range(3))) for i in range(3)]
    shifted=[add(Y[i],scale(b[i],unit)) for i in range(3)]
    for i,j in itertools.product(range(3),repeat=2):
        assert eq(comm(shifted[i],shifted[j]),comm(Y[i],Y[j]))
        expected=add(*(scale(M[i,k]*M[j,l],comm(X[k],X[l]))
                       for k,l in itertools.product(range(3),repeat=2)))
        assert eq(comm(Y[i],Y[j]),expected)
    G=M.T*M
    q=add(*(scale(G[j,k],mul(X[j],X[k]))
            for j,k in itertools.product(range(3),repeat=2)))
    rhs=add(q,scale(2,add(*(scale(b[i],Y[i]) for i in range(3)))),
            scale(sum(c*c for c in b),unit))
    assert eq(add(*(mul(y,y) for y in shifted)),rhs)
    shear=s.Matrix([[1,1,0],[0,1,0],[0,0,1]]); E=shear.inv()
    assert E*(shear*shear.T)*E.T==s.eye(3)
    assert E.T*E==(shear*shear.T).inv()
    assert E.T*E!=(shear.T*shear).inv()
    return {'noncommutative_affine_bracket_cases':9,'ordered_quadratic_expansion':True,
            'inverse_metric_shear_regression':True}

def spin_checks():
    I=s.I; sx=s.Matrix([[0,1],[1,0]])/2
    sy=s.Matrix([[0,-I],[I,0]])/2; sz=s.diag(1,-1)/2
    up=sx+I*sy; dn=sx-I*sy
    ur,ui,vr,vi=s.symbols('ur ui vr vi',real=True)
    u=ur+I*ui;v=vr+I*vi
    p=u*up+v*dn;m=s.conjugate(v)*up+s.conjugate(u)*dn
    assert mat_eq(p*m-m*p,2*(ur*ur+ui*ui-vr*vr-vi*vi)*sz)
    assert mat_eq(sz*p-p*sz-p,-2*v*dn)
    pp=p.subs({ur:s.Rational(5,4),ui:0,vr:s.Rational(3,4),vi:0})
    mm=m.subs({ur:s.Rational(5,4),ui:0,vr:s.Rational(3,4),vi:0})
    assert pp*mm-mm*pp==2*sz and sz*pp-pp*sz != pp
    assert sx*sx+sy*sy+sz*sz==s.Rational(3,4)*s.eye(2)
    assert sz*sz+sz+dn*up==s.Rational(3,4)*s.eye(2)
    assert up*up-dn*dn==s.zeros(2)
    a,b=s.symbols('a b',nonzero=True)
    p=(a+b)/2*up+(a-b)/2*dn;m=(a-b)/2*up+(a+b)/2*dn
    assert mat_eq((a+b)/(2*a*b)*p-(a-b)/(2*a*b)*m,up)
    t=s.symbols('t');assert zero(t*(t+1)-(t+s.Rational(1,2))**2+s.Rational(1,4))
    assert zero((-t-1)*(-t)-t*(t+1))
    return {'mixed_ladder_relation':True,'full_Cartan_defect':True,
            'exact_hyperbolic_counterexample':["5/4","3/4"],
            'spin_half_Casimir':True,'transverse_inverse':True,'rho_shift':True}

def zorn(a,b,x,y): return (a,b,s.Matrix(x),s.Matrix(y))
def zcoords(X): return s.Matrix([X[0],X[1],*X[2],*X[3]])
def uncoords(v): return zorn(v[0],v[1],v[2:5],v[5:8])
def zm(X,Y):
    a,b,x,y=X;c,d,u,v=Y
    return zorn(a*c+x.dot(v),b*d+y.dot(u),a*u+d*x-y.cross(v),b*v+c*y+x.cross(u))
def zscale(a,X): return uncoords(a*zcoords(X))


def zorn_exterior_checks():
    basis=[uncoords(s.eye(8).col(i)) for i in range(8)]
    U=basis[2:5];V=basis[5:8];plus=basis[0];minus=basis[1]
    def L(X):return s.Matrix.hstack(*(zcoords(zm(X,Y)) for Y in basis))
    C=[L(x) for x in U];A=[L(x) for x in V];I8=s.eye(8);Z8=s.zeros(8)
    for i,j in itertools.product(range(3),repeat=2):
        assert C[i]*A[j]+A[j]*C[i]==(I8 if i==j else Z8)
        assert C[i]*C[j]+C[j]*C[i]==Z8
        assert A[i]*A[j]+A[j]*A[i]==Z8
    vacuum=zcoords(minus)
    for i in range(3):
        assert A[i]*vacuum==s.zeros(8,1)
        assert C[i]*vacuum==zcoords(U[i])
        assert C[i]*zcoords(plus)==s.zeros(8,1)
    P=A[0]*C[0]*A[1]*C[1]*A[2]*C[2]
    target=s.zeros(8);target[1,1]=1
    assert P==target and P*P==P and P.rank()==1
    assert L(minus).rank()==4 and P!=L(minus)
    assert L(zm(U[0],U[1])) != C[0]*C[1]
    iunit=uncoords(zcoords(U[0])-zcoords(V[0]))
    assert zcoords(zm(zm(iunit,plus),zscale(-1,iunit)))==zcoords(minus)
    EC=[];EA=[]
    for i in range(3):
        cr=s.zeros(8);an=s.zeros(8)
        for mask in range(8):
            sign=(-1)**((mask&((1<<i)-1)).bit_count())
            if mask&(1<<i):an[mask^(1<<i),mask]=sign
            else:cr[mask|(1<<i),mask]=sign
        EC.append(cr);EA.append(an)
    cols=[]
    for mask in range(8):
        vec=vacuum
        for i in reversed(range(3)):
            if mask&(1<<i):vec=C[i]*vec
        cols.append(vec)
    F=s.Matrix.hstack(*cols)
    assert F.det() in (1,-1)
    for i in range(3):
        assert F*EC[i]==C[i]*F
        assert F*EA[i]==A[i]*F
    exteriorParity=s.diag(*[(-1)**m.bit_count() for m in range(8)])
    regParity=L(minus)-L(plus)
    assert F*exteriorParity==regParity*F
    gammas=[EC[i]-EA[i] for i in range(3)]
    for i,j in itertools.product(range(3),repeat=2):
        assert gammas[i]*gammas[j]+gammas[j]*gammas[i]==(-2*I8 if i==j else Z8)
    n=s.symbols('n0:3',real=True);v=s.symbols('v0:3',real=True)
    Gn=sum((n[i]*gammas[i] for i in range(3)),s.zeros(8))
    Gv=sum((v[i]*gammas[i] for i in range(3)),s.zeros(8))
    nn=sum(a*a for a in n);nv=sum(a*b for a,b in zip(n,v))
    assert mat_eq(Gn*Gn,-nn*I8)
    assert mat_eq(Gn*Gv*Gn,nn*Gv-2*nv*Gn)
    return {'regular_CAR_relations':27,'vacuum_rank':1,'Peirce_left_action_rank':4,
            'regular_action_not_multiplicative':True,'sandwich_exchanges_poles':True,
            'exterior_to_Zorn_matrix':s.matrix2numpy(F,dtype=int).tolist(),
            'intertwined_creation_modes':3,'intertwined_annihilation_modes':3,
            'parity_intertwined':True,'negative_Clifford_relations':9,
            'reflection_polynomial_identity':True}

def quaternion_checks():
    I2=s.eye(2);qi=s.diag(s.I,-s.I);qj=s.Matrix([[0,1],[-1,0]]);qk=qi*qj
    elems=list(itertools.product((0,1),range(4)))
    mats={(0,i):qi**i for i in range(4)}|{(1,i):qj*qi**i for i in range(4)}
    for (x,i),(y,j) in itertools.product(elems,repeat=2):
        if x==0 and y==0:prod=(0,(i+j)%4)
        elif x==0 and y==1:prod=(1,(j-i)%4)
        elif x==1 and y==0:prod=(1,(i+j)%4)
        else:prod=(0,(2+j-i)%4)
        assert mats[(x,i)]*mats[(y,j)]==mats[prod]
    assert len({tuple(M) for M in mats.values()})==8
    assert qj*s.conjugate(qj)==-I2
    ar,ai,br,bi=s.symbols('ar ai br bi',real=True);psi=s.Matrix([ar+s.I*ai,br+s.I*bi])
    T=lambda x:qj*s.conjugate(x)
    assert mat_eq(T(T(psi)),-psi)
    assert zero((s.conjugate(psi).T*T(psi))[0])
    return {'Q8_native_table_cases':64,'faithful_matrix_count':8,
            'time_reversal_square':-1,'time_reversal_orthogonality':True}

def torus_checks():
    t=s.symbols('t',nonzero=True,real=True)
    a=s.symbols('a0:8',real=True);b=s.symbols('b0:8',real=True)
    X,Y=uncoords(a),uncoords(b)
    def torus(X):
        a,b,x,y=X
        return zorn(a,b,[t*x[0],x[1]/t,x[2]],[y[0]/t,t*y[1],y[2]])
    assert mat_eq(zcoords(torus(zm(X,Y))),zcoords(zm(torus(X),torus(Y))))
    return {'full_symbolic_Zorn_torus_multiplicativity':True}

def main():
    result={'affine':affine_checks(),'spin':spin_checks(),'zorn_exterior':zorn_exterior_checks(),
            'quaternion':quaternion_checks(),'torus':torus_checks(),
            'all_checks_passed':True,'Lean_kernel_executed':False,
            'method':'Exact SymPy polynomial arithmetic, free associative words, and finite matrices',
            'limitation':'Independent regressions are not Lean elaboration or a transitive axiom audit.'}
    out=ROOT/'reports/spin_affine_exterior/exact-regressions.json';out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
