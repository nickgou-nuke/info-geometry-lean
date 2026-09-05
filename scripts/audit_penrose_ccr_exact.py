#!/usr/bin/env python3
"""Independent exact regressions for the Penrose CCR reconstruction.

These checks are not Lean elaboration and do not inspect Lean proof dependencies.
All expressions below use exact symbolic arithmetic; no numeric tolerances.
"""
from __future__ import annotations
import itertools
import json
import re
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]

def zero(expr):
    return s.expand(expr) == 0

def veq(a, b):
    return all(zero(x-y) for x,y in zip(a,b))

def signed_geometry():
    eps=s.diag(1,1,-1,-1)
    def herm(x,y): return (s.conjugate(x).T*eps*y)[0]
    def metric(x,y): return s.expand(2*s.re(herm(x,y)))
    def symp(x,y): return s.expand(2*s.im(herm(x,y)))
    def norm(x): return s.expand(s.re(herm(x,x)))
    def pair(x): return (x,eps*s.conjugate(x))
    def omega(A,B): return s.expand((A[0].T*B[1]-A[1].T*B[0])[0])
    def triple(x,y,z): return symp(y,z)*x+symp(z,x)*y+symp(x,y)*z
    def symvec(name):
        a=s.symbols(name+'r0:4',real=True); b=s.symbols(name+'i0:4',real=True)
        return s.Matrix([a[i]+s.I*b[i] for i in range(4)])
    x,y,z=[symvec(n) for n in 'xyz']
    assert zero(s.I*omega(pair(x),pair(y))-symp(x,y))
    assert zero(s.I*omega(pair(x),pair(s.I*y))-metric(x,y))
    assert zero(metric(s.I*x,s.I*y)-metric(x,y))
    assert zero(symp(x,y)+symp(y,x))
    actual=s.I*(omega(pair(y),pair(z))*x+omega(pair(z),pair(x))*y+omega(pair(x),pair(y))*z)
    assert veq(actual,triple(x,y,z))
    actualdn=s.I*(omega(pair(y),pair(z))*pair(x)[1]+omega(pair(z),pair(x))*pair(y)[1]+omega(pair(x),pair(y))*pair(z)[1])
    assert veq(actualdn,pair(triple(x,y,z))[1])
    E,X,Y=(s.eye(4).col(i) for i in range(3))
    cross=lambda a,b:triple(s.I*a,s.I*b,s.I*E)
    scalar=lambda a:metric(a,E)/2
    vector=lambda a:a-scalar(a)*E
    def candidate(k,a,b):
        u,v=vector(a),vector(b)
        return s.simplify((scalar(a)*scalar(b)-k*metric(u,v))*E+scalar(a)*v+scalar(b)*u+cross(u,v))
    k=s.symbols('k',real=True)
    assert metric(E,E)==2 and metric(X,X)==2 and metric(Y,Y)==-2
    assert veq(cross(X,Y),s.zeros(4,1))
    assert veq(candidate(k,X,Y),s.zeros(4,1))
    assert veq(candidate(k,X,X),-2*k*E)
    assert veq(candidate(k,X,candidate(k,X,Y)),s.zeros(4,1))
    assert veq(candidate(k,candidate(k,X,X),Y),-2*k*Y)
    assert norm(candidate(k,X,Y))==0 and norm(X)*norm(Y)==-1
    return {'signed_pairing':True,'signed_triple_closure':True,
            'candidate_alternativity_left':'0','candidate_alternativity_right':'-2*k*testY',
            'candidate_product_norm':0,'product_of_input_norms':-1}

def polynomial_ccr():
    q=s.symbols('q0:4'); h=s.symbols('h')
    f=s.Function('f')(*q)
    def Q(A,p):
        return sum(A[0][i]*q[i] for i in range(4))*p-h*sum(A[1][i]*s.diff(p,q[i]) for i in range(4))
    A,B,C=[(s.symbols(n+'a0:4'),s.symbols(n+'b0:4')) for n in 'ABC']
    om=lambda a,b:sum(a[0][i]*b[1][i]-a[1][i]*b[0][i] for i in range(4))
    assert zero(Q(A,Q(B,f))-Q(B,Q(A,f))-h*om(A,B)*f)
    triples=[A,B,C]
    lhs=0
    for p in itertools.permutations(range(3)):
        inv=sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
        lhs += (-1)**inv*Q(triples[p[0]],Q(triples[p[1]],Q(triples[p[2]],f)))
    rhs=h*(om(B,C)*Q(A,f)+om(C,A)*Q(B,f)+om(A,B)*Q(C,f))
    assert zero(lhs-rhs)
    return {'arbitrary_coefficient_commutator':True,'six_term_operator_triple':True,
            'test_function':'generic smooth symbolic f(q0,q1,q2,q3), not a truncated polynomial space'}

def legacy_regression():
    E=s.eye(4).col(0);X=s.eye(4).col(1);Y=s.eye(4).col(2)
    e=(E,E);x=(X,X);y=(Y,Y)
    def dot(A,B):return s.expand(2*s.re((s.conjugate(A[0]).T*B[0])[0]))
    def phase(A):return (s.I*A[0],-s.I*A[1])
    def triple(A,B,C):
        def br(a,b,c,slot):
            return (a[0].T*c[1])[0]*b[slot]-(b[0].T*c[1])[0]*a[slot]
        return (-s.I*(br(A,B,C,0)+br(B,C,A,0)+br(C,A,B,0)),
                 s.I*(br(A,B,C,1)+br(B,C,A,1)+br(C,A,B,1)))
    def product(A,B):
        a=dot(A,e)/2;b=dot(B,e)/2
        u=tuple(A[j]-a*e[j] for j in (0,1));v=tuple(B[j]-b*e[j] for j in (0,1))
        cross=triple(phase(u),phase(v),phase(e))
        return tuple(s.simplify((a*b-dot(u,v)/2)*e[j]+a*v[j]+b*u[j]+cross[j]) for j in (0,1))
    left=product(x,product(x,y));right=product(product(x,x),y)
    assert veq(left[0],s.zeros(4,1)) and veq(right[0],-Y)
    assert dot(y,y)==2
    return {'exact_historical_product_left_up2':0,'exact_historical_product_right_up2':-1,
            'historical_dot_Y_Y':2}

def zorn_completion():
    def Z(a,b,x,y):return (a,b,s.Matrix(x),s.Matrix(y))
    def coords(z):return [z[0],z[1],*z[2],*z[3]]
    def mult(A,B):
        a,b,x,y=A;c,d,u,v=B
        return Z(a*c+x.dot(v),b*d+y.dot(u),a*u+d*x-y.cross(v),b*v+c*y+x.cross(u))
    def n(A):return s.expand(A[0]*A[1]-A[2].dot(A[3]))
    def equal(A,B):return veq(coords(A),coords(B))
    def symz(name):
        vals=s.symbols(name+'0:8',real=True)
        return Z(vals[0],vals[1],vals[2:5],vals[5:8])
    A,B=symz('A'),symz('B')
    assert zero(n(mult(A,B))-n(A)*n(B))
    assert equal(mult(mult(A,A),B),mult(A,mult(A,B)))
    assert equal(mult(mult(B,A),A),mult(B,mult(A,A)))
    def witt(v):
        p=[s.re(v[0]),s.im(v[0]),s.re(v[1]),s.im(v[1])]
        m=[s.re(v[2]),s.im(v[2]),s.re(v[3]),s.im(v[3])]
        c=[p[i]+m[i] for i in range(4)]+[p[0]-m[0]]+[m[i]-p[i] for i in range(1,4)]
        return Z(c[0],c[4],c[1:4],c[5:8])
    def iwitt(A):
        a,b,x,y=A
        return s.Matrix([(a+b)/2+s.I*(x[0]-y[0])/2,
                         (x[1]-y[1])/2+s.I*(x[2]-y[2])/2,
                         (a-b)/2+s.I*(x[0]+y[0])/2,
                         (x[1]+y[1])/2+s.I*(x[2]+y[2])/2])
    assert equal(witt(iwitt(A)),A)
    E,X,Y=(s.eye(4).col(i) for i in range(3))
    assert equal(witt(E),Z(1,1,[0,0,0],[0,0,0]))
    xy=iwitt(mult(witt(X),witt(Y)))
    assert veq(xy,-s.eye(4).col(3))
    assert n(mult(witt(X),witt(Y)))==-1
    return {'native_zorn_composition':True,'native_left_alternativity':True,
            'native_right_alternativity':True,'explicit_witt_inverse':True,
            'witt_unit':True,'selected_product_XY':'-e3','selected_product_XY_norm':-1}

def strip_lean_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;i+=2
            elif text.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i):depth=1;i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i);i=len(text) if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
            out.append(' ')
        else:out.append(text[i]);i+=1
    if depth: raise ValueError('Unclosed Lean block comment')
    return ''.join(out)

def source_scan():
    names=['PenrosePolynomialCCR','PenroseSignedCCRGeometry','PenroseLiteralCrossObstruction',
           'PenroseWittCompositionCompletion','PenroseLegacyProductAudit',
           'PenroseCCRPristineChain','PenroseCCRAudit']
    files=[ROOT/'lean/InfoGeometry/Twistor'/f'{name}.lean' for name in names]
    forbidden=[]
    for p in files:
        for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide|sorryAx)\b',strip_lean_comments(p.read_text())):
            forbidden.append({'path':str(p.relative_to(ROOT)),'token':m.group()})
    assert not forbidden,forbidden
    return {'lean_files':len(files),'new_source_forbidden_tokens':forbidden,
            'transitive_dependencies_scanned':False}

def main():
    result={'polynomial':polynomial_ccr(),'real_geometry':signed_geometry(),
            'legacy':legacy_regression(),'completion':zorn_completion(),'source_scan':source_scan(),
            'lean_kernel_executed':False,'method':'Exact independent SymPy symbolic identities'}
    p=ROOT/'reports/penrose_ccr/exact-regressions.json';p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
