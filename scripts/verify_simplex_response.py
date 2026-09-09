#!/usr/bin/env python3
"""Exact scalar CAS checks for the simplex-response extension.

Carrier: real scalars; coordinates (C, B, X, p, v, pi), ordinary commutative
multiplication. Nonzero denominators are explicit Lean hypotheses; the open
simplex supplies p > 0 and 1-p > 0. No detector or quantum dynamics assumed.
Prints deterministic JSON to stdout; this is navigation, not kernel evidence.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

C, B, X, p, v, pi, scale = s.symbols('C B X p v pi scale', nonzero=True)
I = C*X-B*X**2
g = 1/(p**2*(1-p)**2)
gamma = (2*p-1)/(p*(1-p))
velocity = 2*v*p*(1-p)
H = p**2*(1-p)**2*pi**2/2
checks = {
    'simplex': I.subs(X, C*p/B)-C**2/B*p*(1-p),
    'completion': I-(C**2/(4*B)-B*(X-C/(2*B))**2),
    'rescale': I.subs({C:C/scale, B:B/scale**2, X:scale*X}, simultaneous=True)-I,
    'homogeneity': X*s.diff(I,X)-I+B*X**2,
    'connection': s.diff(g,p)/(2*g)-gamma,
    'geodesic': s.diff(velocity,p)*velocity+gamma*velocity**2,
    'energy': H.subs(pi,2*v/(p*(1-p)))-2*v**2,
    'hamilton_p': s.diff(H,pi).subs(pi,2*v/(p*(1-p)))-velocity,
    'hamilton_pi': s.diff(2*v/(p*(1-p)),p)*velocity+s.diff(H,p).subs(pi,2*v/(p*(1-p))),
    'fisher_pullback': (1/(p*(1-p)))*velocity**2-4*v**2*p*(1-p),
    'barrier_hessian': s.diff(-s.log(p)-s.log(1-p),p,2)-(g-2/(p*(1-p))),
    'third_centered_moment': p*(1-p)**3+(1-p)*(-p)**3-p*(1-p)*(1-2*p),
    'fourth_cumulant': p*(1-p)**4+(1-p)*p**4-3*(p*(1-p))**2-p*(1-p)*(1-6*p*(1-p)),
    'aitchison_speed': (s.diff(s.log(p/(1-p))/2,p))**2+
        (s.diff(-s.log(p/(1-p))/2,p))**2-g/2,
}
results = {name: str(s.factor(value)) for name,value in checks.items()}
assert all(value == '0' for value in results.values()), results
forward = (C/scale, B/scale**2, scale*X)
roundtrip = (forward[0]*scale, forward[1]*scale**2, forward[2]/scale)
roundtrip_ok = all(s.simplify(a-b) == 0 for a,b in zip(roundtrip,(C,B,X)))
assert roundtrip_ok
print(json.dumps({'object':'binary_simplex_response', 'ring':'Real',
    'basis':['C','B','X','p','v','pi','scale'],
    'nonzero':['C','B','p','1-p','scale'],
    'checked_residuals':results,
    'round_trip_verified':roundtrip_ok,
    'round_trip_scope':'CAS inverse coordinate rescaling only; Lean kernel audit is separate',
    'sympy_source':'scripts/verify_simplex_response.py',
    'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
    sort_keys=True, indent=2))
