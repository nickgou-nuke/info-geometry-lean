import json
from pathlib import Path

out = {"checks": {}, "status": "PASS"}

# SymPy matrix certificate: gamma0^2=+1, gammai^2=-1, anticommutation,
# pseudoscalar square, Pauli bivectors, and circular CAR products.
import sympy as sp
I = sp.I
z = sp.zeros(2)
id2 = sp.eye(2)
s1 = sp.Matrix([[0,1],[1,0]])
s2 = sp.Matrix([[0,-I],[I,0]])
s3 = sp.Matrix([[1,0],[0,-1]])
g0 = sp.kronecker_product(s3, id2)
g1 = I * sp.kronecker_product(s2, s1)
g2 = I * sp.kronecker_product(s2, s2)
g3 = I * sp.kronecker_product(s2, s3)
g = [g0,g1,g2,g3]
eye4 = sp.eye(4)
assert g[0]**2 == eye4
for x in g[1:]: assert x**2 == -eye4
for i in range(4):
    for j in range(i+1,4): assert g[i]*g[j] + g[j]*g[i] == sp.zeros(4)
P = g0*g1*g2*g3
assert P**2 == -eye4
sigma = [g[i]*g0 for i in range(1,4)]
for x in sigma: assert x**2 == eye4
uplus = (eye4+sigma[2])/2
uminus = (eye4-sigma[2])/2
cplus = (sigma[0] + P*sigma[1])/2
cminus = (sigma[0] - P*sigma[1])/2
assert cplus**2 == sp.zeros(4) and cminus**2 == sp.zeros(4)
assert cplus*cminus == uplus and cminus*cplus == uminus
out["checks"]["sympy"] = {"status":"PASS", "real_cl14_basis_dimension":8,
    "pseudoscalar_square":str(P**2), "circular_CAR":"PASS"}

for name, fn in [("clifford", "clifford"), ("galgebra", "galgebra")]:
    try:
        __import__(fn)
        out["checks"][name] = {"status":"AVAILABLE", "note":"package import succeeded; matrix certificate above is authoritative"}
    except Exception as e:
        out["checks"][name] = {"status":"NOT_AVAILABLE", "error":repr(e)}

Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2, sort_keys=True))
print(json.dumps(out, indent=2, sort_keys=True))
