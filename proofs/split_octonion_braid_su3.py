"""SymPy witness: split-octonion zero divisors and B3 -> S3 color permutations.

Computational layer for the topological strong-interaction deferred_interface:
- Artin braid generators project to adjacent transpositions in S3;
- the braid relation s1 s2 s1 = s2 s1 s2 holds after projection;
- S3 acts by permuting three color labels (Weyl-group deferred_interface for SU(3));
- split-octonion (4,4) norm has nonzero null vectors;
- Zorn split-octonion model contains nonzero nilpotents N^2=0;
- tripotent scale polynomial retains zero-mode pole s=0.
"""

import sympy as sp

print("§1  B3 projection to S3")
# permutations as tuples p where p[i] is image of i; compose p after q.
def compose(p, q):
    return tuple(p[i] for i in q)

s1 = (1, 0, 2)  # swap colors 0,1
s2 = (0, 2, 1)  # swap colors 1,2
lhs = compose(s1, compose(s2, s1))
rhs = compose(s2, compose(s1, s2))
assert lhs == rhs == (2, 1, 0)
assert compose(s1, s1) == (0, 1, 2)
assert compose(s2, s2) == (0, 1, 2)
colors = ["red", "green", "blue"]
assert [colors[i] for i in lhs] == ["blue", "green", "red"]
print("   braid relation projects to S3 color permutation ✓")

print("§2  Split signature (4,4) null cone")
x = sp.symbols("x0:8")
split_norm = sum(x[i]**2 for i in range(4)) - sum(x[i]**2 for i in range(4, 8))
null_vec = {x[0]: 1, x[1]: 0, x[2]: 0, x[3]: 0, x[4]: 1, x[5]: 0, x[6]: 0, x[7]: 0}
assert split_norm.subs(null_vec) == 0
assert any(v != 0 for v in null_vec.values())
print("   nonzero vector on split-octonion null cone has norm 0 ✓")

print("§3  Zorn split-octonion nilpotent")
def dot(u, v):
    return sum(ui*vi for ui, vi in zip(u, v))

def cross(u, v):
    return [u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0]]

def zorn_mul(X, Y):
    a, u, v, b = X
    c, xvec, yvec, d = Y
    return (
        sp.simplify(a*c + dot(u, yvec)),
        [sp.simplify(a*xvec[i] + d*u[i] - cross(v, yvec)[i]) for i in range(3)],
        [sp.simplify(c*v[i] + b*yvec[i] + cross(u, xvec)[i]) for i in range(3)],
        sp.simplify(dot(v, xvec) + b*d),
    )

N = (0, [1, 0, 0], [0, 0, 0], 0)
zero = (0, [0, 0, 0], [0, 0, 0], 0)
assert zorn_mul(N, N) == zero
assert N != zero
print("   nonzero Zorn split-octonion N satisfies N²=0 ✓")

print("§4  Tripotent zero-mode pole")
s = sp.symbols("s")
T = sp.diag(1, -1, 0)
det_trip = sp.factor((s*sp.eye(3)-T).det())
assert det_trip == s*(s-1)*(s+1)
assert det_trip.subs(s, 0) == 0
print("   tripotent determinant has zero-mode pole s=0 ✓")

print()
print("split_octonion_braid_su3.py: All identities verified")
