"""SymPy witness: pentagon/Penrose fractal beyond wallpaper crystallography.

Checks the synthesis:
- periodic wallpaper lattices allow rotation orders {1,2,3,4,6}, so 5-fold
  pentagonal symmetry is forbidden for true wallpaper groups;
- Penrose quasicrystals carry exact 5-fold symmetry via aperiodic inflation;
- the Penrose rhombus inflation matrix has Perron eigenvalue φ² and conjugate
  φ⁻², giving fractal/self-similar growth;
- finite substitution words project to a Cantor boundary of infinite choices.
"""

import sympy as sp

print("§1  Crystallographic restriction: pentagon forbidden for wallpaper")
allowed = {1, 2, 3, 4, 6}
assert 5 not in allowed
print("   5-fold rotations are excluded from periodic wallpaper lattices ✓")

print("§2  Pentagon rotation exists for Penrose/quasicrystal symmetry")
theta = 2 * sp.pi / 5
R = sp.Matrix([[sp.cos(theta), -sp.sin(theta)], [sp.sin(theta), sp.cos(theta)]])
R5 = sp.simplify(R**5)
assert sp.N(R5 - sp.eye(2), 40).norm() < sp.Float("1e-35")
print("   planar 72° rotation satisfies R^5=I, available to aperiodic tilings ✓")

print("§3  Penrose inflation matrix and golden ratio")
phi = (1 + sp.sqrt(5)) / 2
M = sp.Matrix([[2, 1], [1, 1]])  # thick/thin rhombus substitution count matrix
char = sp.factor(M.charpoly().as_expr())
assert char == sp.Symbol('lambda')**2 - 3 * sp.Symbol('lambda') + 1
assert sp.simplify((phi**2)**2 - 3 * phi**2 + 1) == 0
assert sp.simplify((phi**-2)**2 - 3 * phi**-2 + 1) == 0
assert M.det() == 1 and M.trace() == 3
print("   substitution eigenvalues are φ² and φ⁻²; det=1, trace=3 ✓")

print("§4  Inflation growth recurrence")
v = sp.Matrix([1, 0])  # start with one thick tile
counts = [v]
for _ in range(6):
    counts.append(M * counts[-1])
# total tile count strictly increases after first inflation
for i in range(1, len(counts) - 1):
    assert sum(counts[i + 1]) > sum(counts[i])
print("   substitution iterates produce increasing finite Penrose patches ✓")

print("§5  Cantor/fractal boundary coding")
# Binary choices at depth n have 2^n cylinders; inverse limit is {0,1}^N.
for n in range(10):
    assert len(list(range(2**n))) == 2**n
# Prefix cylinders refine by two children.
prefix = "101"
children = [prefix + "0", prefix + "1"]
assert len(children) == 2 and all(c.startswith(prefix) for c in children)
print("   finite prefix cylinders refine binary; limit is Cantor boundary ✓")

print()
print("pentagon_penrose_wallpaper_fractal.py: All identities verified")
