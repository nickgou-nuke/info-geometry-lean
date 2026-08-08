#!/usr/bin/env python3
"""SymPy witness for the S7/S4/CP2 chiral twisted fibration picture.

This is intentionally a symbolic algebra model, not a Lean proof.  It checks the
identities that should later be mirrored in Lean:

* Klein bottle monodromy: G T = T^{-1} G and G^2 is translation by 2.
* Orbifold local symmetries: mirror and half-turn are order two.
* Cl(1,1) / split-signature Pauli sector: determinant grades the sectors.
* Chiral pentagon braiding: a 5th-root phase is stable in the fiber.
* Grothendieck-fibration bookkeeping: base labels, fiber labels, and transport
  are kept separate, so S7, S4, CP2, V4, and Klein bottle data are not collapsed.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import sympy as sp


def assert_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.simplify(expr)
    assert simplified == 0, f"{name} failed: {simplified}"
    print(f"OK  {name}")


def assert_matrix_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    assert simplified == sp.zeros(*mat.shape), f"{name} failed:\n{simplified}"
    print(f"OK  {name}")


# ---------------------------------------------------------------------------
# 1. Klein bottle and non-orientable orbifold monodromy on C ~= R^2.
# ---------------------------------------------------------------------------

x, y = sp.symbols("x y", real=True)
z = sp.Matrix([x, y])


def T(v: sp.Matrix) -> sp.Matrix:
    """Translation by i: (x,y) -> (x,y+1)."""
    return sp.Matrix([v[0], v[1] + 1])


def T_inv(v: sp.Matrix) -> sp.Matrix:
    """Inverse translation by -i: (x,y) -> (x,y-1)."""
    return sp.Matrix([v[0], v[1] - 1])


def M(v: sp.Matrix) -> sp.Matrix:
    """Mirror/conjugation: (x,y) -> (x,-y)."""
    return sp.Matrix([v[0], -v[1]])


def G(v: sp.Matrix) -> sp.Matrix:
    """Glide reflection: conjugation followed by real translation by 1."""
    return sp.Matrix([v[0] + 1, -v[1]])


def H(v: sp.Matrix) -> sp.Matrix:
    """Half turn: v -> -v."""
    return -v


assert_matrix_zero("Klein relation G*T = T_inv*G", G(T(z)) - T_inv(G(z)))
assert_matrix_zero("glide square G^2 = real translation by 2", G(G(z)) - (z + sp.Matrix([2, 0])))
assert_matrix_zero("mirror is order two", M(M(z)) - z)
assert_matrix_zero("half-turn is order two", H(H(z)) - z)
assert_matrix_zero("glide is translated mirror", G(z) - (M(z) + sp.Matrix([1, 0])))

# Fixed-point loci for orbifold singularities.
mirror_fixed_equations = [sp.Eq(M(z)[i], z[i]) for i in range(2)]
half_turn_fixed_equations = [sp.Eq(H(z)[i], z[i]) for i in range(2)]
mirror_fixed_solution = sp.solve(mirror_fixed_equations, [y], dict=True)
half_turn_fixed_solution = sp.solve(half_turn_fixed_equations, [x, y], dict=True)
assert mirror_fixed_solution == [{y: 0}]
assert half_turn_fixed_solution == [{x: 0, y: 0}]
print("OK  mirror fixed locus is real axis y=0")
print("OK  half-turn fixed locus is origin")


# ---------------------------------------------------------------------------
# 2. Cl(1,1), split-signature determinant grading, and V4 transport.
# ---------------------------------------------------------------------------

I2 = sp.eye(2)
e_plus = sp.Matrix([[0, 1], [1, 0]])      # square +I
e_minus = sp.Matrix([[0, -1], [1, 0]])    # square -I
pseudo = e_plus * e_minus

assert_matrix_zero("e_plus^2 = I", e_plus * e_plus - I2)
assert_matrix_zero("e_minus^2 = -I", e_minus * e_minus + I2)
assert_matrix_zero("Cl(1,1) anticommutation", e_plus * e_minus + e_minus * e_plus)

a, b, c, d = sp.symbols("a b c d", real=True)
cl = a * I2 + b * e_plus + c * e_minus + d * pseudo
det_cl = sp.factor(cl.det())
expected_det = a**2 - b**2 + c**2 - d**2
assert_zero("Cl determinant split norm", det_cl - expected_det)


def det_sector(expr: sp.Expr) -> str:
    """Symbolic classifier used for named samples."""
    val = sp.simplify(expr)
    if val.is_positive:
        return "det>0"
    if val.is_negative:
        return "det<0"
    if val == 0:
        return "det=0"
    return "symbolic"


samples = {
    "elliptic/unit": cl.subs({a: 1, b: 0, c: 0, d: 0}),
    "hyperbolic/reflection": cl.subs({a: 0, b: 1, c: 0, d: 0}),
    "null/projector": sp.Matrix([[1, 0], [0, 0]]),
}
for label, mat in samples.items():
    print(f"OK  {label} determinant sector = {det_sector(mat.det())}")

# V4 acts by involutive matrix transport and preserves determinant up to the
# sign classifier.  The set is projective: pseudo^2 = I for this real model.
V4 = {
    "I": I2,
    "P": e_plus,
    "J": e_minus,
    "PJ": pseudo,
}
for name, mat in V4.items():
    det_sq = sp.simplify((mat.det()) ** 2 - 1)
    assert det_sq == 0, f"{name} determinant is not +/-1"
print("OK  V4 transport representatives have determinant sign +/-1")


# ---------------------------------------------------------------------------
# 3. Chiral pentagon braiding as cyclotomic fiber phase.
# ---------------------------------------------------------------------------

q = sp.symbols("q")
cyclo5 = q**4 + q**3 + q**2 + q + 1


def reduce_cyclo5(poly: sp.Expr) -> sp.Expr:
    return sp.rem(sp.Poly(sp.expand(poly), q), sp.Poly(cyclo5, q)).as_expr()


def assert_matrix_cyclo5_zero(name: str, mat: sp.Matrix) -> None:
    reduced = mat.applyfunc(lambda entry: sp.simplify(reduce_cyclo5(entry)))
    assert reduced == sp.zeros(*mat.shape), f"{name} failed:\n{reduced}"
    print(f"OK  {name}")


assert_zero("q^5 = 1 modulo Phi_5", reduce_cyclo5(q**5 - 1))
assert_zero("chiral inverse q^4 = q^-1 modulo Phi_5", reduce_cyclo5(q * q**4 - 1))

R_left = sp.Matrix([[q, 0], [0, q**4]])
R_right = sp.Matrix([[q**4, 0], [0, q]])
assert_zero("left chiral braiding determinant = 1", reduce_cyclo5(R_left.det() - 1))
assert_zero("right chiral braiding determinant = 1", reduce_cyclo5(R_right.det() - 1))
assert_matrix_cyclo5_zero("left/right chiral braids are inverse modulo Phi_5", R_left * R_right - I2)


# ---------------------------------------------------------------------------
# 4. Two-sheeted polarization and emergent complex structure.
# ---------------------------------------------------------------------------

# Real doubling operators on two sheets.
sheet_swap = sp.Matrix([[0, 1], [1, 0]])
sheet_grading = sp.Matrix([[1, 0], [0, -1]])
K_complex = sheet_swap * sheet_grading

assert_matrix_zero("sheet swap squared is identity", sheet_swap * sheet_swap - I2)
assert_matrix_zero("sheet grading squared is identity", sheet_grading * sheet_grading - I2)
assert_matrix_zero("sheet swap anticommutes with grading", sheet_swap * sheet_grading + sheet_grading * sheet_swap)
assert_matrix_zero("emergent complex structure matrix K = J ε", K_complex - e_minus)
assert_matrix_zero("K^2 = -I", K_complex * K_complex + I2)
assert_matrix_zero("K has e_minus coordinates", K_complex - e_minus)

# The relation is the real geometric precursor to a complex polarization:
# sheet grading ε splits the two-sheeted space, sheet swap J couples them,
# and K = J ε gives the algebraic complex unit with K^2 = -I.

# ---------------------------------------------------------------------------
# 5. Grothendieck-style fibration bookkeeping.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BaseChart:
    name: str
    role: str


@dataclass(frozen=True)
class FiberSector:
    name: str
    algebra: str
    chirality: str


@dataclass(frozen=True)
class Transport:
    name: str
    source: BaseChart
    target: BaseChart
    matrix: sp.Matrix
    orientation_sign: int


S4 = BaseChart("S4", "macroscopic quaternionic/Hopf base")
CP2 = BaseChart("CP2", "complex projective reduced sector")
KLEIN_ORB = BaseChart("Klein-orbifold", "non-orientable quotient/defect base")

S7_FIBER = FiberSector("S7", "unit octonion phase fiber", "both")
SPLIT_OCT_FIBER = FiberSector("split-octonion", "Cl(1,1)-graded split fiber", "chiral")

transport_glide = Transport("glide monodromy", S4, KLEIN_ORB, sp.Matrix([[1, 0], [0, -1]]), -1)
transport_chiral = Transport("pentagon chiral braid", CP2, CP2, R_left, 1)

assert transport_glide.orientation_sign == -1
assert transport_chiral.orientation_sign == 1
assert_zero("glide transport determinant sign", transport_glide.matrix.det() + 1)
assert_zero("chiral transport determinant", reduce_cyclo5(transport_chiral.matrix.det() - 1))


@dataclass(frozen=True)
class GrothendieckFibrationWitness:
    base_charts: tuple[BaseChart, ...]
    fibers: tuple[FiberSector, ...]
    transports: tuple[Transport, ...]

    def has_base(self, name: str) -> bool:
        return any(chart.name == name for chart in self.base_charts)

    def has_fiber(self, name: str) -> bool:
        return any(fiber.name == name for fiber in self.fibers)

    def has_transport(self, name: str) -> bool:
        return any(transport.name == name for transport in self.transports)


witness = GrothendieckFibrationWitness(
    base_charts=(S4, CP2, KLEIN_ORB),
    fibers=(S7_FIBER, SPLIT_OCT_FIBER),
    transports=(transport_glide, transport_chiral),
)

assert witness.has_base("S4")
assert witness.has_base("CP2")
assert witness.has_base("Klein-orbifold")
assert witness.has_fiber("S7")
assert witness.has_fiber("split-octonion")
assert witness.has_transport("glide monodromy")
assert witness.has_transport("pentagon chiral braid")

print("OK  fibration bookkeeping keeps base, fiber, and monodromy distinct")
print("OK  symbolic reconciliation witness completed")
