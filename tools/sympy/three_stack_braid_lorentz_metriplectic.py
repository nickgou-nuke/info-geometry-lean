#!/usr/bin/env python3
"""
Finite three-stack validator for braid / Lorentz / metriplectic digest claims.

The script checks a deliberately small theorem-safe packet:
  * SymPy: rational 1+1 Lorentz boost preserves diag(-1,1); S4 permutation
    shadows satisfy adjacent/distant braid relations; central +/-I is preserved;
    J is skew with J^2=-I and G=I is symmetric.
  * Sage: same rational Lorentz and permutation checks.
  * GAP: Artin action B4 -> End(F4) satisfies braid relations on generators;
    no faithfulness theorem is claimed.
  * clifford/galgebra: split Cl(1,1) signs and pseudoscalar square.

Negative scope: no SO^+(1,3) theorem, no faithful B4 -> Aut(F4) proof,
no Mac Lane hexagon theorem, no anomaly-free TQFT, no super-Kahler or
metriplectic thermodynamics theorem.
"""

from __future__ import annotations

import json
import shutil
import subprocess
from fractions import Fraction

import sympy as sp

SAGE = shutil.which("sage") or "/home/goutev/miniforge3/envs/sage/bin/sage"
GAP = shutil.which("gap") or "/home/goutev/miniforge3/envs/sage/bin/gap"


def assert_zero(M: sp.Matrix, label: str) -> None:
    if M != sp.zeros(*M.shape):
        raise AssertionError(f"{label} not zero: {M}")


def perm_matrix(p: tuple[int, ...]) -> sp.Matrix:
    n = len(p)
    M = sp.zeros(n)
    for i, pi in enumerate(p):
        M[pi, i] = 1
    return M


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """p after q."""
    return tuple(p[q[i]] for i in range(len(p)))


def verify_sympy() -> dict[str, bool]:
    # Exact rational 1+1 Lorentz boost with c^2-s^2=1.
    c = sp.Rational(5, 4)
    s = sp.Rational(3, 4)
    eta = sp.diag(-1, 1)
    boost = sp.Matrix([[c, s], [s, c]])
    assert_zero(boost.T * eta * boost - eta, "rational Lorentz boost metric preservation")

    # Central sign preservation by conjugation.
    I2 = sp.eye(2)
    assert boost * I2 * boost.inv() == I2
    assert boost * (-I2) * boost.inv() == -I2

    # B4 permutation shadow: adjacent Artin and distant commutativity.
    s1 = (1, 0, 2, 3)
    s2 = (0, 2, 1, 3)
    s3 = (0, 1, 3, 2)
    assert compose(compose(s1, s2), s1) == compose(compose(s2, s1), s2)
    assert compose(s1, s3) == compose(s3, s1)
    P1, P2, P3 = map(perm_matrix, (s1, s2, s3))
    assert_zero(P1 * P2 * P1 - P2 * P1 * P2, "matrix Artin relation")
    assert_zero(P1 * P3 - P3 * P1, "matrix distant commutativity")

    # Finite metriplectic split: skew J, symmetric G, central signs stable.
    J = sp.Matrix([[0, 1], [-1, 0]])
    G = sp.eye(2)
    assert_zero(J + J.T, "J skew")
    assert_zero(J * J + I2, "J^2 + I")
    assert_zero(G - G.T, "G symmetric")

    return {
        "rational_boost_preserves_minkowski_metric": True,
        "central_signs_preserved_by_boost_conjugation": True,
        "s4_adjacent_artin_relation": True,
        "s4_distant_commutativity": True,
        "finite_metriplectic_split_J_skew_G_symmetric": True,
    }


def run_sage() -> dict[str, object]:
    script = r'''
M2 = MatrixSpace(QQ, 2)
eta = M2([[-1,0],[0,1]])
B = M2([[QQ(5)/4, QQ(3)/4], [QQ(3)/4, QQ(5)/4]])
assert B.transpose()*eta*B == eta
assert B*M2.identity_matrix()*B.inverse() == M2.identity_matrix()
assert B*(-M2.identity_matrix())*B.inverse() == -M2.identity_matrix()
S4 = SymmetricGroup(4)
s1 = S4((1,2)); s2 = S4((2,3)); s3 = S4((3,4))
assert s1*s2*s1 == s2*s1*s2
assert s1*s3 == s3*s1
print("SAGE_THREE_STACK_FINITE_OK")
'''
    proc = subprocess.run([SAGE, "-c", script], text=True, capture_output=True, check=True)
    assert "SAGE_THREE_STACK_FINITE_OK" in proc.stdout
    return {"sage_ok": True, "stdout": proc.stdout.strip()}


def run_gap() -> dict[str, object]:
    script = r'''
F := FreeGroup("x1", "x2", "x3", "x4");;
gens := GeneratorsOfGroup(F);;
Beta := function(i, w)
  local imgs, hom;
  imgs := ShallowCopy(gens);
  imgs[i] := gens[i] * gens[i+1] * gens[i]^-1;
  imgs[i+1] := gens[i];
  hom := GroupHomomorphismByImages(F, F, gens, imgs);
  return Image(hom, w);
end;;
ApplyWord := function(word, w)
  local out, i;
  out := w;
  for i in Reversed(word) do
    out := Beta(i, out);
  od;
  return out;
end;;
RequireTrue := function(label, cond)
  if not cond then Error(label); fi;
end;;
for x in gens do
  RequireTrue("B4 adjacent Artin action on F4 generator", ApplyWord([1,2,1], x) = ApplyWord([2,1,2], x));
  RequireTrue("B4 distant action on F4 generator", ApplyWord([1,3], x) = ApplyWord([3,1], x));
od;
Z2 := CyclicGroup(2);;
RequireTrue("central Z2 order", Size(Z2)=2);
Print("GAP_THREE_STACK_FINITE_OK\n");
'''
    proc = subprocess.run([GAP, "-q"], input=script, text=True, capture_output=True, check=True)
    assert "GAP_THREE_STACK_FINITE_OK" in proc.stdout
    return {"gap_ok": True, "stdout": proc.stdout.strip()}


def verify_clifford() -> dict[str, object]:
    import clifford  # type: ignore

    layout, blades = clifford.Cl(1, 1, firstIdx=1)
    e1, e2 = blades["e1"], blades["e2"]
    ps = e1 * e2
    assert (e1 * e1)[()] == 1
    assert (e2 * e2)[()] == -1
    assert e1 * e2 + e2 * e1 == 0
    assert (ps * ps)[()] == 1
    return {"clifford_ok": True, "dims": layout.dims}


def verify_galgebra() -> dict[str, bool]:
    from galgebra.ga import Ga  # type: ignore

    ga = Ga("e f", g=[1, -1])
    e, f = ga.mv()
    ps = e * f
    assert str(e * e) == "1"
    assert str(f * f) == "-1"
    assert str(e * f + f * e) == "0"
    assert str(ps * ps) == "1"
    return {"galgebra_ok": True}


def main() -> None:
    result = {
        "sympy": verify_sympy(),
        "sage": run_sage(),
        "gap": run_gap(),
        "clifford": verify_clifford(),
        "galgebra": verify_galgebra(),
    }
    print("THREE_STACK_BRAID_LORENTZ_METRIPLECTIC_FINITE_OK")
    print(json.dumps(result, sort_keys=True))
    print(
        "scope: finite rational boost, S4 braid shadow, F4 Artin-action relation checks, "
        "Z2 central bookkeeping, and split Cl(1,1) signs only; no SO+(1,3), "
        "faithfulness, Mac Lane hexagon, TQFT anomaly, mass gap, or super-Kahler theorem asserted"
    )


if __name__ == "__main__":
    main()
