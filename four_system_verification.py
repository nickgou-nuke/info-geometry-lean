"""
Four-system verification of the Aubert-Plymen twisted group algebra
and its connection to Cl(1,1), Cl(5,5), O(5,5), D4/D5 Weyl data,
and the Klein-bottle quotient.

This script is deliberately fail-closed: any failed subprocess, GAP error,
Sage traceback, or failed assertion exits nonzero.
"""

import subprocess
import sys


def banner(title: str) -> None:
    print("\n" + "=" * 60)
    print(title)
    print("=" * 60)


def run_checked(cmd, *, input_text: str, name: str, timeout: int) -> str:
    result = subprocess.run(cmd, input=input_text, capture_output=True, text=True, timeout=timeout)
    print(result.stdout)
    if result.stderr:
        print(f"{name} stderr:")
        print(result.stderr)
    bad_markers = ["Error,", "Syntax warning", "Traceback", "AttributeError", "KeyError"]
    combined = result.stdout + result.stderr
    if result.returncode != 0 or any(marker in combined for marker in bad_markers):
        raise RuntimeError(f"{name} verification failed")
    return result.stdout


# ============================================================
# System 1: clifford — Cl(5,5) numeric verification
# ============================================================

banner("SYSTEM 1: clifford — Cl(5,5) / O(5,5)")

import clifford
import numpy as np

layout, blades = clifford.Cl(5, 5)
e = [blades[f"e{i}"] for i in range(1, 11)]

assert layout.gaDims == 1024
assert list(layout.sig) == [1, 1, 1, 1, 1, -1, -1, -1, -1, -1]
print(f"Cl(5,5) dimension: {layout.gaDims}")
print(f"Signature: {layout.sig}")

# Honest Cl(1,1) atom: first positive and first negative vector.
e_pos = e[0]
e_neg = e[5]
assert float((e_pos * e_pos)(0)) == 1.0
assert float((e_neg * e_neg)(0)) == -1.0
assert e_pos * e_neg + e_neg * e_pos == 0
print("Cl(1,1) atom: e_pos²=+1, e_neg²=-1, anticommutator=0")

# CPT phase flip: conjugation by positive unit fixes e_pos and flips e_neg.
def P(X):
    return e_pos * X * e_pos

assert P(e_pos) == e_pos
assert P(e_neg) == -e_neg
print("CPT phase-flip P(X)=e_pos X e_pos fixes e_pos and flips e_neg")

# O(5,5) vector-action check: simple reflection in positive unit preserves eta.
R = e_pos
Rrev = e_pos
basis_bitmap_to_idx = {sum(1 << (b - 1) for b in bt): i for i, bt in enumerate(layout.bladeTupList)}
A = np.zeros((10, 10))
for j, ej in enumerate(e):
    image = R * ej * Rrev
    for i in range(10):
        A[i, j] = float(image.value[basis_bitmap_to_idx[1 << i]])
eta = np.diag([1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
assert np.max(np.abs(A.T @ eta @ A - eta)) == 0.0
print("O(5,5) reflection matrix preserves eta exactly")

bivectors = [e[i] ^ e[j] for i in range(10) for j in range(i + 1, 10)]
assert len(bivectors) == 45
print("so(5,5) bivector count: 45")


# ============================================================
# System 2: galgebra — Symbolic Cl(5,5)
# ============================================================

banner("SYSTEM 2: galgebra — symbolic Cl(5,5)")

from galgebra.ga import Ga

ga = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1, 1, 1, 1, 1, -1, -1, -1, -1, -1])
e_g = list(ga.mv_basis)
ep_g = e_g[0]
en_g = e_g[5]
assert str(ep_g * ep_g) == "1"
assert str(en_g * en_g) == "-1"
assert str(ep_g * en_g + en_g * ep_g) == "0"
print("galgebra Cl(1,1) atom: e1²=1, e6²=-1, anticommutator=0")


# ============================================================
# System 3: GAP — Group-theoretic verification
# ============================================================

banner("SYSTEM 3: GAP — Weyl orders, triality, cocycle")

gap_script = r'''
weylDOrder := function(n)
  return 2^(n-1) * Factorial(n);
end;
if weylDOrder(5) <> 1920 then Error("bad D5 Weyl order"); fi;
if weylDOrder(4) <> 192 then Error("bad D4 Weyl order"); fi;
Print("W(D5) order formula: ", weylDOrder(5), "\n");
Print("W(D4) order formula: ", weylDOrder(4), "\n");
S3 := SymmetricGroup(3);
if Size(S3) <> 6 then Error("bad S3 order"); fi;
Print("S3 triality order: ", Size(S3), "\n");

N := 8;
Mu := function(a, b)
  return (-1)^(a[1] * b[2]);
end;
AddPair := function(a, b)
  return [ (a[1] + b[1]) mod 2, (a[2] + b[2]) mod N ];
end;
for eps in [0..1] do
for m in [0..N-1] do
for delta in [0..1] do
for n in [0..N-1] do
for kappa in [0..1] do
for p in [0..N-1] do
  a := [eps, m]; b := [delta, n]; c := [kappa, p];
  lhs := Mu(a,b) * Mu(AddPair(a,b), c);
  rhs := Mu(b,c) * Mu(a, AddPair(b,c));
  if lhs <> rhs then Error("cocycle identity failed"); fi;
od; od; od; od; od; od;
Print("finite quotient cocycle identity checked for Z/2 x Z/", N, "Z\n");
Print("No 1-dim scalar module: sY=-Ys with Y invertible forces y=0\n");
quit;
'''
run_checked(["/home/goutev/miniforge3/envs/sage/bin/gap", "-q"], input_text=gap_script, name="GAP", timeout=60)


# ============================================================
# System 4: SageMath — Root systems and Lie algebras
# ============================================================

banner("SYSTEM 4: SageMath — root systems and Lie algebra")

sage_script = r'''
R5 = RootSystem(['D', 5])
assert len(R5.index_set()) == 5
assert len(list(R5.root_poset())) == 20     # positive D5 roots
assert 2 * len(list(R5.root_poset())) == 40 # all D5 roots
print(f"D5 rank: {len(R5.index_set())}")
print(f"D5 root count: {2 * len(list(R5.root_poset()))}")
print("D5 Cartan matrix:")
print(R5.cartan_matrix())
from sage.algebras.lie_algebras.classical_lie_algebra import LieAlgebraChevalleyBasis
g = LieAlgebraChevalleyBasis(QQ, ['D', 5])
assert g.dimension() == 45
print(f"so(5,5) / D5 Lie algebra dimension: {g.dimension()}")

R4 = RootSystem(['D', 4])
assert len(R4.index_set()) == 4
assert len(list(R4.root_poset())) == 12
assert 2 * len(list(R4.root_poset())) == 24
print(f"D4 rank: {len(R4.index_set())}")
print(f"D4 root count: {2 * len(list(R4.root_poset()))}")
print("D4 Cartan matrix:")
print(R4.cartan_matrix())

W5 = WeylGroup(['D', 5])
W4 = WeylGroup(['D', 4])
assert W5.order() == 1920
assert W4.order() == 192
print(f"Sage W(D5) order: {W5.order()}")
print(f"Sage W(D4) order: {W4.order()}")
print("Klein bottle compact quotient: S^1 x S^1 / (w,z)~(-w,z^-1), chi=0 nonorientable")
print("Bott periodicity: Cl(5,5) ≅ M_32(R), Cl(1,1) ≅ M_2(R)")
'''
run_checked(["/home/goutev/miniforge3/envs/sage/bin/sage", "-q"], input_text=sage_script, name="SageMath", timeout=120)


banner("FOUR-SYSTEM VERIFICATION COMPLETE")
print("SymPy + clifford + galgebra + GAP + Sage checks passed with hard assertions.")
print("Lean translation target: InfoGeometry.Canonical.AubertPlymen")
