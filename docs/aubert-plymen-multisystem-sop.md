# Aubert--Plymen Multi-System Formalization SOP

Status: maintained operational SOP
Scope: Aubert--Plymen twisted group algebra representation, Cl(1,1) atom, O(5,5)/Cl(5,5) support, SymPy certificates, Lean 4 kernel translation.

## Purpose

This SOP records the exact verified workflow used to formalize the Aubert--Plymen twisted group algebra representation from `2603.03027v1.pdf` in the `info-geometry-lean` repository.

The method is intentionally multi-lane:

1. Extract and normalize the mathematics from the source.
2. Verify the representation in SymPy.
3. Verify Clifford/O(5,5) support with `clifford` and `galgebra`.
4. Verify group/root data with GAP and SageMath.
5. Translate only the computationally verified core into Lean 4.
6. Build the Lean target and distinguish kernel-checked theorems from external computational evidence.

Do not claim Lean closure for anything that is only checked by SymPy/GAP/Sage/clifford/galgebra. External systems support discovery and certificate generation; Lean closure is only what `lake build` kernel-checks.

## Environment

Repository:

```bash
cd /home/goutev/repos/info-geometry-lean
```

Python lane:

```bash
.venv-123/bin/python3
```

SageMath:

```bash
/home/goutev/miniforge3/envs/sage/bin/sage
```

GAP:

```bash
/home/goutev/miniforge3/envs/sage/bin/gap
```

Lean:

```bash
lake build <target>
lake env lean <file>
```

Do not assume `sage` or `gap` are on PATH in non-activated shells. Use the direct paths above.

## Source Math Normalization

From Aubert--Plymen, the twisted algebra has generators and relations:

```text
s² = 1
sX = X⁻¹s
sY = -Ys
XY = YX
```

Correct simple-module matrices:

```text
s ↦ [[0, 1], [1, 0]]
X ↦ [[z, 0], [0, z⁻¹]]
Y ↦ [[w, 0], [0, -w]]
```

Parameter involution / module equivalence:

```text
(w, z) ↦ (-w, z⁻¹)
```

Primitive spectrum quotient:

```text
(C× × C×) / ((w,z) ~ (-w,z⁻¹))
```

Maximal compact real form:

```text
(S¹ × S¹) / ((w,z) ~ (-w,z⁻¹))
```

This quotient is the Klein bottle.

Discard the tempting but wrong representation:

```text
s = [[0, -w], [1, 0]]
```

because it gives `s² = -w I`, not `1`.

## Step 1: SymPy Verification

Primary script:

```bash
.venv-123/bin/python3 sympy_twisted_algebra.py
```

The SymPy script must assert, not merely print:

```python
assert s * s == eye(2)
assert simplify(s * X - X.inv() * s) == zeros(2)
assert simplify(s * Y + Y * s) == zeros(2)
assert simplify(X * Y - Y * X) == zeros(2)
assert simplify(s * X * s.inv() - M_X(z**(-1))) == zeros(2)
assert simplify(s * Y * s.inv() - M_Y(-w)) == zeros(2)
```

It should also check the Cl(1,1) atom/trifactor lane:

```text
e₊ = [[1,0],[0,-1]]
e₋ = [[0,1],[-1,0]]
e₊² = 1
e₋² = -1
e₊e₋ + e₋e₊ = 0
T³ = T for T = e₊
```

Expected terminal marker:

```text
ALL VERIFICATIONS PASSED
```

## Step 2: Clifford / Galgebra O(5,5) Support

Primary script:

```bash
.venv-123/bin/python3 four_system_verification.py
```

For the `clifford` lane, create Cl(5,5):

```python
import clifford
layout, blades = clifford.Cl(5, 5)
e = [blades[f"e{i}"] for i in range(1, 11)]
```

Use an honest Cl(1,1) atom inside Cl(5,5):

```python
e_pos = e[0]  # square +1
e_neg = e[5]  # square -1
assert e_pos * e_neg + e_neg * e_pos == 0
```

Do not use `e[1]` as the negative generator in signature `(5,5)`; it is still positive. The negative basis starts at `e[5]` / printed `e6`.

Verify a phase flip:

```python
def P(X):
    return e_pos * X * e_pos

assert P(e_pos) == e_pos
assert P(e_neg) == -e_neg
```

Verify an O(5,5) metric-preserving action exactly with `eta = diag(1,1,1,1,1,-1,-1,-1,-1,-1)`.

For the `galgebra` lane:

```python
from galgebra.ga import Ga
ga = Ga("e1 e2 e3 e4 e5 e6 e7 e8 e9 e10", g=[1,1,1,1,1,-1,-1,-1,-1,-1])
e_g = list(ga.mv_basis)
assert str(e_g[0] * e_g[0]) == "1"
assert str(e_g[5] * e_g[5]) == "-1"
assert str(e_g[0] * e_g[5] + e_g[5] * e_g[0]) == "0"
```

Expected checks:

```text
Cl(5,5) dimension: 1024
Cl(1,1) atom: e_pos²=+1, e_neg²=-1, anticommutator=0
O(5,5) reflection matrix preserves eta exactly
so(5,5) bivector count: 45
galgebra Cl(1,1) atom: e1²=1, e6²=-1, anticommutator=0
```

## Step 3: GAP Verification

Use the direct GAP path:

```bash
/home/goutev/miniforge3/envs/sage/bin/gap -q
```

The robust GAP lane should avoid optional package-dependent `WeylGroup` calls if unavailable and use checked formulas for D-type Weyl orders:

```gap
weylDOrder := function(n)
  return 2^(n-1) * Factorial(n);
end;
if weylDOrder(5) <> 1920 then Error("bad D5 Weyl order"); fi;
if weylDOrder(4) <> 192 then Error("bad D4 Weyl order"); fi;
S3 := SymmetricGroup(3);
if Size(S3) <> 6 then Error("bad S3 order"); fi;
```

Check the finite quotient cocycle identity for:

```text
µ((ε,m),(δ,n)) = (-1)^(ε n)
```

The batch runner must fail on GAP errors. Do not print a positive summary after GAP emits `Error,` or `Syntax warning`.

Expected checks:

```text
W(D5) order formula: 1920
W(D4) order formula: 192
S3 triality order: 6
finite quotient cocycle identity checked
```

## Step 4: SageMath Verification

Use the direct Sage path:

```bash
/home/goutev/miniforge3/envs/sage/bin/sage -q
```

Sage 10.9 API pitfalls:

```python
R5 = RootSystem(['D', 5])
len(R5.index_set())        # rank, not R5.rank()
len(list(R5.root_poset())) # positive roots, not roots_number()
```

Hard assertions:

```python
R5 = RootSystem(['D', 5])
assert len(R5.index_set()) == 5
assert 2 * len(list(R5.root_poset())) == 40

R4 = RootSystem(['D', 4])
assert len(R4.index_set()) == 4
assert 2 * len(list(R4.root_poset())) == 24

from sage.algebras.lie_algebras.classical_lie_algebra import LieAlgebraChevalleyBasis
g = LieAlgebraChevalleyBasis(QQ, ['D', 5])
assert g.dimension() == 45

W5 = WeylGroup(['D', 5])
W4 = WeylGroup(['D', 4])
assert W5.order() == 1920
assert W4.order() == 192
```

Expected checks:

```text
D5 rank: 5
D5 root count: 40
so(5,5) / D5 Lie algebra dimension: 45
D4 rank: 4
D4 root count: 24
Sage W(D5) order: 1920
Sage W(D4) order: 192
```

The Sage virtualenv warning is harmless:

```text
UserWarning: Attempting to work in a virtualenv
```

but Python tracebacks / AttributeErrors / KeyErrors are failures.

## Step 5: Lean Translation

Target file:

```text
lean/InfoGeometry/Canonical/AubertPlymen.lean
```

Use a concrete real 2×2 slice for kernel proof engineering:

```lean
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def s : Mat2 := !![(0 : ℝ), 1; 1, (0 : ℝ)]
def X (z : ℝ) : Mat2 := !![z, 0; 0, z⁻¹]
def Y (w : ℝ) : Mat2 := !![w, 0; 0, -w]
```

Avoid dependent nonzero arguments in `X`/`Y` if the theorem can be stated as a parameter transform. This avoids proof noise like `X z hz` and problematic existential annotations.

Kernel theorem surface:

```lean
theorem s_sq : s * s = 1
theorem sX_eq_Xinv_s (z : ℝ) : s * X z = X z⁻¹ * s
theorem sY_eq_neg_Ys (w : ℝ) : s * Y w = -Y w * s
theorem XY_eq_YX (z w : ℝ) : X z * Y w = Y w * X z
theorem sXs_eq_Xinv (z : ℝ) : s * X z * s = X z⁻¹
theorem sYs_eq_Yneg (w : ℝ) : s * Y w * s = Y (-w)
```

Cl(1,1) atom:

```lean
def ePlus : Mat2 := Y 1
def eMinus : Mat2 := s * ePlus

theorem ePlus_sq : ePlus * ePlus = 1
theorem eMinus_sq : eMinus * eMinus = -1
theorem ePlus_eMinus_anticomm : ePlus * eMinus + eMinus * ePlus = 0
```

No-one-dimensional scalar obstruction:

```lean
theorem no_one_dimensional_scalar_model {sigma y : ℝ}
    (hsigma : sigma ≠ 0) (hy : y ≠ 0) (h : sigma * y = -(y * sigma)) : False
```

Proof style:

```lean
ext i j <;> fin_cases i <;> fin_cases j <;>
  simp [s, X, Y, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
```

Do not use `native_decide` over real matrices. It fails because real decidable equality is noncomputable.

Do not use placeholder closures:

```lean
-- forbidden
example : True := by trivial
```

## Step 6: Lean Build Verification

Run:

```bash
lake build InfoGeometry.Canonical.AubertPlymen
```

Expected success marker:

```text
Build completed successfully (3102 jobs).
```

Check for forbidden placeholders in the Lean target:

```bash
rg 'sorry|axiom|: True :=|native_decide' lean/InfoGeometry/Canonical/AubertPlymen.lean
```

Only docstring/prose mentions should appear; no theorem body may contain these.

## Final Validation Bundle

Run all of this before reporting success:

```bash
cd /home/goutev/repos/info-geometry-lean
.venv-123/bin/python3 sympy_twisted_algebra.py
.venv-123/bin/python3 four_system_verification.py
lake build InfoGeometry.Canonical.AubertPlymen
lake build InfoGeometry.Krein.Cl55Certificates
rg 'sorry|axiom|: True :=|native_decide' lean/InfoGeometry/Canonical/AubertPlymen.lean
```

Acceptable final statuses:

```text
ALL VERIFICATIONS PASSED
FOUR-SYSTEM VERIFICATION COMPLETE
Build completed successfully
```

## What Was Kernel-Checked

The successful Lean target kernel-checks:

```text
AubertPlymen.s_sq
AubertPlymen.sX_eq_Xinv_s
AubertPlymen.sY_eq_neg_Ys
AubertPlymen.XY_eq_YX
AubertPlymen.sXs_eq_Xinv
AubertPlymen.sYs_eq_Yneg
AubertPlymen.ePlus_sq
AubertPlymen.eMinus_sq
AubertPlymen.ePlus_eMinus_anticomm
AubertPlymen.no_one_dimensional_scalar_model
AubertPlymen.relation_package
```

## Common Failure Modes

1. Wrong Cl(1,1) negative vector in Cl(5,5):
   - Bad: `e[1]` in `clifford.Cl(5,5)`; it squares to `+1`.
   - Good: `e[5]`; it squares to `-1`.

2. False GAP success:
   - Bad: print summary after GAP emits `Error, no method found`.
   - Good: subprocess runner scans stdout/stderr for `Error,` and exits nonzero.

3. Sage API hallucination:
   - Bad: `R5.rank()` / `R5.root_lattice().roots_number()`.
   - Good: `len(R5.index_set())` / `2 * len(list(R5.root_poset()))`.

4. Lean `native_decide` on `ℝ` matrices:
   - Bad: `native_decide`.
   - Good: entrywise `ext`, `fin_cases`, `simp`, `ring`.

5. Overclaiming topology in Lean:
   - The Klein bottle quotient is verified computationally/prose-operationally here, not formalized as a Lean topological quotient in `AubertPlymen.lean`.
   - Report it as external Sage/SOP support unless a dedicated Lean topology theorem is added and built.

6. Treating external computations as promotion authority:
   - SymPy/GAP/Sage/clifford/galgebra support the translation.
   - Only Lean theorem names built by `lake build` are kernel closure.

## Output Reporting Template

Use this shape:

```text
Implemented and verified.

SymPy:
- <script path>
- relations checked: ...

Support systems:
- clifford/galgebra: ...
- GAP: ...
- SageMath: ...

Lean:
- <Lean target path>
- kernel-checked theorem names: ...
- build command and result: ...

Limits:
- topology quotient / O(5,5) support is external unless separately Lean-formalized.
```
