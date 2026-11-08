/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.Decomposition
import Mathlib.Tactic.Ring

/-!
# Hopf Braid Crossing Supertrace, Fisher Trace Dual, & Quadratic Braid Invariant

Target: `InfoGeometry/Topology/HopfInvariantBraidSupertrace.lean`

This module epistemically compiles Section 150 (Turns 352–355) of
`1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or` directly on the 8D split-octonion Zorn
matrix algebra `ZornCell R` (`InfoGeometry.Algebra.Zorn.ConcreteComposition`):

1. **Hopf Braid Crossing Operator $B(\mathbf{u}, \mathbf{v}) = [U(\mathbf{u}), V(\mathbf{v})]$:**
   - Proves that the commutator of the forward and backward Majorana sheets
     evaluates to $(\mathbf{u} \cdot \mathbf{v}) K_0$, has vanishing ordinary
     trace $\mathrm{Tr}(B) = 0$, and has chiral supertrace
     $$\mathrm{STr}\bigl([U(\mathbf{u}), V(\mathbf{v})]\bigr) = 2(\mathbf{u} \cdot \mathbf{v})$$
     (`hopfBraidCommutator_supertrace_and_square`).
2. **Quadratic Braid Casimir & Determinant Invariant:**
   - Proves that the square of the braid crossing operator is proportional to
     the identity with coefficient $(\mathbf{u} \cdot \mathbf{v})^2$:
     $$B(\mathbf{u}, \mathbf{v})^2 = (\mathbf{u} \cdot \mathbf{v})^2 \mathbf{1}, \qquad
       \det_Z\bigl(B(\mathbf{u}, \mathbf{v})\bigr) = -(\mathbf{u} \cdot \mathbf{v})^2.$$
3. **Fisher Symmetric Fusion Dual & Additivity (`hopfBraid_fisher_duality_and_additivity`):**
   - Proves that the symmetric anticommutator $F(\mathbf{u}, \mathbf{v}) = \{U(\mathbf{u}), V(\mathbf{v})\}$
     has ordinary trace $\mathrm{Tr}(F) = 2(\mathbf{u} \cdot \mathbf{v})$ and vanishing
     supertrace $\mathrm{STr}(F) = 0$, and that the Hopf braid crossing operator is
     strictly bilinear in the 3D sheet vectors.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved 8D Zorn Braid & Supertrace Theorems (`[kernel_verified]`):**
  - `hopfBraidCommutator_supertrace_and_square`, `hopfBraid_fisher_duality_and_additivity`,
    and `hopfBraid_zorn_noncommutative`.
* **BUCKET 2 — Eliminated Certificate Wrappers (Zero Remaining):**
  - `HopfInvariantBraidCertificate : Prop` from Turn 352 is eliminated.
* **BUCKET 3 — Smooth $S^3 \to S^2$ Whitehead Integral Hopf Invariant (`[bucket_3_open_debt]`):**
  - De Rham integral cohomology $\int_{S^3} A \wedge dA$ over smooth 3-spheres
    remains outside this algebraic 8D Zorn commutator model.
-/

namespace InfoGeometry.Topology.HopfInvariant

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

variable {R : Type*} [CommRing R]

/-- Multiplicative identity $\mathbf{1} = \mathrm{diag}(1, 1)$ in `ZornCell R`. -/
def oneZ : ZornCell R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Para-symplectic grading involution $K_0 = e_1 - e_2$ in `ZornCell R`. -/
def paraSymplecticK0 : ZornCell R :=
  ⟨1, -1, 0, 0, 0, 0, 0, 0⟩

/-- Componentwise subtraction on `ZornCell R`. -/
def subZ (X Y : ZornCell R) : ZornCell R :=
  ⟨X.r - Y.r, X.s - Y.s,
   X.x1 - Y.x1, X.x2 - Y.x2, X.x3 - Y.x3,
   X.y1 - Y.y1, X.y2 - Y.y2, X.y3 - Y.y3⟩

/-- Scalar multiplication on `ZornCell R`. -/
def smulZ (c : R) (X : ZornCell R) : ZornCell R :=
  ⟨c * X.r, c * X.s,
   c * X.x1, c * X.x2, c * X.x3,
   c * X.y1, c * X.y2, c * X.y3⟩

/-- Ordinary trace $\mathrm{Tr}(X) = r + s$ on `ZornCell R`. -/
def traceZ (X : ZornCell R) : R :=
  X.r + X.s

/-- Chiral supertrace $\mathrm{STr}(X) = r - s$ on `ZornCell R`. -/
def superTraceZ (X : ZornCell R) : R :=
  X.r - X.s

/-- Upper-right isotropic Majorana sheet $U(\mathbf{u}) \in \mathrm{ZornCell}\,R$. -/
def sheetU (u₁ u₂ u₃ : R) : ZornCell R :=
  ⟨0, 0, u₁, u₂, u₃, 0, 0, 0⟩

/-- Lower-left isotropic Majorana sheet $V(\mathbf{v}) \in \mathrm{ZornCell}\,R$. -/
def sheetV (v₁ v₂ v₃ : R) : ZornCell R :=
  ⟨0, 0, 0, 0, 0, v₁, v₂, v₃⟩

/-- Hopf braid crossing commutator $B(\mathbf{u}, \mathbf{v}) = [U(\mathbf{u}), V(\mathbf{v})]$
in `ZornCell R`. -/
def hopfBraidCommutator (u₁ u₂ u₃ v₁ v₂ v₃ : R) : ZornCell R :=
  subZ (mulZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃))
       (mulZ (sheetV v₁ v₂ v₃) (sheetU u₁ u₂ u₃))

/-- Symmetric Fisher fusion anticommutator $F(\mathbf{u}, \mathbf{v}) = \{U(\mathbf{u}), V(\mathbf{v})\}$
in `ZornCell R`. -/
def fisherSheetAnticommutator (u₁ u₂ u₃ v₁ v₂ v₃ : R) : ZornCell R :=
  addZ (mulZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃))
       (mulZ (sheetV v₁ v₂ v₃) (sheetU u₁ u₂ u₃))

/-- **Hopf Braid Crossing Supertrace, Square Law, & Determinant
(`hopfBraidCommutator_supertrace_and_square`):**
For any 3D sheet vectors $\mathbf{u}, \mathbf{v} \in R^3$:
1. $B(\mathbf{u}, \mathbf{v}) = (\mathbf{u} \cdot \mathbf{v})\,K_0$;
2. $\mathrm{STr}(B(\mathbf{u}, \mathbf{v})) = 2(\mathbf{u} \cdot \mathbf{v})$ and
   $\mathrm{Tr}(B(\mathbf{u}, \mathbf{v})) = 0$;
3. $B(\mathbf{u}, \mathbf{v})^2 = (\mathbf{u} \cdot \mathbf{v})^2\,\mathbf{1}$;
4. $\det_Z(B(\mathbf{u}, \mathbf{v})) = -(\mathbf{u} \cdot \mathbf{v})^2$. -/
theorem hopfBraidCommutator_supertrace_and_square (u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    hopfBraidCommutator u₁ u₂ u₃ v₁ v₂ v₃ =
      smulZ (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) paraSymplecticK0 ∧
    superTraceZ (hopfBraidCommutator u₁ u₂ u₃ v₁ v₂ v₃) =
      2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ∧
    traceZ (hopfBraidCommutator u₁ u₂ u₃ v₁ v₂ v₃) = 0 ∧
    mulZ (hopfBraidCommutator u₁ u₂ u₃ v₁ v₂ v₃)
         (hopfBraidCommutator u₁ u₂ u₃ v₁ v₂ v₃) =
      smulZ ((u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ^ 2) oneZ ∧
    detZ (hopfBraidCommutator u₁ u₂ u₃ v₁ v₂ v₃) =
      -((u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [hopfBraidCommutator, subZ, mulZ, sheetU, sheetV, smulZ, paraSymplecticK0]; ring)
  · dsimp [superTraceZ, hopfBraidCommutator, subZ, mulZ, sheetU, sheetV]; ring
  · dsimp [traceZ, hopfBraidCommutator, subZ, mulZ, sheetU, sheetV]; ring
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [hopfBraidCommutator, subZ, mulZ, sheetU, sheetV, smulZ, oneZ]; ring)
  · dsimp [detZ, hopfBraidCommutator, subZ, mulZ, sheetU, sheetV]; ring

/-- **Fisher Symmetric Fusion Dual & Left Additivity of the Braid Crossing
(`hopfBraid_fisher_duality_and_additivity`):**
For any $\mathbf{u}, \mathbf{w}, \mathbf{v} \in R^3$:
1. $\mathrm{Tr}(\{U(\mathbf{u}), V(\mathbf{v})\}) = 2(\mathbf{u} \cdot \mathbf{v})$ and
   $\mathrm{STr}(\{U(\mathbf{u}), V(\mathbf{v})\}) = 0$;
2. $B(\mathbf{u} + \mathbf{w}, \mathbf{v}) = B(\mathbf{u}, \mathbf{v}) + B(\mathbf{w}, \mathbf{v})$. -/
theorem hopfBraid_fisher_duality_and_additivity (u₁ u₂ u₃ w₁ w₂ w₃ v₁ v₂ v₃ : R) :
    traceZ (fisherSheetAnticommutator u₁ u₂ u₃ v₁ v₂ v₃) =
      2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ∧
    superTraceZ (fisherSheetAnticommutator u₁ u₂ u₃ v₁ v₂ v₃) = 0 ∧
    hopfBraidCommutator (u₁ + w₁) (u₂ + w₂) (u₃ + w₃) v₁ v₂ v₃ =
      addZ (hopfBraidCommutator u₁ u₂ u₃ v₁ v₂ v₃)
           (hopfBraidCommutator w₁ w₂ w₃ v₁ v₂ v₃) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [traceZ, fisherSheetAnticommutator, addZ, mulZ, sheetU, sheetV]; ring
  · dsimp [superTraceZ, fisherSheetAnticommutator, addZ, mulZ, sheetU, sheetV]; ring
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [hopfBraidCommutator, addZ, subZ, mulZ, sheetU, sheetV]; ring)

/-- Explicit non-commutativity witness on `ZornCell ℤ` showing that the Hopf braid
commutator of `sheetU 1 0 0` and `sheetV 1 0 0` is non-zero. -/
theorem hopfBraid_zorn_noncommutative :
    mulZ (sheetU (1 : ℤ) 0 0) (sheetV 1 0 0) ≠
      mulZ (sheetV 1 0 0) (sheetU 1 0 0) := by
  intro hEq
  have hr := congrArg ZornCell.r hEq
  revert hr
  decide

end InfoGeometry.Topology.HopfInvariant
