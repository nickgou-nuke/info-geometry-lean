/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.Decomposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Witten–Möbius Chiral Parity Swing & Klein Bottle EPR Vacuum Topology

Target: `InfoGeometry/Superalgebra/WittenMoebiusChiralParity.lean`

This module epistemically compiles Sections 151 and 152 (Turns 358–362) of
`1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or` directly on the 8D split-octonion Zorn
matrix algebra `ZornCell R` (`InfoGeometry.Algebra.Zorn.ConcreteComposition`):

1. **8D Witten–Möbius Chiral Parity Charge Operator (`wittenMoebiusOperator`):**
   $$\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})
     = c \cdot K_0 - s \cdot \bigl(U(\mathbf{u}) - V(\mathbf{v})\bigr).$$
   - Proves the exact Clifford square law
     $\mathcal{P}_{\mathrm{WM}}^2 = (c^2 - s^2(\mathbf{u} \cdot \mathbf{v}))\,\mathbf{1}$,
     determinant law $\det_Z(\mathcal{P}_{\mathrm{WM}}) = -(c^2 - s^2(\mathbf{u} \cdot \mathbf{v}))$,
     and supertrace protection $\mathrm{STr}(\mathcal{P}_{\mathrm{WM}}) = 2c$
     (`wittenMoebius_clifford_square_and_supertrace`).
2. **Klein Bottle Non-Orientable Conjugation & EPR Gluing Defect (`wittenMoebius_klein_conjugation_and_epr_defect`):**
   - Proves the orientation-reversal conjugation identity
     $K_0 \mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v}) K_0 = \mathcal{P}_{\mathrm{WM}}(c, -s, \mathbf{u}, \mathbf{v})$,
     the exact EPR singlet defect formula
     $\mathcal{P}_{\mathrm{WM}}^2 - \mathbf{1} = -s^2(1 + \mathbf{u} \cdot \mathbf{v})\,\mathbf{1}$
     under $c^2 + s^2 = 1$, and exact involution $\mathcal{P}_{\mathrm{WM}}^2 = \mathbf{1}$
     when $\mathbf{u} \cdot \mathbf{v} = -1$.
3. **Section 152 — Real Angular Klein Bottle Vacuum Periodicity (`wittenMoebius_klein_bottle_sewing_periodicity`):**
   - Over $\mathbb{R}$ with $c = \cos(2\theta)$ and $s = \sin(2\theta)$, proves
     $\pi$-periodicity $\mathcal{P}_{\mathrm{WM}}(\theta + \pi) = \mathcal{P}_{\mathrm{WM}}(\theta)$,
     Möbius quarter-turn inversion $\mathcal{P}_{\mathrm{WM}}(\theta + \pi/2) = -\mathcal{P}_{\mathrm{WM}}(\theta)$,
     and vanishing Euler-characteristic supertrace balance
     $\mathrm{STr}(\theta) + \mathrm{STr}(\theta + \pi/2) = 0$.

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved 8D Zorn & Trigonometric Theorems (`[kernel_verified]`):**
  - `wittenMoebius_clifford_square_and_supertrace`,
    `wittenMoebius_klein_conjugation_and_epr_defect`,
    `wittenMoebius_epr_singlet_involution`,
    `wittenMoebius_klein_bottle_sewing_periodicity`, and
    `wittenMoebius_zorn_noncommutative`.
* **BUCKET 2 — Eliminated Certificate Wrappers (Zero Remaining):**
  - `WittenMoebiusParityCertificate : Prop` from Turn 358 is eliminated.
* **BUCKET 3 — Continuum Pin$^-$/Pin$^+$ Cobordism Spectrum $\Omega^{\mathrm{Pin}^-}_2$ (`[bucket_3_open_debt]`):**
  - Brown–Kervaire $\mathbb{Z}_8$ Arf-invariant cobordism classification of smooth
    non-orientable surfaces remains outside this 8D Zorn operator model.
-/

namespace InfoGeometry.Superalgebra.WittenMoebiusParity

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

section AlgebraicWittenMoebius

variable {R : Type*} [Ring R]

/-- Multiplicative identity $\mathbf{1} = \mathrm{diag}(1, 1)$ in `ZornCell R`. -/
def oneZ : ZornCell R :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0⟩

/-- Para-symplectic grading involution $K_0 = e_1 - e_2$ in `ZornCell R`. -/
def paraSymplecticK0 : ZornCell R :=
  ⟨1, -1, 0, 0, 0, 0, 0, 0⟩

/-- Additive negation on `ZornCell R`. -/
def negZ (X : ZornCell R) : ZornCell R :=
  ⟨-X.r, -X.s, -X.x1, -X.x2, -X.x3, -X.y1, -X.y2, -X.y3⟩

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

/-- The 8D **Witten–Möbius Chiral Parity Charge Operator**
$$\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})
  = c \cdot K_0 - s \cdot \bigl(U(\mathbf{u}) - V(\mathbf{v})\bigr).$$ -/
def wittenMoebiusOperator (c s u₁ u₂ u₃ v₁ v₂ v₃ : R) : ZornCell R :=
  subZ (smulZ c paraSymplecticK0)
       (smulZ s (subZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)))

variable {R : Type*} [CommRing R]

/-- **Clifford Square, Determinant, & Supertrace Protection of `wittenMoebiusOperator`
(`wittenMoebius_clifford_square_and_supertrace`):**
For all $c, s \in R$ and $\mathbf{u}, \mathbf{v} \in R^3$:
1. $\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})^2 = (c^2 - s^2(\mathbf{u} \cdot \mathbf{v}))\,\mathbf{1}$;
2. $\det_Z(\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})) = -(c^2 - s^2(\mathbf{u} \cdot \mathbf{v}))$;
3. $\mathrm{STr}(\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})) = 2c$;
4. $\mathrm{Tr}(\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})) = 0$. -/
theorem wittenMoebius_clifford_square_and_supertrace (c s u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    mulZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃)
         (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) =
      smulZ (c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃)) oneZ ∧
    detZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) =
      -(c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃)) ∧
    superTraceZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) = 2 * c ∧
    traceZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [wittenMoebiusOperator, mulZ, subZ, smulZ, paraSymplecticK0,
              sheetU, sheetV, oneZ]; ring)
  · dsimp [detZ, wittenMoebiusOperator, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]; ring
  · dsimp [superTraceZ, wittenMoebiusOperator, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]; ring
  · dsimp [traceZ, wittenMoebiusOperator, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]; ring

/-- **Klein Bottle $K_0$-Conjugation Orientation Reversal & EPR Gluing Defect
(`wittenMoebius_klein_conjugation_and_epr_defect`):**
1. Conjugating $\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})$ by $K_0$ reverses
   the off-diagonal Möbius twist sign $s \mapsto -s$:
   $$K_0 \cdot \mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v}) \cdot K_0
     = \mathcal{P}_{\mathrm{WM}}(c, -s, \mathbf{u}, \mathbf{v});$$
2. Whenever $c^2 + s^2 = 1$, the deviation of $\mathcal{P}_{\mathrm{WM}}^2$ from $\mathbf{1}$
   is proportional to the EPR singlet gluing defect $1 + \mathbf{u} \cdot \mathbf{v}$:
   $$\mathcal{P}_{\mathrm{WM}}(c, s, \mathbf{u}, \mathbf{v})^2 - \mathbf{1}
     = -s^2\bigl(1 + \mathbf{u} \cdot \mathbf{v}\bigr)\,\mathbf{1}.$$ -/
theorem wittenMoebius_klein_conjugation_and_epr_defect
    (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_trig : c ^ 2 + s ^ 2 = 1) :
    mulZ (mulZ paraSymplecticK0 (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃))
         paraSymplecticK0 =
      wittenMoebiusOperator c (-s) u₁ u₂ u₃ v₁ v₂ v₃ ∧
    subZ (mulZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃)
               (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃)) oneZ =
      smulZ (-(s ^ 2 * (1 + (u₁ * v₁ + u₂ * v₂ + u₃ * v₃)))) oneZ := by
  refine ⟨?_, ?_⟩
  · refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [wittenMoebiusOperator, mulZ, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]; ring)
  · rw [(wittenMoebius_clifford_square_and_supertrace c s u₁ u₂ u₃ v₁ v₂ v₃).1]
    have hScalar :
        c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) - 1 =
          -(s ^ 2 * (1 + (u₁ * v₁ + u₂ * v₂ + u₃ * v₃))) := by
      linear_combination h_trig
    refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp [subZ, smulZ, oneZ]; linear_combination hScalar
    · dsimp [subZ, smulZ, oneZ]; linear_combination hScalar
    · dsimp [subZ, smulZ, oneZ]; ring
    · dsimp [subZ, smulZ, oneZ]; ring
    · dsimp [subZ, smulZ, oneZ]; ring
    · dsimp [subZ, smulZ, oneZ]; ring
    · dsimp [subZ, smulZ, oneZ]; ring
    · dsimp [subZ, smulZ, oneZ]; ring

/-- **Topological Involution at the EPR Singlet (`wittenMoebius_epr_singlet_involution`):**
If $c^2 + s^2 = 1$ and the chiral Majorana sheets satisfy the EPR singlet condition
$\mathbf{u} \cdot \mathbf{v} = -1$, then $\mathcal{P}_{\mathrm{WM}}^2 = \mathbf{1}$
and $\det_Z(\mathcal{P}_{\mathrm{WM}}) = -1$. -/
theorem wittenMoebius_epr_singlet_involution (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_trig : c ^ 2 + s ^ 2 = 1)
    (h_epr : u₁ * v₁ + u₂ * v₂ + u₃ * v₃ = -1) :
    mulZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃)
         (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) = oneZ ∧
    detZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) = -1 := by
  have hLaws := wittenMoebius_clifford_square_and_supertrace c s u₁ u₂ u₃ v₁ v₂ v₃
  have hFactor : c ^ 2 - s ^ 2 * (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) = 1 := by
    rw [h_epr]
    linear_combination h_trig
  refine ⟨?_, ?_⟩
  · rw [hLaws.1, hFactor]
    refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [smulZ, oneZ]; ring)
  · rw [hLaws.2.1, hFactor]

/-- Explicit non-commutativity witness on `ZornCell ℤ`. -/
theorem wittenMoebius_zorn_noncommutative :
    mulZ (sheetU (1 : ℤ) 0 0) (sheetV 1 0 0) ≠
      mulZ (sheetV 1 0 0) (sheetU 1 0 0) := by
  intro hEq
  have hr := congrArg ZornCell.r hEq
  revert hr
  decide

end AlgebraicWittenMoebius

section RealKleinBottleVacuum

/-- Real angular Witten–Möbius parity operator
$\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v}) = \cos(2\theta)\,K_0 - \sin(2\theta)\,(U(\mathbf{u}) - V(\mathbf{v}))$. -/
noncomputable def wittenMoebiusAngle (θ u₁ u₂ u₃ v₁ v₂ v₃ : ℝ) : ZornCell ℝ :=
  wittenMoebiusOperator (Real.cos (2 * θ)) (Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃

/-- **Section 152 — Klein Bottle Sewing Periodicity & Vanishing Euler Balance
(`wittenMoebius_klein_bottle_sewing_periodicity`):**
For every Möbius angle $\theta \in \mathbb{R}$ and EPR-entangled sheets
$\mathbf{u}, \mathbf{v} \in \mathbb{R}^3$ satisfying $u_1 v_1 + u_2 v_2 + u_3 v_3 = -1$:
1. $\mathcal{P}_{\mathrm{WM}}(\theta + \pi, \mathbf{u}, \mathbf{v}) = \mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})$;
2. $\mathcal{P}_{\mathrm{WM}}(\theta + \pi / 2, \mathbf{u}, \mathbf{v}) = -\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})$;
3. $\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})^2 = \mathbf{1}$;
4. $\det_Z(\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})) = -1$;
5. $\mathrm{STr}(\mathcal{P}_{\mathrm{WM}}(\theta, \mathbf{u}, \mathbf{v})) + \mathrm{STr}(\mathcal{P}_{\mathrm{WM}}(\theta + \pi / 2, \mathbf{u}, \mathbf{v})) = 0$. -/
theorem wittenMoebius_klein_bottle_sewing_periodicity
    (θ u₁ u₂ u₃ v₁ v₂ v₃ : ℝ)
    (h_epr : u₁ * v₁ + u₂ * v₂ + u₃ * v₃ = -1) :
    wittenMoebiusAngle (θ + Real.pi) u₁ u₂ u₃ v₁ v₂ v₃ =
      wittenMoebiusAngle θ u₁ u₂ u₃ v₁ v₂ v₃ ∧
    wittenMoebiusAngle (θ + Real.pi / 2) u₁ u₂ u₃ v₁ v₂ v₃ =
      negZ (wittenMoebiusAngle θ u₁ u₂ u₃ v₁ v₂ v₃) ∧
    mulZ (wittenMoebiusAngle θ u₁ u₂ u₃ v₁ v₂ v₃)
         (wittenMoebiusAngle θ u₁ u₂ u₃ v₁ v₂ v₃) = oneZ ∧
    detZ (wittenMoebiusAngle θ u₁ u₂ u₃ v₁ v₂ v₃) = -1 ∧
    superTraceZ (wittenMoebiusAngle θ u₁ u₂ u₃ v₁ v₂ v₃) +
      superTraceZ (wittenMoebiusAngle (θ + Real.pi / 2) u₁ u₂ u₃ v₁ v₂ v₃) = 0 := by
  have hArgPi : 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi := by ring
  have hCosPi : Real.cos (2 * (θ + Real.pi)) = Real.cos (2 * θ) := by
    rw [hArgPi, Real.cos_add_two_pi]
  have hSinPi : Real.sin (2 * (θ + Real.pi)) = Real.sin (2 * θ) := by
    rw [hArgPi, Real.sin_add_two_pi]
  have hArgHalf : 2 * (θ + Real.pi / 2) = 2 * θ + Real.pi := by ring
  have hCosHalf : Real.cos (2 * (θ + Real.pi / 2)) = -Real.cos (2 * θ) := by
    rw [hArgHalf, Real.cos_add_pi]
  have hSinHalf : Real.sin (2 * (θ + Real.pi / 2)) = -Real.sin (2 * θ) := by
    rw [hArgHalf, Real.sin_add_pi]
  have hEPR := wittenMoebius_epr_singlet_involution
    (Real.cos (2 * θ)) (Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃
    (Real.cos_sq_add_sin_sq (2 * θ)) h_epr
  refine ⟨?_, ?_, hEPR.1, hEPR.2, ?_⟩
  · unfold wittenMoebiusAngle
    rw [hCosPi, hSinPi]
  · unfold wittenMoebiusAngle
    rw [hCosHalf, hSinHalf]
    refine ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [wittenMoebiusOperator, negZ, subZ, smulZ, paraSymplecticK0, sheetU, sheetV]; ring)
  · unfold wittenMoebiusAngle
    rw [hCosHalf, hSinHalf,
        (wittenMoebius_clifford_square_and_supertrace (Real.cos (2 * θ)) (Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃).2.2.1,
        (wittenMoebius_clifford_square_and_supertrace (-Real.cos (2 * θ)) (-Real.sin (2 * θ)) u₁ u₂ u₃ v₁ v₂ v₃).2.2.1]
    ring

end RealKleinBottleVacuum

end InfoGeometry.Superalgebra.WittenMoebiusParity
