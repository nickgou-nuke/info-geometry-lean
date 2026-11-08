/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.SplitQ44
import InfoGeometry.Clifford.Cl44Witt
import InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry

/-!
# Topological KMS Flow and the Modular Automorphism Group

This module constructs the continuous one-parameter modular automorphism group
`modularFlow` as an `AlgEquiv` on the split-signature Clifford algebra `Cl(4,4)`
via `CliffordAlgebra.equivOfIsometry` applied to the exact pseudo-orthogonal
Lorentz boost isometry `boostIsometryEquiv` of the null Witt basis.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Clifford.SplitQ44`: `splitQ44`, `Cl44`.
  * `InfoGeometry.Clifford.Cl44Witt`: `aVec`, `adagVec`, `eVec`, `fVec`.
  * `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`: `CliffordAlgebra.equivOfIsometry`.
- BUCKET 2 (Deconfabulation):
  * Replaced the file-level section hypothesis `variable (E μ : Fin 4 → ℝ)` with
    explicit `(E μ : Fin 4 → ℝ)` arguments on each declaration, preserving exact
    elaborated parameter order.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `ω`, `boostFun`, `boostIsometryEquiv`, `modularFlow`.
  * `boostFun_zero`, `boostFun_comp`, `continuous_boostFun`, `boostFun_add`,
    `boostFun_smul`, `boostFun_preserves_Q`.
  * `modularFlow_aVec`, `modularFlow_adagVec`: exponential hyperbolic scaling of
    the Witt annihilation and creation vectors under `boostFun`.
-/

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44Witt
open InfoGeometry.Clifford.ChiralGrandCanonicalOperatorGeometry
open CliffordAlgebra

noncomputable section

namespace InfoGeometry.Canonical.TopologicalKMSFlow

/-- The grand-canonical mode frequency $\omega_i = E_i - \mu_i$ for each mode $i \in \mathrm{Fin}\,4$. -/
noncomputable def ω (E μ : Fin 4 → ℝ) (i : Fin 4) : ℝ := E i - μ i

/-- The continuous pseudo-orthogonal Lorentz boost evolution on $V_{4,4} = \mathbb{R}^8$. -/
noncomputable def boostFun (E μ : Fin 4 → ℝ) (t : ℝ) (x : Fin 8 → ℝ) : Fin 8 → ℝ
  | 0 => Real.cosh (t * ω E μ 0) * x 0 - Real.sinh (t * ω E μ 0) * x 4
  | 1 => Real.cosh (t * ω E μ 1) * x 1 - Real.sinh (t * ω E μ 1) * x 5
  | 2 => Real.cosh (t * ω E μ 2) * x 2 - Real.sinh (t * ω E μ 2) * x 6
  | 3 => Real.cosh (t * ω E μ 3) * x 3 - Real.sinh (t * ω E μ 3) * x 7
  | 4 => -Real.sinh (t * ω E μ 0) * x 0 + Real.cosh (t * ω E μ 0) * x 4
  | 5 => -Real.sinh (t * ω E μ 1) * x 1 + Real.cosh (t * ω E μ 1) * x 5
  | 6 => -Real.sinh (t * ω E μ 2) * x 2 + Real.cosh (t * ω E μ 2) * x 6
  | 7 => -Real.sinh (t * ω E μ 3) * x 3 + Real.cosh (t * ω E μ 3) * x 7

/-- At $t = 0$, the boost flow acts as the identity on $\mathbb{R}^8$. -/
theorem boostFun_zero (E μ : Fin 4 → ℝ) (x : Fin 8 → ℝ) :
    boostFun E μ 0 x = x := by
  ext j
  fin_cases j <;> simp [boostFun]

/-- One-parameter group composition law for the Lorentz boost flow:
$\mathrm{boost}_t(\mathrm{boost}_s(x)) = \mathrm{boost}_{t+s}(x)$. -/
theorem boostFun_comp (E μ : Fin 4 → ℝ) (s t : ℝ) (x : Fin 8 → ℝ) :
    boostFun E μ t (boostFun E μ s x) = boostFun E μ (t + s) x := by
  ext j
  fin_cases j <;>
    simp [boostFun, Real.cosh_add, Real.sinh_add, add_mul,
      mul_add, sub_eq_add_neg] <;> ring

/-- Continuity of the trajectory $t \mapsto \mathrm{boostFun}(E, \mu, t, x)$. -/
theorem continuous_boostFun (E μ : Fin 4 → ℝ) (x : Fin 8 → ℝ) :
    Continuous (fun t : ℝ => boostFun E μ t x) := by
  refine continuous_pi fun j => ?_
  fin_cases j <;> simp only [boostFun]
  all_goals fun_prop

/-- Additivity of `boostFun E μ t` on $\mathbb{R}^8$. -/
lemma boostFun_add (E μ : Fin 4 → ℝ) (t : ℝ) (x y : Fin 8 → ℝ) :
    boostFun E μ t (x + y) = boostFun E μ t x + boostFun E μ t y := by
  ext j; fin_cases j <;> simp [boostFun, Pi.add_apply] <;> ring

/-- Real-scalar homogeneity of `boostFun E μ t` on $\mathbb{R}^8$. -/
lemma boostFun_smul (E μ : Fin 4 → ℝ) (t c : ℝ) (x : Fin 8 → ℝ) :
    boostFun E μ t (c • x) = c • boostFun E μ t x := by
  ext j; fin_cases j <;> simp [boostFun, Pi.smul_apply] <;> ring

/-- The continuous boost evolution preserves the split quadratic form `splitQ44`. -/
theorem boostFun_preserves_Q (E μ : Fin 4 → ℝ) (t : ℝ) (x : Fin 8 → ℝ) :
    splitQ44 (boostFun E μ t x) = splitQ44 x := by
  have h0 : Real.cosh (t * ω E μ 0) ^ 2 - Real.sinh (t * ω E μ 0) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (t * ω E μ 0)
  have h1 : Real.cosh (t * ω E μ 1) ^ 2 - Real.sinh (t * ω E μ 1) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (t * ω E μ 1)
  have h2 : Real.cosh (t * ω E μ 2) ^ 2 - Real.sinh (t * ω E μ 2) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (t * ω E μ 2)
  have h3 : Real.cosh (t * ω E μ 3) ^ 2 - Real.sinh (t * ω E μ 3) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (t * ω E μ 3)
  simp [splitQ44_apply, boostFun]
  calc
    (Real.cosh (t * ω E μ 0) * x 0 - Real.sinh (t * ω E μ 0) * x 4) *
            (Real.cosh (t * ω E μ 0) * x 0 - Real.sinh (t * ω E μ 0) * x 4) +
          (Real.cosh (t * ω E μ 1) * x 1 - Real.sinh (t * ω E μ 1) * x 5) *
            (Real.cosh (t * ω E μ 1) * x 1 - Real.sinh (t * ω E μ 1) * x 5) +
        (Real.cosh (t * ω E μ 2) * x 2 - Real.sinh (t * ω E μ 2) * x 6) *
          (Real.cosh (t * ω E μ 2) * x 2 - Real.sinh (t * ω E μ 2) * x 6) +
      (Real.cosh (t * ω E μ 3) * x 3 - Real.sinh (t * ω E μ 3) * x 7) *
        (Real.cosh (t * ω E μ 3) * x 3 - Real.sinh (t * ω E μ 3) * x 7) -
    ((-(Real.sinh (t * ω E μ 0) * x 0) + Real.cosh (t * ω E μ 0) * x 4) *
            (-(Real.sinh (t * ω E μ 0) * x 0) + Real.cosh (t * ω E μ 0) * x 4) +
          (-(Real.sinh (t * ω E μ 1) * x 1) + Real.cosh (t * ω E μ 1) * x 5) *
            (-(Real.sinh (t * ω E μ 1) * x 1) + Real.cosh (t * ω E μ 1) * x 5) +
        (-(Real.sinh (t * ω E μ 2) * x 2) + Real.cosh (t * ω E μ 2) * x 6) *
          (-(Real.sinh (t * ω E μ 2) * x 2) + Real.cosh (t * ω E μ 2) * x 6) +
      (-(Real.sinh (t * ω E μ 3) * x 3) + Real.cosh (t * ω E μ 3) * x 7) *
        (-(Real.sinh (t * ω E μ 3) * x 3) + Real.cosh (t * ω E μ 3) * x 7))
    = (Real.cosh (t * ω E μ 0) ^ 2 - Real.sinh (t * ω E μ 0) ^ 2) * (x 0 * x 0 - x 4 * x 4) +
      (Real.cosh (t * ω E μ 1) ^ 2 - Real.sinh (t * ω E μ 1) ^ 2) * (x 1 * x 1 - x 5 * x 5) +
      (Real.cosh (t * ω E μ 2) ^ 2 - Real.sinh (t * ω E μ 2) ^ 2) * (x 2 * x 2 - x 6 * x 6) +
      (Real.cosh (t * ω E μ 3) ^ 2 - Real.sinh (t * ω E μ 3) ^ 2) * (x 3 * x 3 - x 7 * x 7) := by ring
    _ = 1 * (x 0 * x 0 - x 4 * x 4) + 1 * (x 1 * x 1 - x 5 * x 5) +
        1 * (x 2 * x 2 - x 6 * x 6) + 1 * (x 3 * x 3 - x 7 * x 7) := by rw [h0, h1, h2, h3]
    _ = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 - (x 4 * x 4 + x 5 * x 5 + x 6 * x 6 + x 7 * x 7) := by ring

/-- The boost function packaged as a quadratic-form isometry equivalence on `splitQ44`. -/
noncomputable def boostIsometryEquiv (E μ : Fin 4 → ℝ) (t : ℝ) :
    QuadraticMap.IsometryEquiv splitQ44 splitQ44 where
  toFun := boostFun E μ t
  invFun := boostFun E μ (-t)
  map_add' := boostFun_add E μ t
  map_smul' := boostFun_smul E μ t
  left_inv x := by
    rw [boostFun_comp E μ t (-t) x, neg_add_cancel, boostFun_zero E μ x]
  right_inv x := by
    rw [boostFun_comp E μ (-t) t x, add_neg_cancel, boostFun_zero E μ x]
  map_app' x := boostFun_preserves_Q E μ t x

/-- The continuous one-parameter modular automorphism group (KMS flow) on `Cl(4,4)`. -/
noncomputable def modularFlow (E μ : Fin 4 → ℝ) (t : ℝ) : Cl44 ≃ₐ[ℝ] Cl44 :=
  CliffordAlgebra.equivOfIsometry (boostIsometryEquiv E μ t)

/-- The boost flow scales the Witt annihilation vectors `aVec i` by $\cosh(t\omega_i) - \sinh(t\omega_i)$. -/
theorem modularFlow_aVec (E μ : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    boostFun E μ t (aVec i) = (Real.cosh (t * ω E μ i) - Real.sinh (t * ω E μ i)) • aVec i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [boostFun, aVec, eVec, fVec, Pi.smul_apply, Pi.add_apply, Real.cosh_eq, Real.sinh_eq] <;> ring

/-- The boost flow scales the Witt creation vectors `adagVec i` by $\cosh(t\omega_i) + \sinh(t\omega_i)$. -/
theorem modularFlow_adagVec (E μ : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    boostFun E μ t (adagVec i) = (Real.cosh (t * ω E μ i) + Real.sinh (t * ω E μ i)) • adagVec i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [boostFun, adagVec, eVec, fVec, Pi.smul_apply, Pi.sub_apply, Real.cosh_eq, Real.sinh_eq] <;> ring

end InfoGeometry.Canonical.TopologicalKMSFlow
