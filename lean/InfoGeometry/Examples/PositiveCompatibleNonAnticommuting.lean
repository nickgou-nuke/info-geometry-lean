/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.HypercomplexTriad
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Positive compatibility does not force anticommutation

Reuse the actual real matrices `I`, `E`, and `N` from `HypercomplexTriad`.
The family `K_b = E + b N` is an antisymplectic involution for every real `b`.
The right contraction of the standard symplectic form by `I` is the positive
dot product, but `I K_b + K_b I = b * identity`. Thus every nonzero parameter
is a concrete counterexample to an asserted implication from positivity to
anticommutation. Both products are full matrix products.
-/

noncomputable section

namespace InfoGeometry.Examples.PositiveCompatibleNonAnticommuting

open Matrix InfoGeometry.Algebra.HypercomplexTriad

/-- The standard real skew form, with matrix `-I` in the existing convention. -/
def omega : LinearMap.BilinForm ℝ (Fin 2 → ℝ) := Matrix.toBilin' (-I)

theorem omega_apply (u v : Fin 2 → ℝ) :
    omega u v = u 0 * v 1 - u 1 * v 0 := by
  simp [omega, Matrix.toBilin'_apply, I, Fin.sum_univ_two, sub_eq_add_neg]

theorem omega_alternating : omega.IsAlt := by
  intro u
  rw [omega_apply, mul_comm (u 1) (u 0), sub_self]

theorem omega_nondegenerate : omega.Nondegenerate := by
  constructor
  · intro u hu
    funext i
    fin_cases i
    · simpa [omega_apply] using hu ![0, 1]
    · simpa [omega_apply] using hu ![1, 0]
  · intro v hv
    funext i
    fin_cases i
    · simpa [omega_apply] using hv ![0, 1]
    · simpa [omega_apply] using hv ![1, 0]

/-- Reuses the elliptic generator of the canonical two-dimensional owner. -/
theorem omega_I_preserved (u v : Fin 2 → ℝ) :
    omega (I *ᵥ u) (I *ᵥ v) = omega u v := by
  simp [omega_apply, I, Matrix.mulVec, dotProduct, Fin.sum_univ_two, neg_sub_neg]

/-- The right-slot metric is exactly the ordinary positive real dot product. -/
theorem omega_I_metric (u v : Fin 2 → ℝ) :
    omega u (I *ᵥ v) = dotProduct u v := by
  simp [omega_apply, I, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem omega_I_pos (u : Fin 2 → ℝ) (hu : u ≠ 0) :
    0 < omega u (I *ᵥ u) := by
  rw [omega_I_metric]
  have hn : 0 ≤ dotProduct u u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  exact lt_of_le_of_ne hn (fun hz => hu (dotProduct_self_eq_zero.mp hz.symm))

/-- A real sheared product structure on the same full two-dimensional carrier. -/
def shearedPara (b : ℝ) : Mat2 := E + b • N

theorem shearedPara_mulVec (b : ℝ) (u : Fin 2 → ℝ) :
    shearedPara b *ᵥ u = ![u 0 + b * u 1, -u 1] := by
  ext i
  fin_cases i <;> simp [shearedPara, E, N, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem shearedPara_sq (b : ℝ) : shearedPara b * shearedPara b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearedPara, E, N, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearedPara_antisymplectic (b : ℝ) (u v : Fin 2 → ℝ) :
    omega (shearedPara b *ᵥ u) (shearedPara b *ᵥ v) = -omega u v := by
  have hm : (shearedPara b)ᵀ * (-I) * shearedPara b = -(-I) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shearedPara, E, N, I, Matrix.mul_apply, Fin.sum_univ_two]
  change ((Matrix.toBilin' (-I)).comp (shearedPara b).toLin'
    (shearedPara b).toLin') u v = -(Matrix.toBilin' (-I) u v)
  rw [Matrix.toBilin'_comp, hm]
  simp only [map_neg, LinearMap.neg_apply]

/-- An exact matrix identity, rather than an inference from noncommutativity. -/
theorem shearedPara_anticommutator (b : ℝ) :
    I * shearedPara b + shearedPara b * I = b • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearedPara, I, E, N, Matrix.mul_apply, Fin.sum_univ_two]

theorem shearedPara_anticommutes_iff (b : ℝ) :
    I * shearedPara b = -(shearedPara b * I) ↔ b = 0 := by
  constructor
  · intro h
    have hz : b • (1 : Mat2) = 0 := by
      rw [← shearedPara_anticommutator, h, neg_add_cancel]
    have h00 := congrArg (fun A : Mat2 => A 0 0) hz
    simpa using h00
  · intro hb
    subst b
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [shearedPara, I, E, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Commuting is also impossible; it is a different condition from anticommuting. -/
theorem shearedPara_not_commute (b : ℝ) :
    I * shearedPara b ≠ shearedPara b * I := by
  intro h
  have h01 := congrArg (fun A : Mat2 => A 0 1) h
  norm_num [shearedPara, I, E, N, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The fixed line is exactly the first coordinate line, for every parameter. -/
theorem shearedPara_fixed_iff (b : ℝ) (u : Fin 2 → ℝ) :
    shearedPara b *ᵥ u = u ↔ u 1 = 0 := by
  rw [shearedPara_mulVec]
  constructor
  · intro h
    have h1 := congrFun h 1
    change -u 1 = u 1 at h1
    linarith
  · intro hu
    ext i
    fin_cases i <;> simp [hu]

/-- The other eigenspace is a genuine line, not a collapsed zero factor. -/
theorem shearedPara_antifixed_iff (b : ℝ) (u : Fin 2 → ℝ) :
    shearedPara b *ᵥ u = -u ↔ u 0 = -(b / 2) * u 1 := by
  rw [shearedPara_mulVec]
  constructor
  · intro h
    have h0 := congrFun h 0
    change u 0 + b * u 1 = -u 0 at h0
    linarith
  · intro hu
    ext i
    fin_cases i
    · simp only [Matrix.cons_val_zero, Pi.neg_apply]
      rw [hu]
      ring
    · simp

end InfoGeometry.Examples.PositiveCompatibleNonAnticommuting
