/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The positive Gram bound for the internal doubled phase

This low-level owner contains the Bessel argument formerly owned by
`Canonical.OperatorialUncertainty`.  The canonical layer forwards its
historical API here.  The proof uses only the positive doubled Hilbert
pairing, the native isometry `complex_i`, and a two-vector orthonormal family.
It imposes no indefinite probability interpretation or operator commutation
relation.
-/

noncomputable section

namespace InfoGeometry.Krein.InternalPhaseGram

open scoped InnerProductSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "Iop" => complex_i (E := E)

/-- The native internal phase defines an alternating real bilinear pairing. -/
theorem phase_pair_neg_swap (x y : H₂) :
    ⟪Iop x, y⟫_ℝ = -⟪Iop y, x⟫_ℝ := by
  simp [complex_i, modular_j, spectral_epsilon, WithLp.prod_inner_apply,
    real_inner_comm, add_comm]

theorem phase_pair_self_zero (x : H₂) :
    ⟪Iop x, x⟫_ℝ = 0 := by
  have h := phase_pair_neg_swap x x
  linarith

/-- The real and internal-phase Gram components obey the full two-vector
Bessel bound.  This is the original canonical uncertainty argument moved to
its minimal geometric owner. -/
theorem inner_sq_add_phase_inner_sq_le (x y : H₂) :
    (⟪x, y⟫_ℝ) ^ 2 + (⟪Iop x, y⟫_ℝ) ^ 2 ≤
      ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  let kx : H₂ := Iop x
  have hKnorm : ‖kx‖ = ‖x‖ := complex_i_norm x
  have hNormNe : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hkx : kx ≠ 0 := by
    have hKnormNe : ‖kx‖ ≠ 0 := by
      rw [hKnorm]
      exact hNormNe
    exact norm_ne_zero_iff.mp hKnormNe
  have hOrth : ⟪x, kx⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact phase_pair_self_zero x
  have hOrthNorm :
      ⟪NormedSpace.normalize x, NormedSpace.normalize kx⟫_ℝ = 0 := by
    rw [NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_right, hOrth]
    ring
  let v : Fin 2 → H₂ := ![NormedSpace.normalize x, NormedSpace.normalize kx]
  have hv : Orthonormal ℝ v := by
    constructor
    · intro i
      fin_cases i
      · simpa [v] using NormedSpace.norm_normalize hx
      · simpa [v] using NormedSpace.norm_normalize hkx
    · intro i j hij
      fin_cases i <;> fin_cases j
      · contradiction
      · simpa [v] using hOrthNorm
      · simpa [v, real_inner_comm] using hOrthNorm
      · contradiction
  have hBessel :
      ‖⟪NormedSpace.normalize x, y⟫_ℝ‖ ^ 2 +
          ‖⟪NormedSpace.normalize kx, y⟫_ℝ‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    simpa [v] using hv.sum_inner_products_le (x := y) (s := Finset.univ)
  have hScaled :=
    mul_le_mul_of_nonneg_left hBessel (by positivity : 0 ≤ ‖x‖ ^ 2)
  have hLhs :
      ‖x‖ ^ 2 *
          (‖⟪NormedSpace.normalize x, y⟫_ℝ‖ ^ 2 +
            ‖⟪NormedSpace.normalize kx, y⟫_ℝ‖ ^ 2) =
        (⟪x, y⟫_ℝ) ^ 2 + (⟪kx, y⟫_ℝ) ^ 2 := by
    rw [NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_left]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hKnorm]
    field_simp [pow_two, hNormNe]
  rw [hLhs] at hScaled
  simpa only [kx] using hScaled

end InfoGeometry.Krein.InternalPhaseGram
