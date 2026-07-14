import Mathlib
import InfoGeometry.Algebra.HypercomplexTriad

/-!
# InfoGeometry.Canonical.NilpotentFluxVirasoroReadout

Concrete local bridge readout from the nilpotent cross-flux seed to the
`c = 1` Virasoro central coefficient.

This file is intentionally finite-dimensional and local:
it does not claim a global infinite-mode identification theorem.
-/

noncomputable section

namespace NilpotentFluxVirasoroReadout

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- Local `2×2` trace. -/
def tr2 (A : Mat2) : ℝ := A 0 0 + A 1 1

/-- Local nilpotent cross-flux seed (`N ⊗ N` readout proxy at the matrix seed level). -/
def nilpotentCrossFlux : Mat2 := N * Nᵀ

/-- Scalar charge extracted from the local cross-flux seed. -/
def nilpotentFluxCharge : ℝ := tr2 nilpotentCrossFlux

/--
The local cross-flux seed has unit charge.

This gives a concrete finite witness for the `c = 1` normalization at the
`2×2` seed level.
-/
theorem nilpotentFluxCharge_eq_one : nilpotentFluxCharge = 1 := by
  unfold nilpotentFluxCharge tr2 nilpotentCrossFlux
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Central-coefficient readout induced by the local nilpotent cross-flux charge. -/
def nilpotentFluxCentralCoefficient (m n : Int) : ℝ :=
  if m + n = 0 then nilpotentFluxCharge * (((m ^ 3 - m : Int) : ℝ) / 12) else 0

/--
With unit local charge, the induced coefficient matches the standard Virasoro
`c = 1` coefficient formula.
-/
theorem nilpotentFluxCentralCoefficient_eq_virasoro (m n : Int) :
    nilpotentFluxCentralCoefficient m n =
      (if m + n = 0 then (((m ^ 3 - m : Int) : ℝ) / 12) else 0) := by
  unfold nilpotentFluxCentralCoefficient
  by_cases hmn : m + n = 0
  · simp [hmn, nilpotentFluxCharge_eq_one]
  · simp [hmn]

/--
Global conformal mode readout: the induced central coefficient vanishes for
`m = -1, 0, 1`.
-/
theorem nilpotentFluxCentralCoefficient_zero_of_global_mode
    {m n : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    nilpotentFluxCentralCoefficient m n = 0 := by
  rw [nilpotentFluxCentralCoefficient_eq_virasoro]
  rcases hm with hm | hm | hm
  · subst m
    by_cases hmn : (-1 : Int) + n = 0
    · simp [hmn]
    · simp [hmn]
  · subst m
    by_cases hmn : (0 : Int) + n = 0
    · norm_num [hmn]
    · simp
  · subst m
    by_cases hmn : (1 : Int) + n = 0
    · norm_num [hmn]
    · simp [hmn]

/--
Algebraic factorization of the Virasoro cubic polynomial:
`m^3 - m = m (m - 1) (m + 1)`.
-/
theorem virasoro_cubic_factor (m : Int) :
    (((m ^ 3 - m : Int) : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) + 1) := by
  norm_num
  ring

/--
Global-mode vanishing of the cubic coefficient from factorization alone.
-/
theorem virasoro_cubic_zero_of_global_mode
    {m : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    (((m ^ 3 - m : Int) : ℝ)) = 0 := by
  rw [virasoro_cubic_factor]
  rcases hm with hm | hm | hm <;> subst m <;> norm_num

/--
Equivalent global-mode vanishing statement for the normalized coefficient.
-/
theorem virasoro_coefficient_zero_of_global_mode
    {m : Int}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    (((m ^ 3 - m : Int) : ℝ) / 12) = 0 := by
  rw [virasoro_cubic_zero_of_global_mode hm]
  norm_num

end NilpotentFluxVirasoroReadout
