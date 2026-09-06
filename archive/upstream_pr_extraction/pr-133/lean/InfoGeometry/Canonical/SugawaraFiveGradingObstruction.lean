import Mathlib.Tactic
import InfoGeometry.External.Virasoro.Sugawara
import InfoGeometry.External.Virasoro.FiveGradedDecomposition

/-!
# Sugawara obstruction to a naive five-mode truncation

The imported Sugawara theorem proves

`[L_n, J_m] = -m J_{n+m}`.

Consequently the assignment

* `L₁` to grade `+2`,
* `J₁` to grade `+1`,

cannot satisfy the boundary-zero law of a truncated five-grading unless the
next current mode `J₂` vanishes in the chosen representation or quotient.

This file records that obstruction exactly.  It does not construct a quotient,
a finite conformal truncation, or an identification with the nuclear
five-grading.
-/

noncomputable section

namespace InfoGeometry.Canonical.SugawaraFiveGradingObstruction

open Filter
open VirasoroProject

variable {𝕜 V : Type*}
variable [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

variable (J : ℤ → V →ₗ[𝕜] V)
variable (trunc : ∀ v, atTop.Eventually (fun l => J l v = 0))
variable (hcomm : ∀ m n,
  (J m).commutator (J n) =
    if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0)

include hcomm

/-- The exact Sugawara current-action law, re-exposed on the owner surface. -/
theorem sugawara_current_mode_shift (n m : ℤ) :
    (sugawaraGen trunc n).commutator (J m) =
      -m • J (n + m) := by
  exact commutator_sugawaraGen_heiOper
    (heiOper := J) (heiTrunc := trunc) (heiComm := hcomm) n m

/-- At the first positive modes, the mixed bracket exits the five-mode window. -/
theorem positive_one_one_commutator :
    (sugawaraGen trunc 1).commutator (J 1) = -J 2 := by
  have h := sugawara_current_mode_shift J trunc hcomm (1 : ℤ) (1 : ℤ)
  simpa using h

/-- If a proposed truncated grading forces `[L₁,J₁]=0`, then `J₂` must vanish. -/
theorem boundary_zero_forces_current_two_zero
    (hzero : (sugawaraGen trunc 1).commutator (J 1) = 0) :
    J 2 = 0 := by
  rw [positive_one_one_commutator J trunc hcomm] at hzero
  exact neg_eq_zero.mp hzero

/-- A nonzero `J₂` obstructs the naive boundary-zero five-grading. -/
theorem current_two_ne_zero_obstructs_boundary_zero
    (hJ2 : J 2 ≠ 0) :
    (sugawaraGen trunc 1).commutator (J 1) ≠ 0 := by
  rw [positive_one_one_commutator J trunc hcomm]
  exact neg_ne_zero.mpr hJ2

/--
The obstruction stated as an incompatibility criterion: one cannot have both
nonzero `J₂` and the truncated boundary relation `[L₁,J₁]=0`.
-/
theorem no_naive_positive_boundary_truncation
    (hJ2 : J 2 ≠ 0) :
    ¬ ((sugawaraGen trunc 1).commutator (J 1) = 0) :=
  current_two_ne_zero_obstructs_boundary_zero J trunc hcomm hJ2

/--
More generally, the positive Sugawara mode `L_n` shifts a current mode `J_m`
to `J_{n+m}` with coefficient `-m`.  Any finite truncation must therefore
supply an explicit quotient/vanishing law for modes that leave its window.
-/
theorem mode_escape_formula
    {n m : ℤ} :
    (sugawaraGen trunc n).commutator (J m) =
      -m • J (n + m) :=
  sugawara_current_mode_shift J trunc hcomm n m

end InfoGeometry.Canonical.SugawaraFiveGradingObstruction
