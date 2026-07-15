import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Canonical.TrifactorDecomposition

/-!
# Trifactor-Zeta Bridge

This module records the algebraic part of the proposed tripotent reformulation:
for a tripotent sector operator, a state with vanishing active support lies in
the null/vacuum projector `P_zero`.

It does **not** prove the Riemann Hypothesis.  The analytic assertion that
Riemann zero-modes have vanishing active support remains an explicit field of
the mode structure.  The closed theorem here is the finite polynomial
projector algebra once that field is supplied.
-/

noncomputable section

namespace TrifactorZetaBridge

open TrifactorDecomposition
open RiemannZetaEquivalences

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-! ## Pure tripotent projector algebra -/

/-- The active projector `P_plus + P_minus` is exactly `T^2`. -/
theorem active_projectors_sum_eq_square (T : R) :
    P_plus T + P_minus T = T ^ 2 := by
  unfold P_plus P_minus TriFacetGeometry.P_hyp TriFacetGeometry.P_ell
  calc
    ⅟(2 : R) * (T ^ 2 + T) + ⅟(2 : R) * (T ^ 2 - T) =
        (⅟(2 : R) * (2 : R)) * T ^ 2 := by ring
    _ = 1 * T ^ 2 := by rw [invOf_mul_self (2 : R)]
    _ = T ^ 2 := by ring

/--
If the active plus/minus support of a state vanishes, the state is fixed by the
null/vacuum projector.
-/
theorem vacuum_sector_of_active_support_zero (T ρ : R)
    (hActive : (P_plus T + P_minus T) * ρ = 0) :
    P_zero T * ρ = ρ := by
  calc
    P_zero T * ρ = P_zero T * ρ + 0 := by ring
    _ = P_zero T * ρ + (P_plus T + P_minus T) * ρ := by rw [hActive]
    _ = (P_zero T + P_plus T + P_minus T) * ρ := by ring
    _ = 1 * ρ := by rw [partition_of_unity T]
    _ = ρ := by ring

/-- The square-zero active-support condition is the same null-sector condition. -/
theorem vacuum_sector_of_square_zero (T ρ : R) (hSquare : T ^ 2 * ρ = 0) :
    P_zero T * ρ = ρ := by
  apply vacuum_sector_of_active_support_zero T ρ
  rwa [active_projectors_sum_eq_square T]

/-- Vanishing of both chiral components implies vacuum-sector localization. -/
theorem vacuum_sector_of_active_components_zero (T ρ : R)
    (hPlus : P_plus T * ρ = 0) (hMinus : P_minus T * ρ = 0) :
    P_zero T * ρ = ρ := by
  apply vacuum_sector_of_active_support_zero T ρ
  calc
    (P_plus T + P_minus T) * ρ = P_plus T * ρ + P_minus T * ρ := by ring
    _ = 0 + 0 := by rw [hPlus, hMinus]
    _ = 0 := by ring

/-! ## Zeta-facing conditional mode surface -/

/--
A zeta-facing tripotent mode.

`activeSupportZero` is the explicit analytic/physical hypothesis.  Supplying it
is exactly the nontrivial content; the theorem below only performs the finite
trifactor projection once it is available.
-/
structure TrifactorZetaMode (T state z : ℂ) where
  tripotent : T ^ 3 = T
  centeredXiZero : symmetryAdaptedXi z = 0
  activeSupportZero : (P_plus T + P_minus T) * state = 0

/-- Completed-xi parity reflects a centered zero to its `J`-mirror. -/
theorem centeredXi_zero_reflected {z : ℂ} (hz : symmetryAdaptedXi z = 0) :
    symmetryAdaptedXi (-z) = 0 := by
  simpa [symmetryAdaptedXi_is_even z] using hz

/-- A `TrifactorZetaMode` carries its reflected completed-xi zero. -/
theorem trifactorZetaMode_reflected_zero {T state z : ℂ}
    (M : TrifactorZetaMode T state z) :
    symmetryAdaptedXi (-z) = 0 :=
  centeredXi_zero_reflected M.centeredXiZero

/--
Conditional null-state theorem: if a zeta-facing mode has vanishing active
trifactor support, then it is localized in the `P_zero` vacuum sector.
-/
theorem trifactorZetaMode_in_vacuum_sector {T state z : ℂ}
    (M : TrifactorZetaMode T state z) :
    P_zero T * state = state :=
  vacuum_sector_of_active_support_zero T state M.activeSupportZero

end TrifactorZetaBridge
