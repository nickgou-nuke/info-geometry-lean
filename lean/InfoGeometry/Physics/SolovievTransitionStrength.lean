import Mathlib
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

noncomputable section

namespace InfoGeometry.Physics.SolovievTransitionStrength

open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open Matrix

abbrev Observable := Hamiltonian

/-! A finite transition readout.  The observable and the two states are
explicit inputs; no weak-interaction or spectroscopic interpretation is
assumed here. -/

def amplitude (O : Observable) (initial final : Carrier) : ℝ :=
  dotProduct final (O.mulVec initial)

def strength (O : Observable) (initial final : Carrier) : ℝ :=
  amplitude O initial final ^ 2

theorem strength_nonneg (O : Observable) (initial final : Carrier) :
    0 ≤ strength O initial final := by
  exact sq_nonneg _

theorem strength_eq_zero_iff (O : Observable) (initial final : Carrier) :
    strength O initial final = 0 ↔ amplitude O initial final = 0 := by
  exact sq_eq_zero_iff

theorem amplitude_entries (O : Observable) (initial final : Carrier) :
    amplitude O initial final =
      final 0 * (O 0 0 * initial 0 + O 0 1 * initial 1) +
      final 1 * (O 1 0 * initial 0 + O 1 1 * initial 1) := by
  simp [amplitude, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end InfoGeometry.Physics.SolovievTransitionStrength
