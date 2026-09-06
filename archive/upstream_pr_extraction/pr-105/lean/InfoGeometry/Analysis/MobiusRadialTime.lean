import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Möbius inversion and logarithmic radial time

This file records the exact elementary statements behind the radial-time
interpretation of complex inversion.  It also records the obstruction to a
frequent invalid inference: an inversion-invariant set need not be contained
in the unit circle, because inversion can exchange two distinct points.
-/

noncomputable section

namespace InfoGeometry.Analysis.MobiusRadialTime

/-- Logarithmic radial coordinate on `ℂ`. -/
def radialLogTime (z : ℂ) : ℝ :=
  Real.log ‖z‖

/-- Complex inversion reverses logarithmic radial time. -/
@[simp]
theorem radialLogTime_inv (z : ℂ) :
    radialLogTime z⁻¹ = -radialLogTime z := by
  simp [radialLogTime]

/-- Inversion exchanges the inside and outside logarithmic half-spaces. -/
theorem radialLogTime_inv_pos_iff (z : ℂ) :
    0 < radialLogTime z⁻¹ ↔ radialLogTime z < 0 := by
  rw [radialLogTime_inv]
  exact neg_pos

/-- Equality of a real growth mode and its time reverse forces zero rate or zero time. -/
theorem exp_growth_eq_timeReverse_iff (sigma t : ℝ) :
    Real.exp (sigma * t) = Real.exp (-sigma * t) ↔
      sigma = 0 ∨ t = 0 := by
  rw [Real.exp_injective.eq_iff]
  constructor
  · intro h
    apply mul_eq_zero.mp
    linarith
  · rintro (hsigma | ht)
    · simp [hsigma]
    · simp [ht]

/-- The reciprocal orbit of a complex point. -/
def reciprocalOrbit (z : ℂ) : Set ℂ :=
  {z, z⁻¹}

/-- A reciprocal orbit is invariant under inversion. -/
theorem inv_mem_reciprocalOrbit
    {z w : ℂ}
    (hw : w ∈ reciprocalOrbit z) :
    w⁻¹ ∈ reciprocalOrbit z := by
  rcases hw with (rfl | rfl)
  · exact Or.inr rfl
  · simpa [reciprocalOrbit] using (show z ∈ reciprocalOrbit z from Or.inl rfl)

/-- The reciprocal orbit of `2` is inversion-invariant but contains an off-circle point. -/
theorem inversion_invariant_orbit_not_subset_unitCircle :
    (∀ w ∈ reciprocalOrbit (2 : ℂ), w⁻¹ ∈ reciprocalOrbit (2 : ℂ)) ∧
      ∃ w ∈ reciprocalOrbit (2 : ℂ), ‖w‖ ≠ 1 := by
  constructor
  · intro w hw
    exact inv_mem_reciprocalOrbit hw
  · refine ⟨(2 : ℂ), Or.inl rfl, ?_⟩
    norm_num

/--
Consequently, setwise inversion invariance does not imply pointwise
unit-circle localization.
-/
theorem inversion_invariance_does_not_force_unitCircle :
    ¬ (∀ K : Set ℂ,
        (∀ z ∈ K, z⁻¹ ∈ K) →
        ∀ z ∈ K, ‖z‖ = 1) := by
  intro h
  obtain ⟨hinv, w, hw, hnorm⟩ :=
    inversion_invariant_orbit_not_subset_unitCircle
  exact hnorm (h (reciprocalOrbit (2 : ℂ)) hinv w hw)

end InfoGeometry.Analysis.MobiusRadialTime
