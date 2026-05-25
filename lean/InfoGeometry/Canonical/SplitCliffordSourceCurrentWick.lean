import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordSourceCurrent

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

Wick/Schwinger commutator interface for split source currents.

This file records the endomorphism-valued commutator theorem required by the
Heisenberg bridge. Carrier-valued source currents must first be transported to
endomorphisms of the source vector space; only then does the commutator make
sense.

No closure is postulated here. The equation below remains a theorem debt for a
concrete transported current family.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/--
Endomorphism-valued Wick/Schwinger commutator law.

This is the exact commutator equation required by the Heisenberg bridge.
Carrier-valued currents `V → Carrier` are intentionally not accepted here,
because their associative commutator is not defined without transport back to
`End(V)`.
-/
def SplitSourceEndWickLaw
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (Jlift : Int → V →ₗ[𝕜] V) : Prop :=
  ∀ m n : Int,
    (Jlift m).commutator (Jlift n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0

/-- Backward-compatible name for the endomorphism-valued Wick law. -/
abbrev SplitSourceWickLaw := @SplitSourceEndWickLaw

/--
Off-diagonal Wick readout: if `m + n ≠ 0`, the commutator vanishes.
-/
theorem commutator_eq_zero_of_add_ne_zero
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    {Jlift : Int → V →ₗ[𝕜] V}
    (hWick : SplitSourceEndWickLaw Jlift)
    {m n : Int} (hmn : m + n ≠ 0) :
    (Jlift m).commutator (Jlift n) = 0 := by
  simpa [SplitSourceEndWickLaw, hmn] using hWick m n

/--
Diagonal Wick readout: if `m + n = 0`, the commutator is the central term.
-/
theorem commutator_eq_central_of_add_eq_zero
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    {Jlift : Int → V →ₗ[𝕜] V}
    (hWick : SplitSourceEndWickLaw Jlift)
    {m n : Int} (hmn : m + n = 0) :
    (Jlift m).commutator (Jlift n) = (m : 𝕜) • (1 : V →ₗ[𝕜] V) := by
  simpa [SplitSourceEndWickLaw, hmn] using hWick m n

/--
Honest raw-CAR corollary: the completed normal-ordered current bracket has the
Heisenberg central coefficient.
-/
theorem completed_current_commutator_from_rawCAR
    {A : Type*} [Ring A]
    (C : _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeCompletion A)
    (m n : Int) :
    _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted
        C
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
        (_root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n)
      =
      if m + n = 0 then
        m • _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else
        0 :=
  _root_.InfoGeometry.Canonical.BosonizationConstructiveCurrent.bosonization_constructive_heisenberg_current C m n

/--
Honest represented current commutator from the existing charged Fock
representation owner surface.
-/
theorem represented_current_commutator_chargedFock
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    ∃ J :
        Int →
          VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
            VirasoroProject.ChargedFockSpace 𝕜 α,
      (∀ v, ∀ᶠ n : Int in Filter.atTop, J n v = 0) ∧
      (∀ m n : Int,
        (J m).commutator (J n) =
          if m + n = 0 then
            (m : 𝕜) •
              (1 :
                VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
                  VirasoroProject.ChargedFockSpace 𝕜 α)
          else
            0) := by
  let H :=
    _root_.InfoGeometry.Canonical.CurrentSugawaraBridge.chargedFockSpaceCurrentHeisenbergRep 𝕜 α
  exact ⟨H.J, H.trunc, H.comm⟩

end InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
