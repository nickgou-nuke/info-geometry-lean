import InfoGeometry.Algebra.KleinSpinorOrbit
import Mathlib.Tactic

/-!
# Orbit stratification for Klein spinors
-/

open InfoGeometry.Algebra.KleinSpinorOrbit

namespace InfoGeometry.Algebra.OrbitStratification

/-- The zero spinor (0,0). -/
def zeroSpinor : CsSpinor := ⟨Cs.zero, Cs.zero⟩

/-- Orbit type for ψ ∈ Cs²: zero or non-zero. -/
inductive OrbitType (ψ : CsSpinor) : Prop where
  | isZero : ψ.plus = Cs.zero ∧ ψ.minus = Cs.zero → OrbitType ψ
  | isNonZero : (ψ.plus ≠ Cs.zero ∨ ψ.minus ≠ Cs.zero) → OrbitType ψ

/-- Every spinor is zero or non-zero (decidable case analysis). -/
theorem orbit_classification (ψ : CsSpinor) : OrbitType ψ := by
  by_cases hplus : ψ.plus = Cs.zero
  · by_cases hminus : ψ.minus = Cs.zero
    · exact OrbitType.isZero ⟨hplus, hminus⟩
    · exact OrbitType.isNonZero (Or.inr hminus)
  · exact OrbitType.isNonZero (Or.inl hplus)

/-- A spinor equals (0,0) iff both components are zero. -/
theorem zero_iff_both_zero (ψ : CsSpinor) : ψ = zeroSpinor ↔ ψ.plus = Cs.zero ∧ ψ.minus = Cs.zero := by
  constructor
  · intro h
    have hp : ψ.plus = Cs.zero := by
      simpa [zeroSpinor] using congrArg CsSpinor.plus h
    have hm : ψ.minus = Cs.zero := by
      simpa [zeroSpinor] using congrArg CsSpinor.minus h
    exact ⟨hp, hm⟩
  · rintro ⟨hp, hm⟩
    rcases ψ with ⟨p, m⟩
    simp [zeroSpinor]
    exact ⟨hp, hm⟩

end InfoGeometry.Algebra.OrbitStratification
