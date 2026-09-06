import Mathlib.Tactic
import InfoGeometry.Canonical.CuntzConnesSpectralDistance

noncomputable section

namespace InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum

/-!
# Supremum Connes spectral distance over a noncommutative normed algebra

This module owns the supremum construction only.  The algebraic commutator and
its norm are imported from `CuntzConnesSpectralDistance`; no commutative
diagonal subalgebra or finite matrix surrogate is used here.
-/

open InfoGeometry.Canonical.CuntzConnesSpectralDistance

variable {A : Type*} [NormedRing A]

/-- The Lip-1 ball for an algebra element relative to a Dirac element `D`. -/
def LipSet (D : A) : Set A :=
  {a | LipschitzBall D a}

/-- Values whose supremum defines the Connes spectral distance. -/
def spectralDistanceSet (D : A) (ω₁ ω₂ : A → ℝ) : Set ℝ :=
  {r | ∃ a ∈ LipSet D, r = |ω₁ a - ω₂ a|}

/-- Connes' supremum spectral distance for two real-valued state readouts. -/
def supremumSpectralDist (D : A) (ω₁ ω₂ : A → ℝ) : ℝ :=
  sSup (spectralDistanceSet D ω₁ ω₂)

/-- Every admissible observable is bounded above by the defining supremum. -/
theorem pointwise_le_supremum_spectral_dist
    (D : A) (ω₁ ω₂ : A → ℝ) (a : A)
    (ha : a ∈ LipSet D)
    (h_bdd : BddAbove (spectralDistanceSet D ω₁ ω₂)) :
    |ω₁ a - ω₂ a| ≤ supremumSpectralDist D ω₁ ω₂ := by
  apply le_csSup h_bdd
  exact ⟨a, ha, rfl⟩

end InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum
