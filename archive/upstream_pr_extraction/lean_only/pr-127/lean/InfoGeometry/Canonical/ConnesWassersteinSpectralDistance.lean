import InfoGeometry.Canonical.ConnesSpectralDistanceTopCatBridge
import InfoGeometry.Canonical.ConnesNoncommutativeGeometry

/-!
# Connes spectral distance bridge

This module packages the existing noncommutative spectral-distance owners under
a single bridge namespace.  It does not introduce a transport map, a diagonal
carrier, or a finite-matrix surrogate.  The only data here are the already
proved Lipschitz ball, supremum distance readout, and the noncommutative
Leibniz/distance laws.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnesWassersteinSpectralDistance

open InfoGeometry.Canonical.CuntzConnesSpectralDistance
open InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum

variable {A : Type*} [NormedRing A]

/-- The Connes spectral-distance readout, packaged as a bridge alias. -/
def spectralDistance (D : A) (ω₁ ω₂ : A → ℝ) : ℝ :=
  supremumSpectralDist D ω₁ ω₂

/-- The bridge distance is definitionally the supremum readout. -/
theorem spectralDistance_eq_supremum
    (D : A) (ω₁ ω₂ : A → ℝ) :
    spectralDistance D ω₁ ω₂ = supremumSpectralDist D ω₁ ω₂ :=
  rfl

/-- The Lip-1 ball remains closed in the bridged namespace. -/
theorem lipSet_closed (D : A) :
    IsClosed (LipSet D) :=
  ConnesNCSpectralDistanceTopCat.lipSet_closed D

/-- Every admissible observable is bounded by the bridge supremum. -/
theorem pointwise_le_spectralDistance
    (D : A) (ω₁ ω₂ : A → ℝ) (a : A)
    (ha : a ∈ LipSet D)
    (h_bdd : BddAbove (spectralDistanceSet D ω₁ ω₂)) :
    |ω₁ a - ω₂ a| ≤ spectralDistance D ω₁ ω₂ := by
  simpa [spectralDistance] using
    pointwise_le_supremum_spectral_dist D ω₁ ω₂ a ha h_bdd

/-- The bridge spectral distance is symmetric in its state arguments. -/
theorem spectralDistance_symmetry
    (D : A) (ω₁ ω₂ : A → ℝ) :
    spectralDistance D ω₁ ω₂ = spectralDistance D ω₂ ω₁ := by
  unfold spectralDistance supremumSpectralDist
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    exact abs_sub_comm _ _
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    exact abs_sub_comm _ _

/-- The bridged spectral distance supports triangle-inequality readouts. -/
theorem spectralDistance_triangle
    (D : A) (ω₁ ω₂ ω₃ : A → ℝ)
    (d1 d2 : ℝ)
    (h1 : StateDistanceBound D ω₁ ω₂ d1)
    (h2 : StateDistanceBound D ω₂ ω₃ d2) :
    StateDistanceBound D ω₁ ω₃ (d1 + d2) :=
  distance_bound_triangle D ω₁ ω₂ ω₃ d1 d2 h1 h2

/-- The bridged noncommutative differential still obeys Leibniz. -/
theorem differential_leibniz
    (D a b : A) :
    ConnesNCGFormAlgebra.ncDeriv D (a * b) =
      ConnesNCGFormAlgebra.ncDeriv D a * b + a * ConnesNCGFormAlgebra.ncDeriv D b :=
  ConnesNoncommutativeGeometry.differential_leibniz D a b

/-- The bridge packages the spectral and differential noncommutative facts. -/
theorem connes_wasserstein_spectral_distance_bridge
    (D : A) (ω₁ ω₂ ω₃ : A → ℝ)
    (a b : A)
    (ha : a ∈ LipSet D)
    (h_bdd : BddAbove (spectralDistanceSet D ω₁ ω₂))
    (d1 d2 : ℝ)
    (h1 : StateDistanceBound D ω₁ ω₂ d1)
    (h2 : StateDistanceBound D ω₂ ω₃ d2) :
    IsClosed (LipSet D) ∧
      |ω₁ a - ω₂ a| ≤ spectralDistance D ω₁ ω₂ ∧
      StateDistanceBound D ω₁ ω₃ (d1 + d2) ∧
      ConnesNCGFormAlgebra.ncDeriv D (a * b) =
        ConnesNCGFormAlgebra.ncDeriv D a * b + a * ConnesNCGFormAlgebra.ncDeriv D b := by
  refine ⟨lipSet_closed D, ?_, ?_, ?_⟩
  · exact pointwise_le_spectralDistance D ω₁ ω₂ a ha h_bdd
  · exact spectralDistance_triangle D ω₁ ω₂ ω₃ d1 d2 h1 h2
  · exact differential_leibniz D a b

end InfoGeometry.Canonical.ConnesWassersteinSpectralDistance
