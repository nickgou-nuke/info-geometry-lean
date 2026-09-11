import InfoGeometry.Canonical.ConnesNoncommutativeGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConnesNCSpectralDistanceTopCat

/-!
# Bridge from the Connes noncommutative metric to the topological Lip-set owner

The repository already owns the algebraic commutator/distance layer and the
topological Lip-set closure layer.  This file only packages those truths under
a single bridge namespace; it does not introduce any new spectral surrogate.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnesSpectralDistanceTopCatBridge

open InfoGeometry.Canonical.CuntzConnesSpectralDistance
open InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum

variable {A : Type*} [NormedRing A]

/-- The Dirac commutator is the same algebraic observable used by the
topological commutator map. -/
theorem commutatorTopCatHom_apply
    (D a : A) :
    InfoGeometry.Canonical.ConnesNCSpectralDistanceTopCat.commutatorTopCatHom D a =
      CuntzConnesSpectralDistance.commutator D a := by
  rfl

/-- The Lip-1 ball is closed in the topological owner. -/
theorem lipSet_closed (D : A) :
    IsClosed (LipSet D) :=
  InfoGeometry.Canonical.ConnesNCSpectralDistanceTopCat.lipSet_closed D

/-- A pointwise admissible observable is bounded above by the defining supremum. -/
theorem pointwise_le_supremum_spectral_dist
    (D : A) (ω₁ ω₂ : A → ℝ) (a : A)
    (ha : a ∈ LipSet D)
    (h_bdd : BddAbove (spectralDistanceSet D ω₁ ω₂)) :
    |ω₁ a - ω₂ a| ≤ supremumSpectralDist D ω₁ ω₂ :=
  InfoGeometry.Canonical.ConnesNCSpectralMetricSupremum.pointwise_le_supremum_spectral_dist
    D ω₁ ω₂ a ha h_bdd

/-- The noncommutative differential still satisfies Leibniz under the bridge. -/
theorem differential_leibniz
    (D a b : A) :
    ConnesNCGFormAlgebra.ncDeriv D (a * b) =
      ConnesNCGFormAlgebra.ncDeriv D a * b + a * ConnesNCGFormAlgebra.ncDeriv D b :=
  ConnesNoncommutativeGeometry.differential_leibniz D a b

/-- The bridge packages the algebraic and topological spectral-distance facts. -/
theorem connes_spectral_distance_topcat_bridge
    (D : A) (ω₁ ω₂ : A → ℝ) (a : A)
    (ha : a ∈ LipSet D)
    (h_bdd : BddAbove (spectralDistanceSet D ω₁ ω₂)) :
    IsClosed (LipSet D) ∧
      |ω₁ a - ω₂ a| ≤ supremumSpectralDist D ω₁ ω₂ ∧
      ConnesNCGFormAlgebra.ncDeriv D (a * a) =
        ConnesNCGFormAlgebra.ncDeriv D a * a + a * ConnesNCGFormAlgebra.ncDeriv D a := by
  refine ⟨lipSet_closed D, ?_, ?_⟩
  · exact pointwise_le_supremum_spectral_dist D ω₁ ω₂ a ha h_bdd
  · simpa using differential_leibniz D a a

end InfoGeometry.Canonical.ConnesSpectralDistanceTopCatBridge

