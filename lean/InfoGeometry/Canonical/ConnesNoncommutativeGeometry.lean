import InfoGeometry.Canonical.ConnesNCGFormAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzConnesSpectralDistance

/-!
# Connes noncommutative geometry bridge

This file does not introduce a new carrier.  It packages the existing
noncommutative differential owner and the spectral-distance owner under one
bridge so downstream code can depend on a single theorem-safe layer.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnesNoncommutativeGeometry

open ConnesSpectral
open ConnesSpectral.SpectralTriple

variable {A : Type*} [NormedRing A]

/-- The Dirac commutator differential obeys the Leibniz rule. -/
theorem differential_leibniz (D a b : A) :
    ConnesNCGFormAlgebra.ncDeriv D (a * b) =
      (ConnesNCGFormAlgebra.ncDeriv D a) * b + a * ConnesNCGFormAlgebra.ncDeriv D b :=
  ConnesNCGFormAlgebra.ncDeriv_leibniz D a b

/-- The spectral distance bound is symmetric. -/
theorem state_distance_symmetry (D : A) (μ ν : A → ℝ) (d : ℝ)
    (h : CuntzConnesSpectralDistance.StateDistanceBound D μ ν d) :
    CuntzConnesSpectralDistance.StateDistanceBound D ν μ d :=
  CuntzConnesSpectralDistance.distance_bound_symmetry D μ ν d h

/-- The spectral distance bound satisfies the triangle inequality. -/
theorem state_distance_triangle (D : A) (μ ν ρ : A → ℝ) (d1 d2 : ℝ)
    (h1 : CuntzConnesSpectralDistance.StateDistanceBound D μ ν d1)
    (h2 : CuntzConnesSpectralDistance.StateDistanceBound D ν ρ d2) :
    CuntzConnesSpectralDistance.StateDistanceBound D μ ρ (d1 + d2) :=
  CuntzConnesSpectralDistance.distance_bound_triangle D μ ν ρ d1 d2 h1 h2

/-- Zero distance for identical states. -/
theorem state_distance_self (D : A) (μ : A → ℝ) :
    CuntzConnesSpectralDistance.StateDistanceBound D μ μ 0 :=
  CuntzConnesSpectralDistance.distance_bound_self D μ

/-- The native noncommutative bridge in one package. -/
theorem connes_noncommutative_geometry_synthesis
    (D a b : A) (μ ν ρ : A → ℝ) (d1 d2 : ℝ)
    (h1 : CuntzConnesSpectralDistance.StateDistanceBound D μ ν d1)
    (h2 : CuntzConnesSpectralDistance.StateDistanceBound D ν ρ d2) :
    (ConnesNCGFormAlgebra.ncDeriv D (a * b) =
      (ConnesNCGFormAlgebra.ncDeriv D a) * b + a * ConnesNCGFormAlgebra.ncDeriv D b) ∧
    CuntzConnesSpectralDistance.StateDistanceBound D ν μ d1 ∧
    CuntzConnesSpectralDistance.StateDistanceBound D μ ρ (d1 + d2) ∧
    CuntzConnesSpectralDistance.StateDistanceBound D μ μ 0 := by
  refine ⟨differential_leibniz D a b, ?_, ?_, ?_⟩
  · exact state_distance_symmetry D μ ν d1 h1
  · exact state_distance_triangle D μ ν ρ d1 d2 h1 h2
  · exact state_distance_self D μ

end InfoGeometry.Canonical.ConnesNoncommutativeGeometry

