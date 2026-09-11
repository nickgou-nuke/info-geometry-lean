import InfoGeometry.Dynamics.KmsBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.TomitaTakesaki

noncomputable section

/-!
# SouriauFoliationFiniteShadow

This file is an honest finite shadow for the untracked placeholder module
`Quantum/SouriauFoliation.lean`.

BUCKET 1: closed finite theorems
- the diagonal modular operator is a concrete `2 × 2` matrix;
- the finite modular flow `Δ^{it}` forms an additive one-parameter family;
- the modular conjugation `J` is an involution and reflects the diagonal
  modular Hamiltonian;
- the finite Tomita operator is exactly `J * Δ^{1/2}`.

BUCKET 2: explicit finite predicates
- `IsRadialEngine U` means `U` is a concrete imaginary-time Gibbs weight;
- `IsRotationalEngine U` means `U` is a concrete finite Tomita flow matrix.

BUCKET 3: excluded analytic claims
- no infinite-dimensional GNS completion;
- no Souriau coadjoint-orbit theorem;
- no full Tomita--Takesaki standard-form theorem.
-/

namespace InfoGeometry.Quantum.SouriauFoliationFiniteShadow

open InfoGeometry.Dynamics.KmsBoundary
open InfoGeometry.Dynamics.TomitaTakesaki

abbrev Mat2C := InfoGeometry.Dynamics.KmsBoundary.Mat2C

/-- Concrete finite radial engine: an imaginary-time Gibbs weight. -/
def IsRadialEngine (U : Mat2C) : Prop :=
  ∃ β : ℂ, U = imaginaryTimeEvolution β

/-- Concrete finite rotational engine: a Tomita flow matrix `Δ^{it}`. -/
def IsRotationalEngine (U : Mat2C) : Prop :=
  ∃ t : ℝ, U = finiteTomitaFlow t

/-- The finite modular operator is a radial engine. -/
theorem modularOperator_isRadialEngine :
    IsRadialEngine modularOperator := by
  refine ⟨1, rfl⟩

/-- The finite modular square root is also a radial engine. -/
theorem modularOperatorSqrt_isRadialEngine :
    IsRadialEngine modularOperatorSqrt := by
  refine ⟨(1 / 2 : ℂ), rfl⟩

/-- Every finite Tomita flow matrix is a rotational engine. -/
theorem finiteTomitaFlow_isRotationalEngine (t : ℝ) :
    IsRotationalEngine (finiteTomitaFlow t) := by
  exact ⟨t, rfl⟩

/-- The identity matrix is the zero-time rotational engine. -/
theorem identity_isRotationalEngine :
    IsRotationalEngine (1 : Mat2C) := by
  refine ⟨0, ?_⟩
  exact finiteTomitaFlow_zero.symm

/-- The finite rotational engine composes additively in time. -/
theorem rotationalEngine_add (s t : ℝ) :
    finiteTomitaFlow s * finiteTomitaFlow t = finiteTomitaFlow (s + t) := by
  simpa using finiteTomitaFlow_add s t

/-- The finite modular conjugation is an involution. -/
theorem modularConjugation_involutive :
    modularConjugation * modularConjugation = (1 : Mat2C) := by
  exact modularConjugation_is_involution

/-- The finite modular conjugation reflects the diagonal modular Hamiltonian. -/
theorem modularConjugation_reflects_modularHamiltonian :
    modularConjugation * modularHamiltonian * modularConjugation =
      -modularHamiltonian := by
  simpa using modularConjugation_reflects_hamiltonian

/-- The finite Tomita operator is the product `J * Δ^{1/2}`. -/
theorem tomitaOperator_eq_product :
    tomitaOperator = modularConjugation * modularOperatorSqrt := by
  rfl

/-- Honest finite dual-engine packet for the modular shadow. -/
theorem dual_engine_finite_shadow :
    IsRadialEngine modularOperator ∧
      IsRotationalEngine (1 : Mat2C) ∧
      modularConjugation * modularConjugation = (1 : Mat2C) := by
  exact ⟨modularOperator_isRadialEngine, identity_isRotationalEngine,
    modularConjugation_involutive⟩

end InfoGeometry.Quantum.SouriauFoliationFiniteShadow
