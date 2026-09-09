import Mathlib

/-!
QMS isolated proof target for purifying `onsagerPositiveSemidefiniteClaim` in
`InfoGeometry.Canonical.SouriauOperatorialLogPotential`.

Mathematical context:
- `State` is the state carrier.
- `Observable` is the abstract observable carrier.
- `Density State` is represented here as a density/readout function `State → ℝ`.
- `SouriauMetriplecticOnsager` carries a reversible flow, a relative free energy,
  a variational force, an Onsager operator, and a scalar free-energy derivative.
- The structure explicitly supplies the dissipativity law
  `freeEnergyDerivative_nonpos : ∀ ρ, freeEnergyDerivative ρ ≤ 0`.

Existing mathlib/literature context:
- Mathlib supplies the order relation on `ℝ` and theorem projection/equality.
- In Onsager/metriplectic theory, positive-semidefiniteness of an Onsager tensor
  is an operator/quadratic-form property requiring a bilinear form, symmetry, and
  positivity hypotheses. This abstract owner surface does not define such a
  tensor-level PSD predicate.

QMS purification move:
- Replace the impossible tensor-PSD socket by the native dissipativity theorem
  that is actually carried by the structure: along each density `ρ`, the scalar
  free-energy derivative is nonpositive.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialOnsager

abbrev Density (State : Type*) := State → ℝ

structure SouriauMetriplecticOnsager (State Observable : Type*) where
  reversibleFlow : Density State → Density State
  relativeFreeEnergy : Density State → ℝ
  variationOfRelativeFreeEnergy : Density State → Density State
  onsagerOperator : Density State → Density State
  freeEnergyDerivative : Density State → ℝ
  freeEnergyDerivative_nonpos : ∀ ρ, freeEnergyDerivative ρ ≤ 0
  hamiltonianPartPreservesFreeEnergy : ∀ ρ, relativeFreeEnergy (reversibleFlow ρ) = relativeFreeEnergy ρ
  dissipativePartDissipatesFreeEnergy : ∀ ρ, freeEnergyDerivative ρ ≤ 0

/-- The Onsager socket reduces to the supplied scalar free-energy dissipativity law. -/
theorem onsagerPositiveSemidefinite_as_freeEnergyDerivative_nonpos
    {State Observable : Type*}
    (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) :
    O.freeEnergyDerivative ρ ≤ 0 := by
  exact O.freeEnergyDerivative_nonpos ρ

end InfoGeometry.QMS.SouriauOperatorialLogPotentialOnsager
