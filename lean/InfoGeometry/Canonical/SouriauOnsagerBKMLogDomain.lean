import Mathlib

import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint

noncomputable section

namespace SouriauOnsagerBKM

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

variable {n : ℕ}

/-- The real self-adjoint carrier used as the domain of the real CFC logarithm.
The subtype is Mathlib's canonical `selfAdjoint` carrier, not a parallel
operator structure. -/
abbrev SelfAdjointOperator (n : ℕ) :=
  selfAdjoint (FiniteOperatorAlgebra n)

/-- The faithful strictly-positive locus in the self-adjoint carrier. -/
def faithfulStrictPositiveSelfAdjointLocus :
    Set (SelfAdjointOperator n) :=
  {ρ | IsStrictlyPositive (ρ : FiniteOperatorAlgebra n)}

/-- The canonical self-adjoint point represented by a faithful density. -/
def FaithfulDensityOperator.rhoSelfAdjoint
    (D : FaithfulDensityOperator n) : SelfAdjointOperator n :=
  ⟨D.rho, D.strictlyPositive.isSelfAdjoint.star_eq⟩

theorem FaithfulDensityOperator.rho_mem_faithfulStrictPositiveSelfAdjointLocus
    (D : FaithfulDensityOperator n) :
    D.rhoSelfAdjoint ∈ faithfulStrictPositiveSelfAdjointLocus := by
  exact D.strictlyPositive

end SouriauOnsagerBKM
