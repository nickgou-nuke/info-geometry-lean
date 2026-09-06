import Mathlib

import InfoGeometry.Canonical.SouriauOnsagerBKMSelfAdjoint

noncomputable section

set_option synthInstance.maxHeartbeats 200000

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

theorem exists_pos_scalar_le_of_strictlyPositive
    (A : SelfAdjointOperator n)
    [NeZero n]
    (hA : IsStrictlyPositive (A : FiniteOperatorAlgebra n)) :
    ∃ r : ℝ, 0 < r ∧
      algebraMap ℝ (FiniteOperatorAlgebra n) r ≤ (A : FiniteOperatorAlgebra n) := by
  exact (CFC.exists_pos_algebraMap_le_iff A.property).mpr
    (fun x hx => hA.spectrum_pos hx)

theorem strictlyPositive_of_norm_sub_lt
    [NeZero n]
    (A B : SelfAdjointOperator n) {ε : ℝ}
    (hA : algebraMap ℝ (FiniteOperatorAlgebra n) ε ≤
      (A : FiniteOperatorAlgebra n))
    (hBA : ‖(B : FiniteOperatorAlgebra n) - A‖ < ε) :
    IsStrictlyPositive (B : FiniteOperatorAlgebra n) := by
  have hdiff : IsSelfAdjoint
      ((B : FiniteOperatorAlgebra n) - A) := B.property.sub A.property
  have hdiff_lower :
      -(algebraMap ℝ (FiniteOperatorAlgebra n)
        ‖(B : FiniteOperatorAlgebra n) - A‖) ≤
        (B : FiniteOperatorAlgebra n) - A :=
    hdiff.neg_algebraMap_norm_le_self
  have hscalar : 0 < ε - ‖(B : FiniteOperatorAlgebra n) - A‖ :=
    sub_pos.mpr hBA
  have horder :
      algebraMap ℝ (FiniteOperatorAlgebra n)
          (ε - ‖(B : FiniteOperatorAlgebra n) - A‖) ≤
        (B : FiniteOperatorAlgebra n) := by
    calc
      algebraMap ℝ (FiniteOperatorAlgebra n)
          (ε - ‖(B : FiniteOperatorAlgebra n) - A‖) =
          algebraMap ℝ (FiniteOperatorAlgebra n) ε +
            -(algebraMap ℝ (FiniteOperatorAlgebra n)
              ‖(B : FiniteOperatorAlgebra n) - A‖) := by
            simp [sub_eq_add_neg]
      _ ≤ (A : FiniteOperatorAlgebra n) +
          ((B : FiniteOperatorAlgebra n) - A) :=
        add_le_add hA hdiff_lower
      _ = (B : FiniteOperatorAlgebra n) := by abel
  exact (IsStrictlyPositive.smul hscalar
    (isStrictlyPositive_one (A := FiniteOperatorAlgebra n))).of_le horder

theorem faithfulStrictPositiveSelfAdjointLocus_isOpen
    [NeZero n] :
    IsOpen (faithfulStrictPositiveSelfAdjointLocus (n := n)) := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  rcases exists_pos_scalar_le_of_strictlyPositive A hA with
    ⟨ε, hε, hgap⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds A hε) ?_
  intro B hB
  apply strictlyPositive_of_norm_sub_lt A B hgap
  simpa [Metric.mem_ball, dist_eq_norm] using hB

end SouriauOnsagerBKM
