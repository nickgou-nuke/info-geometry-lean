import InfoGeometry.Krein.KreinSpace
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option maxHeartbeats 1000000

/-!
# Infinitesimal Isometries and Exponential Maps

This module demonstrates that the exponential of an infinitesimal isometry
(a skew-adjoint operator with respect to the Krein metric) is an isometry
of the Krein space.

This matches the functorial lifting of Noether/Killing vector fields to
measure-preserving modular operators via the exponential map.
-/

namespace InfoGeometry.Krein

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

open KreinSpace

/-- The fundamental symmetry J as an invertible bounded operator. -/
noncomputable def jUnit : (H →L[ℝ] H)ˣ where
  val := jCLM (H := H)
  inv := jCLM (H := H)
  val_inv := by ext x; exact J_invol x
  inv_val := by ext x; exact J_invol x

/-- `kreinAdjoint A` is identical to conjugating the Hilbert adjoint `A†` by the modular operator `J`. -/
lemma kreinAdjoint_eq_jUnit_conj (A : H →L[ℝ] H) :
    kreinAdjoint A = (jUnit (H := H) : H →L[ℝ] H) * ContinuousLinearMap.adjoint A * (↑((jUnit (H := H))⁻¹) : H →L[ℝ] H) := rfl

/-- The exponential map commutes with the restricted modular conjugation `kreinAdjoint`. -/
lemma exp_kreinAdjoint (A : H →L[ℝ] H) :
    kreinAdjoint (NormedSpace.exp A) = NormedSpace.exp (kreinAdjoint A) := by

  rw [kreinAdjoint_eq_jUnit_conj]
  have h_star : ContinuousLinearMap.adjoint (NormedSpace.exp A) = NormedSpace.exp (ContinuousLinearMap.adjoint A) := NormedSpace.star_exp A
  rw [h_star]
  have h_conj := NormedSpace.exp_units_conj (jUnit (H := H)) (ContinuousLinearMap.adjoint A)
  rw [← h_conj]
  have h_rev : (jUnit (H := H) : H →L[ℝ] H) * ContinuousLinearMap.adjoint A * (↑((jUnit (H := H))⁻¹) : H →L[ℝ] H) = kreinAdjoint A := rfl
  rw [h_rev]

/--
The exponential of a continuous skew-adjoint operator `A` is an exact Isometry in the Krěn space.
(This corresponds to the transport of Killing vector fields generating modular shifts).
-/
theorem exp_preservesMetric (A : H →L[ℝ] H) (hA : IsKreinSkewAdjoint A) (t : ℝ) :
    IsKreinIsometry (NormedSpace.exp (t • A)) := by

  rw [isKreinIsometry_iff_star_comp_self]
  have h_adj_tA : kreinAdjoint (t • A) = - (t • A) := by
    rw [kreinAdjoint_smul, isKreinSkewAdjoint_iff_eq_neg.mp hA, smul_neg]
  have h_adj_exp : kreinAdjoint (NormedSpace.exp (t • A)) = NormedSpace.exp (- (t • A)) := by
    rw [exp_kreinAdjoint, h_adj_tA]
  rw [h_adj_exp]
  have h_add : NormedSpace.exp (- (t • A)) * NormedSpace.exp (t • A) = (1 : H →L[ℝ] H) := by
    have h_comm : Commute (- (t • A)) (t • A) := (Commute.refl (t • A)).neg_left
    rw [← NormedSpace.exp_add_of_commute h_comm]
    have h_zero : - (t • A) + (t • A) = 0 := neg_add_cancel (t • A)
    rw [h_zero]
    exact NormedSpace.exp_zero
  exact h_add

/-- Exponential flow at time `t` as a continuous linear automorphism. -/
noncomputable def expAutomorphism (A : H →L[ℝ] H) (t : ℝ) : H ≃L[ℝ] H := by
  letI : Invertible (NormedSpace.exp (t • A)) := NormedSpace.invertibleExp (t • A)
  exact ContinuousLinearEquiv.ofUnit (unitOfInvertible (NormedSpace.exp (t • A)))

omit [KreinSpace H] in
@[simp] lemma expAutomorphism_toContinuousLinearMap
    (A : H →L[ℝ] H) (t : ℝ) :
    ((expAutomorphism (A := A) t : H ≃L[ℝ] H) : H →L[ℝ] H) = NormedSpace.exp (t • A) := rfl

/-- A Krein-skew generator exponentiates to a Krein-isometric automorphism. -/
theorem expAutomorphism_preservesMetric
    (A : H →L[ℝ] H) (hA : IsKreinSkewAdjoint A) (t : ℝ) :
    IsKreinIsometry (((expAutomorphism (A := A) t : H ≃L[ℝ] H) : H →L[ℝ] H)) := by
  simpa [expAutomorphism_toContinuousLinearMap] using exp_preservesMetric (A := A) hA t

end InfoGeometry.Krein
