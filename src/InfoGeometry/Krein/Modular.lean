import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.KreinSpace
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Star

/-!
# Modular Theory in Krein Spaces

This module provides the foundation for modular operators and flows in
Krein spaces, derived directly from Mathlib's spectral and adjoint theory.

We avoid "witness data" and instead prove the properties of modular operators
constructively.
-/

namespace InfoGeometry.Krein

open scoped InnerProductSpace
open InfoGeometry.Krein.KreinSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [KreinSpace H]

local notation "EndH" => H →L[ℝ] H

/-- The modular operator `Δ = T♯ T` associated to a linear operator `T`. -/
noncomputable def modularOperator (T : EndH) : EndH :=
  (kreinAdjoint T).comp T

/-- The modular operator is always Krein-self-adjoint. -/
theorem modularOperator_kreinSelfAdjoint (T : EndH) :
    IsKreinSelfAdjoint (modularOperator T) := by
  unfold modularOperator IsKreinSelfAdjoint
  rw [kreinAdjoint_comp, kreinAdjoint_involutive]

/-- The Hilbert part of the modular operator is `T† J T`. -/
theorem hilbertPart_modularOperator (T : EndH) :
    (jCLM (H := H)).comp (modularOperator T) =
      (ContinuousLinearMap.adjoint T).comp ((jCLM (H := H)).comp T) := by
  unfold modularOperator kreinAdjoint
  simp only [ContinuousLinearMap.comp_assoc]
  rw [jCLM_comp_jCLM_comp]

/-- The modular operator's Hilbert part is always Hilbert-self-adjoint. -/
theorem modularOperator_hilbert_selfAdjoint (T : EndH) :
    IsSelfAdjoint ((jCLM (H := H)).comp (modularOperator T)) := by
  rw [hilbertPart_modularOperator]
  exact (jCLM_selfAdjoint (H := H)).adjoint_conj T

/--
The Krein adjoint of an exponential is the exponential of the Krein adjoint.
-/
theorem kreinAdjoint_exp (G : EndH) :
    kreinAdjoint (NormedSpace.exp G) = NormedSpace.exp (kreinAdjoint G) := by
  unfold kreinAdjoint
  have h_star : ∀ A : EndH, star A = ContinuousLinearMap.adjoint A := fun _ => rfl
  rw [← h_star, ← h_star]
  rw [NormedSpace.star_exp]
  let J := jCLM (H := H)
  let Ju : (EndH)ˣ := {
    val := J
    inv := J
    val_inv := jCLM_comp_self
    inv_val := jCLM_comp_self
  }
  have h_conj := NormedSpace.exp_units_conj Ju (star G)
  simp [Ju] at h_conj
  have h_mul : ∀ A B : EndH, A.comp B = A * B := fun _ _ => rfl
  rw [h_mul, h_mul, h_mul, h_mul]
  exact h_conj.symm

/-- Modular flow interface on Krein spaces. -/
structure ModularFlow (G : EndH) where
  flow : ℝ → EndH
  flow_zero : flow 0 = 1
  flow_add : ∀ s t, flow (s + t) = (flow s) * (flow t)
  flow_is_isometry : ∀ t, IsKreinIsometry (flow t)

/--
Construct a modular flow from a Krein-skew-adjoint generator via the
exponential map.
-/
noncomputable def modularFlowOfGenerator (G : EndH) (hG : IsKreinSkewAdjoint G) :
    ModularFlow G where
  flow t := NormedSpace.exp (t • G)
  flow_zero := by simp [NormedSpace.exp_zero]
  flow_add s t := by
    rw [← NormedSpace.exp_add_of_commute]
    · simp [add_smul]
    · exact ((Commute.refl G).smul_left s).smul_right t
  flow_is_isometry t := by
    rw [isKreinIsometry_iff_star_comp_self]
    rw [kreinAdjoint_exp]
    have h_adj : kreinAdjoint (t • G) = -(t • G) := by
      rw [kreinAdjoint_smul, hG]
      simp [smul_neg]
    rw [h_adj]
    have h_comp_mul : ∀ A B : EndH, A.comp B = A * B := fun _ _ => rfl
    rw [h_comp_mul]
    rw [← NormedSpace.exp_add_of_commute]
    · simp [NormedSpace.exp_zero]
      rfl
    · exact Commute.neg_left (Commute.refl _)

end InfoGeometry.Krein
