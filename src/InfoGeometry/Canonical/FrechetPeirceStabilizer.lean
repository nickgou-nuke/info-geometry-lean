/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorFrechetPeirceGrading

/-! # Stabilizers of Peirce pinching by continuous Leibniz derivations

A continuous operator derivation commutes with Peirce pinching exactly when
it annihilates the underlying idempotent. This applies to arbitrary
continuous Leibniz derivations, not only inner derivations.
-/

noncomputable section

namespace InfoGeometry.Canonical.FrechetPeirceStabilizer

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Optics.OperatorDerivationForms

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- A Leibniz derivation of a unital ring annihilates its identity. -/
theorem derivation_one (D : FrechetOperatorDerivation ℝ A) : D 1 = 0 := by
  have h := D.leibniz 1 1
  change D (1 * 1) = D 1 * 1 + 1 * D 1 at h
  simp only [one_mul, mul_one] at h
  have h' : D 1 + D 1 = D 1 + 0 := by simpa using h.symm
  exact add_left_cancel h'

/-- The value of a derivation at an idempotent has zero even Peirce part. -/
theorem derivation_idempotent_even_zero (D : FrechetOperatorDerivation ℝ A)
    (P : A) (hP : P * P = P) : evenGrade P (D P) = 0 := by
  have h := D.leibniz P P
  change D (P * P) = D P * P + P * D P at h
  rw [hP] at h
  have hPP (Z : A) : P * (P * Z) = P * Z := by rw [← mul_assoc, hP]
  have hPDP : P * (D P * P) = 0 := by
    have hh := congrArg (fun Z : A => P * Z * P) h
    simp only [mul_add, add_mul, mul_assoc, hPP, hP] at hh
    have hh' : P * (D P * P) + P * (D P * P) = P * (D P * P) + 0 := by
      simpa using hh.symm
    exact add_left_cancel hh'
  rw [h]
  unfold evenGrade
  peirce_nf hP
  simp [hPDP]

/-- A continuous Leibniz derivation commutes with Peirce pinching precisely
when it fixes the idempotent. -/
theorem derivation_commutes_evenGrade_iff (D : FrechetOperatorDerivation ℝ A)
    (P : A) (hP : P * P = P) :
    (∀ X : A, D (evenGrade P X) = evenGrade P (D X)) ↔ D P = 0 := by
  constructor
  · intro h
    have hPgrade : evenGrade P P = P := by
      unfold evenGrade
      peirce_nf hP
    have hAtP := h P
    rw [hPgrade, derivation_idempotent_even_zero D P hP] at hAtP
    exact hAtP
  · intro hDP X
    have hD1 : D 1 = 0 := derivation_one D
    change D.toContinuousLinearMap (evenGrade P X) = evenGrade P (D X)
    simp only [evenGrade, D.toContinuousLinearMap.map_add,
      D.toContinuousLinearMap.map_sub, D.leibniz, hDP, hD1,
      sub_self, zero_mul, mul_zero, zero_add, add_zero]

/-- The complete failure of a derivation to commute with Peirce pinching
is determined by its value on the cut, without assuming idempotence. -/
theorem derivation_evenGrade_defect (D : FrechetOperatorDerivation ℝ A)
    (P X : A) :
    D (evenGrade P X) - evenGrade P (D X) =
      D P * X * P + P * X * D P -
        D P * X * (1 - P) - (1 - P) * X * D P := by
  have hD1 : D 1 = 0 := derivation_one D
  change D.toContinuousLinearMap (evenGrade P X) - evenGrade P (D X) = _
  simp only [evenGrade, D.toContinuousLinearMap.map_add,
    D.toContinuousLinearMap.map_sub, D.leibniz, hD1, zero_sub]
  noncomm_ring

/-- The idempotent itself detects the full defect: no existential search for
an input is needed. -/
theorem derivation_evenGrade_defect_at_idempotent (D : FrechetOperatorDerivation ℝ A)
    (P : A) (hP : P * P = P) :
    D (evenGrade P P) - evenGrade P (D P) = D P := by
  have hPgrade : evenGrade P P = P := by
    unfold evenGrade
    peirce_nf hP
  rw [hPgrade, derivation_idempotent_even_zero D P hP, sub_zero]

/-- The commutator of two continuous Peirce-stabilizing Leibniz derivations
also stabilizes the same Peirce projection. -/
theorem commutator_preserves_evenGrade (D E : FrechetOperatorDerivation ℝ A)
    (P : A) (hP : P * P = P)
    (hD : ∀ X : A, D (evenGrade P X) = evenGrade P (D X))
    (hE : ∀ X : A, E (evenGrade P X) = evenGrade P (E X)) :
    ∀ X : A, FrechetOperatorDerivation.commutator D E (evenGrade P X) =
      evenGrade P (FrechetOperatorDerivation.commutator D E X) := by
  apply (derivation_commutes_evenGrade_iff _ P hP).2
  have hDP := (derivation_commutes_evenGrade_iff D P hP).1 hD
  have hEP := (derivation_commutes_evenGrade_iff E P hP).1 hE
  rw [FrechetOperatorDerivation.commutator_apply, hDP, hEP]
  simp only [D.toContinuousLinearMap.map_zero, E.toContinuousLinearMap.map_zero, sub_self]

open scoped Matrix Matrix.Norms.Operator
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorStageFrechetConnection

/-- On each full matrix stage, an inner continuous derivation preserves the
Peirce pinching exactly when its generator commutes with the idempotent. -/
theorem stageInnerFrechet_commutes_evenGrade_iff
    (n : ℕ) (P H : Stage n) (hP : P * P = P) :
    (∀ X : Stage n, stageInnerFrechet n H (evenGrade P X) =
      evenGrade P (stageInnerFrechet n H X)) ↔ H * P = P * H := by
  rw [derivation_commutes_evenGrade_iff (stageInnerFrechet n H) P hP]
  change H * P - P * H = 0 ↔ H * P = P * H
  exact sub_eq_zero

end InfoGeometry.Canonical.FrechetPeirceStabilizer

end
