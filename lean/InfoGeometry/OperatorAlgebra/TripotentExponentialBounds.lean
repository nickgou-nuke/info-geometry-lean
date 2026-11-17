/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.TripotentExponentialFlow
import InfoGeometry.OperatorAlgebra.ExponentialGradeBounds
import InfoGeometry.Physics.Algebra.TripotentTopologicalFiveGrading

/-!
# Bounded exponential conjugation orbits of a tripotent

The existing five Peirce components are actual bounded linear projections on
the full real normed algebra. Exponential conjugation by a tripotent multiplies
the component of adjoint weight `k` by `exp (k * t)`. Consequently an orbit is
bounded for all real times exactly when its starting operator commutes with
the tripotent.

No finite-dimensionality, self-adjointness, or commutativity of the ambient
algebra is assumed. The degree-zero range is the centralizer of the tripotent,
not necessarily the center of the algebra. One-sided contraction on negative
grades does not imply boundedness for all real times.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TripotentExponentialBounds

open InfoGeometry.Canonical
open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.OperatorAlgebra.ConservedOperatorFlow
open InfoGeometry.OperatorAlgebra.TripotentExponentialFlow
open InfoGeometry.OperatorAlgebra.ExponentialGradeBounds

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

/-- Each projected orbit is bounded by the norm of the native continuous
Peirce projection times the norm of the full orbit. No tripotency is needed
for this covariance and estimate. -/
theorem norm_expTransport_fiveGradeProjector_le
    (S X : A) (k : FiveGrade) (t : ℝ) :
    ‖expTransport S (fiveGradeProjector S k X) t‖ ≤
      ‖continuousGradeProjector S k‖ * ‖expTransport S X t‖ := by
  rw [expTransport_fiveGradeProjector (Commute.refl S) k X t]
  rw [← continuousGradeProjector_apply S (expTransport S X t) k]
  exact (continuousGradeProjector S k).le_opNorm _

/-- Boundedness of the full orbit passes to every existing Peirce component. -/
theorem bounded_expTransport_fiveGradeProjector
    (S X : A) (h : ∃ C : ℝ, ∀ t : ℝ, ‖expTransport S X t‖ ≤ C)
    (k : FiveGrade) :
    ∃ C : ℝ, ∀ t : ℝ,
      ‖expTransport S (fiveGradeProjector S k X) t‖ ≤ C := by
  rcases h with ⟨C, hC⟩
  refine ⟨‖continuousGradeProjector S k‖ * C, ?_⟩
  intro t
  exact (norm_expTransport_fiveGradeProjector_le S X k t).trans
    (mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _))

/-- The complete operator-valued Peirce component has its exact exponential
weight under conjugation; this is not only a scalar readout. -/
theorem expTransport_fiveGradeProjector_eq_exp_smul
    {S : A} (hS : S * S * S = S) (X : A) (k : FiveGrade) (t : ℝ) :
    expTransport S (fiveGradeProjector S k X) t =
      Real.exp ((fiveGradeValue k : ℝ) * t) • fiveGradeProjector S k X := by
  apply expTransport_eq_exp_smul_of_lie_eq
  have heig := mem_fiveGradeRange_implies_adjoint_eigen hS k
    (show fiveGradeProjector S k X ∈ fiveGradeRange S k from ⟨X, rfl⟩)
  change S * fiveGradeProjector S k X - fiveGradeProjector S k X * S =
    (fiveGradeValue k : ℝ) • fiveGradeProjector S k X at heig
  exact heig

/-- Every grade has an exact norm multiplier, without orthogonality or
self-adjointness assumptions on the spectral projectors. -/
theorem norm_expTransport_fiveGradeProjector
    {S : A} (hS : S * S * S = S) (X : A) (k : FiveGrade) (t : ℝ) :
    ‖expTransport S (fiveGradeProjector S k X) t‖ =
      Real.exp ((fiveGradeValue k : ℝ) * t) * ‖fiveGradeProjector S k X‖ := by
  rw [expTransport_fiveGradeProjector_eq_exp_smul hS X k t, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- A single Peirce component has a bounded orbit for all real times exactly
when its weight is zero or the component itself vanishes. -/
theorem bounded_expTransport_fiveGradeProjector_iff
    {S : A} (hS : S * S * S = S) (X : A) (k : FiveGrade) :
    (∃ C : ℝ, ∀ t : ℝ,
      ‖expTransport S (fiveGradeProjector S k X) t‖ ≤ C) ↔
      (fiveGradeValue k : ℝ) = 0 ∨ fiveGradeProjector S k X = 0 := by
  apply bounded_expTransport_iff_of_lie_eq
  have heig := mem_fiveGradeRange_implies_adjoint_eigen hS k
    (show fiveGradeProjector S k X ∈ fiveGradeRange S k from ⟨X, rfl⟩)
  change S * fiveGradeProjector S k X - fiveGradeProjector S k X * S =
    (fiveGradeValue k : ℝ) • fiveGradeProjector S k X at heig
  exact heig

/-- The orbit of an arbitrary operator under a tripotent's exponential
conjugation is bounded for all real times if and only if the operators commute.
The forward direction uses a nonzero genuine Peirce component and its bounded
linear projection, so cancellations between different grades do not conceal
exponential growth. -/
theorem bounded_expTransport_iff_commute
    {S : A} (hS : S * S * S = S) (X : A) :
    (∃ C : ℝ, ∀ t : ℝ, ‖expTransport S X t‖ ≤ C) ↔ Commute S X := by
  constructor
  · intro hbounded
    by_contra hcomm
    have had : LieAlgebra.ad ℝ A S X ≠ 0 := by
      intro hz
      apply hcomm
      change S * X - X * S = 0 at hz
      exact sub_eq_zero.mp hz
    obtain ⟨k, hk, hcomponent⟩ :=
      exists_nonzero_nonzero_grade_component_of_ad_ne_zero hS had
    have hweight : (fiveGradeValue k : ℝ) ≠ 0 := by
      cases k with
      | negTwo => norm_num [fiveGradeValue]
      | negOne => norm_num [fiveGradeValue]
      | zero => exact False.elim (hk rfl)
      | posOne => norm_num [fiveGradeValue]
      | posTwo => norm_num [fiveGradeValue]
    have hkbounded := bounded_expTransport_fiveGradeProjector S X hbounded k
    rcases (bounded_expTransport_fiveGradeProjector_iff hS X k).mp hkbounded with
      hz | hz
    · exact hweight hz
    · exact hcomponent hz
  · intro hcomm
    refine ⟨‖X‖, ?_⟩
    intro t
    calc
      ‖expTransport S X t‖ = ‖X‖ :=
        congrArg norm ((conserved_iff_commute S X).mpr hcomm t)
      _ ≤ ‖X‖ := le_refl _

/-- In nonnegative time, every nonpositive grade contracts in norm. The
all-real boundedness criterion above still excludes nonzero negative grades. -/
theorem norm_expTransport_fiveGradeProjector_le_of_nonpos
    {S : A} (hS : S * S * S = S) (X : A) (k : FiveGrade)
    (hk : (fiveGradeValue k : ℝ) ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖expTransport S (fiveGradeProjector S k X) t‖ ≤
      ‖fiveGradeProjector S k X‖ := by
  rw [norm_expTransport_fiveGradeProjector hS X k t]
  have hexp : Real.exp ((fiveGradeValue k : ℝ) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hk ht)
  calc
    Real.exp ((fiveGradeValue k : ℝ) * t) * ‖fiveGradeProjector S k X‖ ≤
        1 * ‖fiveGradeProjector S k X‖ :=
      mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ = ‖fiveGradeProjector S k X‖ := one_mul _

end InfoGeometry.OperatorAlgebra.TripotentExponentialBounds
