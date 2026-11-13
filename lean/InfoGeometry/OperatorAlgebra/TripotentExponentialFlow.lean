/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentAdjointRigidity
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.Core.TripotentGradeTransport
import InfoGeometry.OperatorAlgebra.ConservedOperatorFlow

/-!
# Tripotent grades under actual exponential conjugation

The existing exponential transport acts on the full complete real normed
algebra. Polynomial spectral projectors, the nine joint Peirce projectors,
and the five grouped projectors are covariant under this transport.

Commutation of the generator with the tripotent makes those projectors
stationary and preserves their actual ranges. Conversely, preserving just
the zero-grade range at all times already forces this commutation: its
application to the tripotent and differentiation at zero give a vanishing
double adjoint, to which the existing quintic rigidity applies.

No identification with the modular flow of a specified state is assumed or
concluded. The zero-grade range is the centralizer of S, equivalently the
kernel of ad_S. It need not be the center of the ambient algebra, and no
identification with the zero-eigenspace of S in an ambient representation is
asserted.
-/

namespace InfoGeometry.OperatorAlgebra.TripotentExponentialFlow

open InfoGeometry.Canonical
open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.OperatorAlgebra.ConservedOperatorFlow

attribute [local instance 100] LieRing.ofAssociativeRing

section Algebraic

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The operator grade zero is precisely the centralizer of the tripotent. -/
theorem mem_fiveGradeRange_zero_iff_commute {S X : A} (hS : S * S * S = S) :
    X ∈ fiveGradeRange S .zero ↔ Commute S X := by
  rw [fiveGradeRange_eq_eigenspace hS .zero, Module.End.mem_eigenspace_iff]
  simp only [fiveGradeValue, Int.cast_zero, zero_smul]
  change S * X - X * S = 0 ↔ S * X = X * S
  exact sub_eq_zero

end Algebraic

section Exponential

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The transported grading element remains tripotent under arbitrary
exponential conjugation. -/
theorem expTransport_tripotent {H S : A} (hS : S * S * S = S) (t : ℝ) :
    expTransport H S t * expTransport H S t * expTransport H S t =
      expTransport H S t := by
  rw [← flow_mul, ← flow_mul, hS]

/-- Spectral polynomials are covariant even before imposing tripotency or
commutation with the flow generator. -/
theorem expTransport_peirceProjector_transport (H S : A) (s : PeirceSign) (t : ℝ) :
    expTransport H (peirceProjector S s) t =
      peirceProjector (expTransport H S t) s := by
  cases s <;>
    simp only [peirceProjector, projPos, projNeg, projZero, flow_smul,
      expTransport_add_seed, expTransport_sub_seed, flow_mul, flow_one]

/-- Joint left/right Peirce projection commutes with transport of both the
grading element and the argument. Multiplication order is retained. -/
theorem expTransport_jointPeirceProjector_transport
    (H S X : A) (left right : PeirceSign) (t : ℝ) :
    expTransport H (jointPeirceProjector S left right X) t =
      jointPeirceProjector (expTransport H S t) left right (expTransport H X t) := by
  simp only [jointPeirceProjector_apply, flow_mul,
    expTransport_peirceProjector_transport]

/-- The existing five grouped projectors are covariant under arbitrary
exponential conjugation, with the tripotent transported alongside them. -/
theorem expTransport_fiveGradeProjector_transport
    (H S X : A) (k : FiveGrade) (t : ℝ) :
    expTransport H (fiveGradeProjector S k X) t =
      fiveGradeProjector (expTransport H S t) k (expTransport H X t) := by
  cases k <;>
    simp only [fiveGradeProjector, gradeNegTwoProjector, gradeNegOneProjector,
      gradeZeroProjector, gradePosOneProjector, gradePosTwoProjector,
      LinearMap.add_apply, expTransport_add_seed,
      expTransport_jointPeirceProjector_transport]

/-- A generator commuting with S conserves each of its spectral polynomials. -/
theorem expTransport_peirceProjector {H S : A} (hHS : Commute H S)
    (s : PeirceSign) (t : ℝ) :
    expTransport H (peirceProjector S s) t = peirceProjector S s := by
  rw [expTransport_peirceProjector_transport, (conserved_iff_commute H S).mpr hHS t]

/-- Conservation of the three spectral polynomials is equivalent to
commutation with S. The converse uses S = Pplus - Pminus and needs no
tripotency assumption. Conservation of Pzero alone would not suffice. -/
theorem peirceProjectors_conserved_iff_commute (H S : A) :
    (∀ (s : PeirceSign) (t : ℝ),
      expTransport H (peirceProjector S s) t = peirceProjector S s) ↔
      Commute H S := by
  constructor
  · intro h
    apply (conserved_iff_commute H S).mp
    intro t
    have hpos : expTransport H (projPos S) t = projPos S := h .pos t
    have hneg : expTransport H (projNeg S) t = projNeg S := h .neg t
    calc
      expTransport H S t = expTransport H (projPos S - projNeg S) t := by
        rw [projPos_sub_projNeg]
      _ = expTransport H (projPos S) t - expTransport H (projNeg S) t :=
        expTransport_sub_seed H (projPos S) (projNeg S) t
      _ = projPos S - projNeg S := by rw [hpos, hneg]
      _ = S := projPos_sub_projNeg
  · intro h s t
    exact expTransport_peirceProjector h s t

/-- Exponential conjugation by a commuting generator intertwines each joint
Peirce projector with itself. -/
theorem expTransport_jointPeirceProjector {H S : A} (hHS : Commute H S)
    (left right : PeirceSign) (X : A) (t : ℝ) :
    expTransport H (jointPeirceProjector S left right X) t =
      jointPeirceProjector S left right (expTransport H X t) := by
  rw [expTransport_jointPeirceProjector_transport,
    (conserved_iff_commute H S).mpr hHS t]

/-- Exponential conjugation by a commuting generator intertwines every
existing five-grade projector with itself. -/
theorem expTransport_fiveGradeProjector {H S : A} (hHS : Commute H S)
    (k : FiveGrade) (X : A) (t : ℝ) :
    expTransport H (fiveGradeProjector S k X) t =
      fiveGradeProjector S k (expTransport H X t) := by
  rw [expTransport_fiveGradeProjector_transport,
    (conserved_iff_commute H S).mpr hHS t]

/-- Projector covariance preserves the actual range of each joint Peirce
projector, without replacing it by a scalar coordinate. -/
theorem expTransport_mem_jointPeirceRange {H S X : A} (hHS : Commute H S)
    (left right : PeirceSign)
    (hX : X ∈ LinearMap.range (jointPeirceProjector S left right)) (t : ℝ) :
    expTransport H X t ∈ LinearMap.range (jointPeirceProjector S left right) := by
  rcases hX with ⟨Y, hY⟩
  refine ⟨expTransport H Y t, ?_⟩
  rw [← expTransport_jointPeirceProjector hHS, hY]

/-- Each of the five owned ranges is preserved by the compatible flow.
This follows from covariance even without assuming tripotency. -/
theorem expTransport_mem_fiveGradeRange {H S X : A} (hHS : Commute H S)
    (k : FiveGrade) (hX : X ∈ fiveGradeRange S k) (t : ℝ) :
    expTransport H X t ∈ fiveGradeRange S k := by
  rcases hX with ⟨Y, hY⟩
  refine ⟨expTransport H Y t, ?_⟩
  rw [← expTransport_fiveGradeProjector hHS, hY]

/-- Invertibility of the real-time flow upgrades range preservation to an
exact membership equivalence. -/
theorem expTransport_mem_fiveGradeRange_iff {H S : A} (hHS : Commute H S)
    (k : FiveGrade) (X : A) (t : ℝ) :
    expTransport H X t ∈ fiveGradeRange S k ↔ X ∈ fiveGradeRange S k := by
  constructor
  · intro h
    have hi := expTransport_mem_fiveGradeRange hHS k h (-t)
    simpa only [flow_inverse] using hi
  · intro h
    exact expTransport_mem_fiveGradeRange hHS k h t

omit [NormedAlgebra ℚ A] in
/-- It already suffices that the orbit of S remains in its own degree-zero
range. Differentiating this condition gives a vanishing double adjoint;
tripotency makes the double-adjoint kernel equal the centralizer. -/
theorem commute_of_expTransport_self_mem_gradeZero {H S : A}
    (hS : S * S * S = S)
    (h : ∀ t : ℝ, expTransport H S t ∈ fiveGradeRange S .zero) :
    Commute H S := by
  have hz : (fun t : ℝ => S * expTransport H S t - expTransport H S t * S) =
      fun _ => (0 : A) := by
    funext t
    exact sub_eq_zero.mpr ((mem_fiveGradeRange_zero_iff_commute hS).mp (h t)).eq
  have hd := hasDerivAt_expTransport_at_zero H S
  have hc : HasDerivAt
      (fun t : ℝ => S * expTransport H S t - expTransport H S t * S)
      (S * ⁅H, S⁆ - ⁅H, S⁆ * S) 0 :=
    (hd.const_mul S).sub (hd.mul_const S)
  rw [hz] at hc
  have hderiv : S * (H * S - S * H) - (H * S - S * H) * S = 0 := by
    simpa only [Ring.lie_def] using
      hc.unique (hasDerivAt_const (0 : ℝ) (0 : A))
  have hdouble : (LieAlgebra.ad ℝ A S ^ 2) H = 0 := by
    change S * (S * H - H * S) - (S * H - H * S) * S = 0
    calc
      S * (S * H - H * S) - (S * H - H * S) * S =
          -(S * (H * S - S * H) - (H * S - S * H) * S) := by noncomm_ring
      _ = 0 := by rw [hderiv, neg_zero]
  have had := (ad_sq_apply_eq_zero_iff hS H).mp hdouble
  change S * H - H * S = 0 at had
  change H * S = S * H
  exact (sub_eq_zero.mp had).symm

/-- Preservation of the actual degree-zero range for all real times is
equivalent to commutation of the generator with the tripotent. -/
theorem gradeZero_preserved_iff_commute {H S : A} (hS : S * S * S = S) :
    (∀ (t : ℝ) (X : A), X ∈ fiveGradeRange S .zero →
      expTransport H X t ∈ fiveGradeRange S .zero) ↔ Commute H S := by
  constructor
  · intro h
    apply commute_of_expTransport_self_mem_gradeZero hS
    intro t
    exact h t S ((mem_fiveGradeRange_zero_iff_commute hS).mpr (Commute.refl S))
  · intro h t X hX
    exact expTransport_mem_fiveGradeRange h .zero hX t

/-- A complete tripotent grading is preserved by the real exponential flow
exactly when its generator commutes with the tripotent. -/
theorem all_fiveGradeRanges_preserved_iff_commute {H S : A} (hS : S * S * S = S) :
    (∀ (t : ℝ) (k : FiveGrade) (X : A), X ∈ fiveGradeRange S k →
      expTransport H X t ∈ fiveGradeRange S k) ↔ Commute H S := by
  constructor
  · intro h
    apply (gradeZero_preserved_iff_commute hS).mp
    intro t X hX
    exact h t .zero X hX
  · intro h t k X hX
    exact expTransport_mem_fiveGradeRange h k hX t

/-- For a proposed product generator J*K, commutation of each factor with S
is a sufficient condition on the actual operator product. An identity such
as J² = -1 does not replace these hypotheses. -/
theorem expTransport_mul_generator_mem_fiveGradeRange_iff {J K S : A}
    (hJ : Commute J S) (hK : Commute K S) (k : FiveGrade) (X : A) (t : ℝ) :
    expTransport (J * K) X t ∈ fiveGradeRange S k ↔ X ∈ fiveGradeRange S k := by
  have hJK : Commute (J * K) S := by
    change (J * K) * S = S * (J * K)
    calc
      (J * K) * S = J * (K * S) := mul_assoc J K S
      _ = J * (S * K) := by rw [hK.eq]
      _ = (J * S) * K := (mul_assoc J S K).symm
      _ = (S * J) * K := by rw [hJ.eq]
      _ = S * (J * K) := mul_assoc S J K
  exact expTransport_mem_fiveGradeRange_iff hJK k X t

/-- A commuting generator preserves every integer adjoint grade, even when
the grading element is not tripotent. -/
theorem expTransport_mem_adGrade {H S X : A} (hHS : Commute H S)
    {k : ℤ} (hX : X ∈ adGrade S k) (t : ℝ) :
    expTransport H X t ∈ adGrade S k := by
  rw [mem_adGrade_iff] at hX ⊢
  have hSfixed := (conserved_iff_commute H S).mpr hHS t
  calc
    adOp S (expTransport H X t) = expTransport H (adOp S X) t := by
      simp only [adOp, expTransport_sub_seed, flow_mul, hSfixed]
    _ = (k : ℝ) • expTransport H X t := by rw [hX, flow_smul]

/-- Inverse time gives equality of each integer grade under the flow. -/
theorem expTransport_mem_adGrade_iff {H S : A} (hHS : Commute H S)
    (k : ℤ) (X : A) (t : ℝ) :
    expTransport H X t ∈ adGrade S k ↔ X ∈ adGrade S k := by
  constructor
  · intro h
    have hi := expTransport_mem_adGrade hHS h (-t)
    simpa only [flow_inverse] using hi
  · intro h
    exact expTransport_mem_adGrade hHS h t

/-- The all-integer version of the proved tripotent flow rigidity theorem. -/
theorem all_adGrades_preserved_iff_commute {H S : A} (hS : S * S * S = S) :
    (∀ (t : ℝ) (k : ℤ) (X : A), X ∈ adGrade S k →
      expTransport H X t ∈ adGrade S k) ↔ Commute H S := by
  constructor
  · intro h
    apply (gradeZero_preserved_iff_commute hS).mp
    intro t X hX
    rw [fiveGradeRange_eq_adGrade hS] at hX ⊢
    exact h t 0 X hX
  · intro h t k X hX
    exact expTransport_mem_adGrade h hX t

/-- Opposite-grade factors give a grading-preserving product generator;
neither factor is required separately to commute with the tripotent. -/
theorem expTransport_opposite_grade_product_iff {J K S : A} {m : ℤ}
    (hJ : J ∈ adGrade S m) (hK : K ∈ adGrade S (-m))
    (k : ℤ) (X : A) (t : ℝ) :
    expTransport (J * K) X t ∈ adGrade S k ↔ X ∈ adGrade S k :=
  expTransport_mem_adGrade_iff (commute_mul_of_opposite_adGrades hJ hK).symm k X t

end Exponential
end InfoGeometry.OperatorAlgebra.TripotentExponentialFlow
