import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.BornRuleCore

/-!
# Hilbertization interface for real split-Krein operators

This owner isolates the exact Krein-to-Hilbert adjoint transport available from
the repository's fundamental symmetry.  It does not assert that a Krein
operator is already an unbounded Kasparov operator, nor does it construct a
group-level equivariant `KK` class.
-/

noncomputable section

namespace InfoGeometry.KK.RealSplitKreinHilbertizationBridge

open InfoGeometry.Krein
open scoped InnerProductSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

/-- The Hilbertized representative obtained by composing with the fundamental
symmetry `J`. -/
noncomputable def hilbertized (T : EndH H) : EndH H :=
  (KreinSpace.jCLM (H := H)).comp T

@[simp] theorem hilbertized_apply (T : EndH H) (x : H) :
    hilbertized T x = KreinSpace.jCLM (H := H) (T x) := rfl

@[simp] theorem hilbertized_id :
    hilbertized (ContinuousLinearMap.id ℝ H) =
      KreinSpace.jCLM (H := H) := by
  simp [hilbertized]

theorem kreinInner_jCLM_left_eq_hilbertInner (u v : H) :
    KreinSpace.kreinInner (KreinSpace.jCLM (H := H) u) v =
      ⟪u, v⟫_ℝ := by
  simpa [KreinSpace.jCLM_apply] using
    (InfoGeometry.Krein.BornRuleCore.kreinInner_fundamentalSymmetry_left
      (H := H) u v)

theorem kreinInner_jCLM_right_eq_hilbertInner (u v : H) :
    KreinSpace.kreinInner u (KreinSpace.jCLM (H := H) v) =
      ⟪u, v⟫_ℝ := by
  simpa [KreinSpace.jCLM_apply] using
    (InfoGeometry.Krein.BornRuleCore.kreinInner_fundamentalSymmetry_right
      (H := H) u v)

theorem kreinSelfAdjoint_iff_hilbertized_selfAdjoint (T : EndH H) :
    KreinSpace.IsKreinSelfAdjoint T ↔
      IsSelfAdjoint (hilbertized T) := by
  simpa [hilbertized] using
    (KreinSpace.isKreinSelfAdjoint_iff_j_comp_selfAdjoint T)

/-- Hilbert skew-adjointness after Hilbertization. -/
def IsHilbertSkewAdjoint (T : EndH H) : Prop :=
  ContinuousLinearMap.adjoint T = -T

theorem kreinSkewAdjoint_iff_hilbertized_skewAdjoint (T : EndH H) :
    KreinSpace.IsKreinSkewAdjoint T ↔
      IsHilbertSkewAdjoint (hilbertized T) := by
  constructor
  · intro h
    change KreinSpace.kreinAdjoint T = -T at h
    change ContinuousLinearMap.adjoint (hilbertized T) = -hilbertized T
    ext x
    have hj : Function.Injective (KreinSpace.jCLM (H := H)) := by
      intro u v huv
      have h' := congrArg (fun z => KreinSpace.jCLM (H := H) z) huv
      simpa using h'
    apply hj
    have hx := congrArg (fun S : EndH H => S x) h
    simpa [hilbertized, ContinuousLinearMap.adjoint_comp,
      KreinSpace.kreinAdjoint_apply, KreinSpace.jCLM_apply,
      KreinSpace.J_invol] using hx
  · intro h
    change ContinuousLinearMap.adjoint (hilbertized T) = -hilbertized T at h
    change KreinSpace.kreinAdjoint T = -T
    ext x
    have hx := congrArg (fun S : EndH H => S x) h
    simpa [hilbertized, ContinuousLinearMap.adjoint_comp,
      KreinSpace.kreinAdjoint_apply, KreinSpace.jCLM_apply,
      KreinSpace.J_invol] using congrArg
      (fun y => KreinSpace.jCLM (H := H) y) hx

theorem kreinAdjoint_formula (T : EndH H) :
    KreinSpace.kreinAdjoint T =
      (KreinSpace.jCLM (H := H)).comp
        ((ContinuousLinearMap.adjoint T).comp (KreinSpace.jCLM (H := H))) := rfl

theorem kreinAdjoint_involutive (T : EndH H) :
    KreinSpace.kreinAdjoint (KreinSpace.kreinAdjoint T) = T :=
  KreinSpace.kreinAdjoint_involutive T

theorem isKreinSelfAdjoint_of_commute_j (T : EndH H)
    (hcomm : (KreinSpace.jCLM (H := H)).comp T = T.comp (KreinSpace.jCLM (H := H))) :
    KreinSpace.IsKreinSelfAdjoint T ↔ IsSelfAdjoint T := by
  rw [KreinSpace.isKreinSelfAdjoint_iff_adjoint_eq_j_conj]
  rw [← hcomm]
  rw [KreinSpace.jCLM_comp_jCLM_comp]
  exact ContinuousLinearMap.isSelfAdjoint_iff'.symm

theorem isKreinSkewAdjoint_of_anticommute_j (T : EndH H)
    (hanticomm : (KreinSpace.jCLM (H := H)).comp T = - (T.comp (KreinSpace.jCLM (H := H)))) :
    KreinSpace.IsKreinSkewAdjoint T ↔ IsSelfAdjoint T := by
  dsimp [KreinSpace.IsKreinSkewAdjoint, KreinSpace.kreinAdjoint]
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  constructor
  · intro hKrein
    have h : (KreinSpace.jCLM (H := H)).comp
        ((KreinSpace.jCLM (H := H)).comp
          ((ContinuousLinearMap.adjoint T).comp (KreinSpace.jCLM (H := H)))) =
        (KreinSpace.jCLM (H := H)).comp (-T) := by
      rw [hKrein]
    rw [KreinSpace.jCLM_comp_jCLM_comp] at h
    have h2 : ((ContinuousLinearMap.adjoint T).comp (KreinSpace.jCLM (H := H))).comp
        (KreinSpace.jCLM (H := H)) =
        ((KreinSpace.jCLM (H := H)).comp (-T)).comp (KreinSpace.jCLM (H := H)) := by
      rw [h]
    rw [KreinSpace.comp_jCLM_comp_jCLM] at h2
    rw [ContinuousLinearMap.comp_neg, hanticomm, neg_neg,
        KreinSpace.comp_jCLM_comp_jCLM] at h2
    exact h2
  · intro hSelf
    rw [hSelf]
    rw [← ContinuousLinearMap.comp_assoc]
    rw [hanticomm]
    rw [ContinuousLinearMap.neg_comp]
    rw [KreinSpace.comp_jCLM_comp_jCLM]

end InfoGeometry.KK.RealSplitKreinHilbertizationBridge
