/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Synthesis.FisherSouriauGroupInverse
import InfoGeometry.Singular.MoorePenrose

set_option autoImplicit false

namespace InfoGeometry.Synthesis.FisherSouriauMoorePenrose

open scoped BigOperators
open InfoGeometry.Synthesis.FisherSouriauGroupInverse
open InfoGeometry.Singular.MoorePenrose

noncomputable section

variable {m : ℕ} [Nonempty (Fin m)]

abbrev Score := EuclideanSpace ℝ (Fin m)
abbrev ScoreFn := Fin m → ℝ

def scoreEquiv : Score (m := m) ≃ₗ[ℝ] ScoreFn (m := m) :=
  WithLp.linearEquiv 2 ℝ (Fin m → ℝ)

def transportEnd (T : Module.End ℝ (ScoreFn (m := m))) :
    Module.End ℝ (Score (m := m)) :=
  (scoreEquiv (m := m)).symm.toLinearMap.comp
    (T.comp (scoreEquiv (m := m)).toLinearMap)

def transportCLM (T : Module.End ℝ (ScoreFn (m := m))) :
    Score (m := m) →L[ℝ] Score (m := m) :=
  LinearMap.toContinuousLinearMap (transportEnd T)

def fisherHessianCLM (s : Fin m → ℝ) : Score (m := m) →L[ℝ] Score (m := m) :=
  transportCLM (fisherHessianEnd s)

def fisherHessianGroupInverseCandidateCLM (s : Fin m → ℝ) :
    Score (m := m) →L[ℝ] Score (m := m) :=
  transportCLM (fisherHessianGroupInverseCandidate s)

def centerCLM : Score (m := m) →L[ℝ] Score (m := m) :=
  transportCLM (centerScores (m := m))

omit [Nonempty (Fin m)] in
private theorem arithmeticMean_pairing (x y : ScoreFn (m := m)) :
    arithmeticMean x * (∑ i : Fin m, y i) =
      (∑ i : Fin m, x i) * arithmeticMean y := by
  unfold arithmeticMean
  ring

omit [Nonempty (Fin m)] in
private theorem centerScores_coordinate_pairing (x y : ScoreFn (m := m)) :
    (∑ i : Fin m, centerScores (m := m) x i * y i) =
      (∑ i : Fin m, x i * centerScores (m := m) y i) := by
  change (∑ i : Fin m, (x i - arithmeticMean x) * y i) =
    (∑ i : Fin m, x i * (y i - arithmeticMean y))
  calc
    (∑ i : Fin m, (x i - arithmeticMean x) * y i) =
        (∑ i : Fin m, x i * y i) - arithmeticMean x * (∑ i : Fin m, y i) := by
      calc
        _ = ∑ i : Fin m, (x i * y i - arithmeticMean x * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (∑ i : Fin m, x i * y i) -
        (∑ i : Fin m, x i) * arithmeticMean y := by
      rw [arithmeticMean_pairing]
    _ = ∑ i : Fin m, (x i * y i - x i * arithmeticMean y) := by
      calc
        _ = (∑ i : Fin m, x i * y i) -
            ∑ i : Fin m, x i * arithmeticMean y := by
              rw [← Finset.sum_mul]
        _ = ∑ i : Fin m, (x i * y i - x i * arithmeticMean y) := by
              rw [Finset.sum_sub_distrib]
    _ = ∑ i : Fin m, x i * (y i - arithmeticMean y) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

omit [Nonempty (Fin m)] in
private theorem centerCLM_symmetric :
    ((centerCLM (m := m) : Score (m := m) →L[ℝ] Score (m := m)) :
      Score (m := m) →ₗ[ℝ] Score (m := m)).IsSymmetric := by
  intro x y
  simp only [PiLp.inner_apply, Real.inner_apply]
  change (∑ i : Fin m,
      (scoreEquiv (m := m) (centerCLM (m := m) x) i) *
        (scoreEquiv (m := m) y i)) =
    (∑ i : Fin m,
      (scoreEquiv (m := m) x i) *
        (scoreEquiv (m := m) (centerCLM (m := m) y) i))
  simp only [centerCLM, transportCLM, transportEnd]
  exact centerScores_coordinate_pairing (scoreEquiv (m := m) x)
    (scoreEquiv (m := m) y)

omit [Nonempty (Fin m)] in
private theorem centerCLM_isSelfAdjoint : IsSelfAdjoint (centerCLM (m := m)) :=
  centerCLM_symmetric.clm_adjoint_eq

omit [Nonempty (Fin m)] in
private theorem transportCLM_comp (A B : Module.End ℝ (ScoreFn (m := m))) :
    (transportCLM A).comp (transportCLM B) = transportCLM (A.comp B) := by
  apply ContinuousLinearMap.ext
  intro x
  change (scoreEquiv (m := m)).symm
      (A ((scoreEquiv (m := m))
        ((scoreEquiv (m := m)).symm (B ((scoreEquiv (m := m)) x))))) =
    (scoreEquiv (m := m)).symm
      ((A.comp B) ((scoreEquiv (m := m)) x))
  simp only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply]

private theorem fisherHessianCLM_comp_candidate (s : Fin m → ℝ) :
    (fisherHessianCLM s).comp (fisherHessianGroupInverseCandidateCLM s) =
      centerCLM (m := m) := by
  change (transportCLM (fisherHessianEnd s)).comp
      (transportCLM (fisherHessianGroupInverseCandidate s)) =
    transportCLM (centerScores (m := m))
  have hOwner :
      (fisherHessianEnd s).comp (fisherHessianGroupInverseCandidate s) =
        centerScores (m := m) := by
    apply LinearMap.ext
    intro x
    exact fisherHessian_candidate_left s x
  rw [transportCLM_comp, hOwner]

private theorem candidateCLM_comp_fisherHessian (s : Fin m → ℝ) :
    (fisherHessianGroupInverseCandidateCLM s).comp (fisherHessianCLM s) =
      centerCLM (m := m) := by
  change (transportCLM (fisherHessianGroupInverseCandidate s)).comp
      (transportCLM (fisherHessianEnd s)) =
    transportCLM (centerScores (m := m))
  have hOwner :
      (fisherHessianGroupInverseCandidate s).comp (fisherHessianEnd s) =
        centerScores (m := m) := by
    apply LinearMap.ext
    intro x
    exact fisherHessian_candidate_right s x
  rw [transportCLM_comp, hOwner]

private theorem fisherHessianCLM_triple (s : Fin m → ℝ) :
    ((fisherHessianCLM s).comp (fisherHessianGroupInverseCandidateCLM s)).comp
        (fisherHessianCLM s) = fisherHessianCLM s := by
  change ((transportCLM (fisherHessianEnd s)).comp
      (transportCLM (fisherHessianGroupInverseCandidate s))).comp
      (transportCLM (fisherHessianEnd s)) =
    transportCLM (fisherHessianEnd s)
  have hOwner :
      ((fisherHessianEnd s).comp
        (fisherHessianGroupInverseCandidate s)).comp
        (fisherHessianEnd s) = fisherHessianEnd s := by
    simpa only [Module.End.mul_eq_comp] using
      (fisherSouriauHessian_groupInverse_formula s).1
  rw [transportCLM_comp, transportCLM_comp, hOwner]

private theorem candidateCLM_triple (s : Fin m → ℝ) :
    ((fisherHessianGroupInverseCandidateCLM s).comp (fisherHessianCLM s)).comp
        (fisherHessianGroupInverseCandidateCLM s) =
      fisherHessianGroupInverseCandidateCLM s := by
  change ((transportCLM (fisherHessianGroupInverseCandidate s)).comp
      (transportCLM (fisherHessianEnd s))).comp
      (transportCLM (fisherHessianGroupInverseCandidate s)) =
    transportCLM (fisherHessianGroupInverseCandidate s)
  have hOwner :
      ((fisherHessianGroupInverseCandidate s).comp
        (fisherHessianEnd s)).comp
        (fisherHessianGroupInverseCandidate s) =
      fisherHessianGroupInverseCandidate s := by
    simpa only [Module.End.mul_eq_comp] using
      (fisherSouriauHessian_groupInverse_formula s).2.1
  rw [transportCLM_comp, transportCLM_comp, hOwner]

/-- The explicit Fisher--Souriau group-inverse candidate satisfies the four
Moore--Penrose equations on each nonempty finite real Euclidean score space. -/
theorem fisherSouriauHessian_groupInverse_isMoorePenrose (s : Fin m → ℝ) :
    IsMoorePenroseInverseCLM (fisherHessianCLM s)
      (fisherHessianGroupInverseCandidateCLM s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fisherHessianCLM_triple s
  · exact candidateCLM_triple s
  · rw [fisherHessianCLM_comp_candidate]
    simp only [ContinuousLinearMap.star_eq_adjoint]
    exact centerCLM_symmetric.clm_adjoint_eq
  · rw [candidateCLM_comp_fisherHessian]
    simp only [ContinuousLinearMap.star_eq_adjoint]
    exact centerCLM_symmetric.clm_adjoint_eq

omit [Nonempty (Fin m)] in
/-- The range of the finite-dimensional Fisher--Souriau Hessian is closed. -/
theorem fisherHessianCLM_range_closed (s : Fin m → ℝ) :
    IsClosed ((fisherHessianCLM s).range : Set (Score (m := m))) := by
  exact (fisherHessianCLM s).range.closed_of_finiteDimensional

/-- The explicit Fisher--Souriau group-inverse candidate is the canonical
closed-range Moore--Penrose inverse on the finite Euclidean score space. -/
theorem fisherSouriauHessian_groupInverseCandidate_eq_moorePenroseInverse
    (s : Fin m → ℝ) :
    fisherHessianGroupInverseCandidateCLM s =
      moorePenroseInverse (fisherHessianCLM s)
        (fisherHessianCLM_range_closed s) := by
  apply MoorePenrose_unique
  · simpa [IsMoorePenroseInverse, IsMoorePenroseInverseCLM,
      ContinuousLinearMap.mul_def] using
      fisherSouriauHessian_groupInverse_isMoorePenrose s
  · simpa [IsMoorePenroseInverse, IsMoorePenroseInverseCLM,
      ContinuousLinearMap.mul_def] using
      isMoorePenroseInverse_moorePenroseInverse
        (fisherHessianCLM s) (fisherHessianCLM_range_closed s)

end

end InfoGeometry.Synthesis.FisherSouriauMoorePenrose
