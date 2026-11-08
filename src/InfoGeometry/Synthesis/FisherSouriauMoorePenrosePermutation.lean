/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Synthesis.FisherSouriauGroupInversePermutation
import InfoGeometry.Synthesis.FisherSouriauMoorePenrose

/-!
# Euclidean Fisher–Souriau Moore–Penrose permutation naturality

The function-space permutation intertwiners and the identification of the
explicit Fisher group inverse with the canonical Moore–Penrose inverse are
transported to the finite Euclidean score space. This is finite-dimensional
operator naturality; it does not assert Dikin-barrier or colimit compatibility.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.FisherSouriauMoorePenrosePermutation

open InfoGeometry.Synthesis.FisherSouriauGroupInverse
open InfoGeometry.Synthesis.FisherSouriauGroupInversePermutation
open InfoGeometry.Synthesis.FisherSouriauMoorePenrose
open InfoGeometry.Singular.MoorePenrose

noncomputable section

variable {m : ℕ} [Nonempty (Fin m)]

/-- Coordinate relabeling transported to the Euclidean score carrier. -/
def scorePermutationCLM (σ : Equiv.Perm (Fin m)) :
    Score (m := m) →L[ℝ] Score (m := m) :=
  transportCLM (scorePermutation σ)

private theorem scoreEquiv_transportCLM_apply
    (T : Module.End ℝ (ScoreFn (m := m))) (x : Score (m := m)) :
    scoreEquiv (m := m) (transportCLM T x) = T (scoreEquiv (m := m) x) := by
  simp [transportCLM, transportEnd]

/-- The Euclidean Fisher Hessian intertwines simultaneous score and coordinate
relabeling, with the convention `(Pσ x)` corresponding to `x ∘ σ`. -/
theorem fisherHessianCLM_intertwines_perm
    (σ : Equiv.Perm (Fin m)) (s : Fin m → ℝ) :
    (scorePermutationCLM σ).comp (fisherHessianCLM s) =
      (fisherHessianCLM (s ∘ σ)).comp (scorePermutationCLM σ) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (scoreEquiv (m := m)).injective
  change scoreEquiv (m := m)
      (scorePermutationCLM σ (fisherHessianCLM s x)) =
    scoreEquiv (m := m)
      (fisherHessianCLM (s ∘ σ) (scorePermutationCLM σ x))
  simp only [scorePermutationCLM, fisherHessianCLM]
  rw [scoreEquiv_transportCLM_apply, scoreEquiv_transportCLM_apply,
    scoreEquiv_transportCLM_apply, scoreEquiv_transportCLM_apply]
  have h := congrArg (fun T : Module.End ℝ (ScoreFn (m := m)) =>
    T (scoreEquiv (m := m) x))
      (fisherHessianEnd_linear_intertwines_perm σ s)
  simpa [scorePermutation] using h

/-- The explicit finite group inverse intertwines the Euclidean coordinate
relabeling. -/
theorem fisherHessianGroupInverseCandidateCLM_intertwines_perm
    (σ : Equiv.Perm (Fin m)) (s : Fin m → ℝ) :
    (scorePermutationCLM σ).comp (fisherHessianGroupInverseCandidateCLM s) =
      (fisherHessianGroupInverseCandidateCLM (s ∘ σ)).comp
        (scorePermutationCLM σ) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (scoreEquiv (m := m)).injective
  change scoreEquiv (m := m)
      (scorePermutationCLM σ (fisherHessianGroupInverseCandidateCLM s x)) =
    scoreEquiv (m := m)
      (fisherHessianGroupInverseCandidateCLM (s ∘ σ) (scorePermutationCLM σ x))
  simp only [scorePermutationCLM, fisherHessianGroupInverseCandidateCLM]
  rw [scoreEquiv_transportCLM_apply, scoreEquiv_transportCLM_apply,
    scoreEquiv_transportCLM_apply, scoreEquiv_transportCLM_apply]
  have h := congrArg (fun T : Module.End ℝ (ScoreFn (m := m)) =>
    T (scoreEquiv (m := m) x))
      (fisherHessianGroupInverseCandidate_linear_intertwines_perm σ s)
  simpa [scorePermutation] using h

/-- The canonical closed-range Moore–Penrose inverse of the Fisher Hessian
intertwines the same finite coordinate relabeling. The proof transports the
already identified explicit group-inverse candidate; no extra isometry premise
is needed for this operator equation. -/
theorem fisherHessianMoorePenrose_intertwines_perm
    (σ : Equiv.Perm (Fin m)) (s : Fin m → ℝ) :
    (scorePermutationCLM σ).comp
        (moorePenroseInverse (fisherHessianCLM s)
          (fisherHessianCLM_range_closed s)) =
      (moorePenroseInverse (fisherHessianCLM (s ∘ σ))
          (fisherHessianCLM_range_closed (s ∘ σ))).comp
        (scorePermutationCLM σ) := by
  rw [← fisherSouriauHessian_groupInverseCandidate_eq_moorePenroseInverse s,
    ← fisherSouriauHessian_groupInverseCandidate_eq_moorePenroseInverse (s ∘ σ)]
  exact fisherHessianGroupInverseCandidateCLM_intertwines_perm σ s

end

end InfoGeometry.Synthesis.FisherSouriauMoorePenrosePermutation
