/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.FisherSouriauGroupInverse
import InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification

/-!
# Permutation naturality of the finite Fisher--Souriau group inverse

Relabeling score coordinates by a finite permutation relabels the centered
reciprocal-weight group-inverse response by the same permutation. The result
is a finite coordinate-reindexing theorem; it does not assert colimit or
Dikin-barrier compatibility.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.FisherSouriauGroupInversePermutation

open InfoGeometry.Synthesis.FisherSouriauGroupInverse
open InfoGeometry.Synthesis.Cl55FiveGradedDrazinDikinUnification
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis

noncomputable section

variable {m : ℕ}

/-- Arithmetic averaging is unchanged by a permutation of the coordinates. -/
theorem arithmeticMean_comp_perm (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) :
    arithmeticMean (x ∘ σ) = arithmeticMean x := by
  unfold arithmeticMean
  change (m : ℝ)⁻¹ * (∑ i : Fin m, x (σ i)) =
    (m : ℝ)⁻¹ * (∑ i : Fin m, x i)
  rw [Equiv.sum_comp σ (fun i => x i)]

/-- Euclidean score centering commutes with coordinate relabeling. -/
theorem centerScores_comp_perm (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) :
    centerScores (x ∘ σ) = centerScores x ∘ σ := by
  funext i
  change x (σ i) - arithmeticMean (x ∘ σ) =
    x (σ i) - arithmeticMean x
  rw [arithmeticMean_comp_perm]

/-- Reciprocal Gibbs weighting commutes with the same coordinate relabeling. -/
theorem reciprocalAttentionWeights_comp_perm
    (σ : Equiv.Perm (Fin m)) (s x : Fin m → ℝ) :
    reciprocalAttentionWeights (s ∘ σ) (x ∘ σ) =
      reciprocalAttentionWeights s x ∘ σ := by
  funext i
  change (souriauAttentionWeight (s ∘ σ) i)⁻¹ * x (σ i) =
    (souriauAttentionWeight s (σ i))⁻¹ * x (σ i)
  rw [show souriauAttentionWeight (s ∘ σ) i =
      souriauAttentionWeight s (σ i) by
        simpa [gibbsProb] using gibbsProb_perm_equivariant σ s i]

/-- The explicit finite Fisher--Souriau group-inverse response is natural under
permutations of both the score coordinates and the input vector. -/
theorem fisherHessianGroupInverseCandidate_perm_equivariant
    (σ : Equiv.Perm (Fin m)) (s x : Fin m → ℝ) :
    fisherHessianGroupInverseCandidate (s ∘ σ) (x ∘ σ) =
      fisherHessianGroupInverseCandidate s x ∘ σ := by
  unfold fisherHessianGroupInverseCandidate
  change centerScores
      (reciprocalAttentionWeights (s ∘ σ) (centerScores (x ∘ σ))) =
    centerScores (reciprocalAttentionWeights s (centerScores x)) ∘ σ
  rw [centerScores_comp_perm σ x,
    reciprocalAttentionWeights_comp_perm σ s (centerScores x),
    centerScores_comp_perm σ (reciprocalAttentionWeights s (centerScores x))]

/-- The linear score-coordinate relabeling used by the pointwise naturality
theorems. Its convention is `(scorePermutation σ) x = x ∘ σ`. -/
def scorePermutation (σ : Equiv.Perm (Fin m)) :
    Module.End ℝ (Fin m → ℝ) where
  toFun x := x ∘ σ
  map_add' x y := by
    funext i
    rfl
  map_smul' c x := by
    funext i
    rfl

/-- The Fisher--Souriau Hessian endomorphism intertwines the same
parameter-changing coordinate relabeling. -/
theorem fisherHessianEnd_linear_intertwines_perm
    (σ : Equiv.Perm (Fin m)) (s : Fin m → ℝ) :
    (scorePermutation σ).comp (fisherHessianEnd s) =
      (fisherHessianEnd (s ∘ σ)).comp (scorePermutation σ) := by
  apply LinearMap.ext
  intro x
  funext i
  change (∑ j : Fin m, fisherSouriauLaplacian s (σ i) j * x j) =
    ∑ j : Fin m, fisherSouriauLaplacian (s ∘ σ) i j * x (σ j)
  calc
    (∑ j : Fin m, fisherSouriauLaplacian s (σ i) j * x j) =
        ∑ j : Fin m, fisherSouriauLaplacian s (σ i) (σ j) * x (σ j) :=
      (Equiv.sum_comp σ
        (fun j : Fin m => fisherSouriauLaplacian s (σ i) j * x j)).symm
    _ = ∑ j : Fin m, fisherSouriauLaplacian (s ∘ σ) i j * x (σ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [fisherSouriauLaplacian_perm_equivariant σ s i j]

/-- The group-inverse response is an intertwiner for coordinate permutation.
Composition is read right to left, so the score is transformed to `s ∘ σ`
and the input vector is relabeled by the same `σ`. -/
theorem fisherHessianGroupInverseCandidate_linear_intertwines_perm
    (σ : Equiv.Perm (Fin m)) (s : Fin m → ℝ) :
    (scorePermutation σ).comp (fisherHessianGroupInverseCandidate s) =
      (fisherHessianGroupInverseCandidate (s ∘ σ)).comp
        (scorePermutation σ) := by
  apply LinearMap.ext
  intro x
  exact (fisherHessianGroupInverseCandidate_perm_equivariant σ s x).symm

/-- The canonical index-one Drazin inverse inherits the same parameter-changing
intertwining law from the explicit group-inverse candidate. -/
theorem fisherHessianDrazinInverse_linear_intertwines_perm
    [Nonempty (Fin m)] (σ : Equiv.Perm (Fin m)) (s : Fin m → ℝ) :
    (scorePermutation σ).comp
        (InfoGeometry.Singular.Drazin.drazinInverse (fisherHessianEnd s)) =
      (InfoGeometry.Singular.Drazin.drazinInverse
        (fisherHessianEnd (s ∘ σ))).comp (scorePermutation σ) := by
  rw [← fisherSouriauHessian_candidate_eq_drazinInverse s,
    ← fisherSouriauHessian_candidate_eq_drazinInverse (s ∘ σ)]
  exact fisherHessianGroupInverseCandidate_linear_intertwines_perm σ s

/-- The finite Fisher--Drazin quadratic readout is invariant under relabeling
of both the score coordinates and the input vector. This is a finite
permutation naturality result; it does not identify the readout with a
self-concordant barrier or a colimit Dikin metric. -/
theorem fisherHessianGroupInverse_energy_perm_invariant
    [Nonempty (Fin m)]
    (σ : Equiv.Perm (Fin m)) (s v : Fin m → ℝ) :
    (∑ i : Fin m,
      fisherHessianGroupInverseCandidate (s ∘ σ) (v ∘ σ) i *
        fisherHessianEnd (s ∘ σ)
          (fisherHessianGroupInverseCandidate (s ∘ σ) (v ∘ σ)) i) =
      ∑ i : Fin m,
        fisherHessianGroupInverseCandidate s v i *
          fisherHessianEnd s (fisherHessianGroupInverseCandidate s v) i := by
  rw [fisherHessian_groupInverse_energy_eq_centered_reciprocal_norm,
    fisherHessian_groupInverse_energy_eq_centered_reciprocal_norm]
  calc
    (∑ i : Fin m,
        (centerScores (v ∘ σ) i) ^ 2 *
          (souriauAttentionWeight (s ∘ σ) i)⁻¹) =
      ∑ i : Fin m,
        (centerScores v (σ i)) ^ 2 *
          (souriauAttentionWeight s (σ i))⁻¹ := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [centerScores_comp_perm, Function.comp_apply]
            rw [show souriauAttentionWeight (s ∘ σ) i =
              souriauAttentionWeight s (σ i) by
                simpa [gibbsProb] using gibbsProb_perm_equivariant σ s i]
    _ = ∑ i : Fin m,
        (centerScores v i) ^ 2 *
          (souriauAttentionWeight s i)⁻¹ :=
      Equiv.sum_comp σ
        (fun i : Fin m => (centerScores v i) ^ 2 *
          (souriauAttentionWeight s i)⁻¹)

end

end InfoGeometry.Synthesis.FisherSouriauGroupInversePermutation
