/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
import InfoGeometry.Synthesis.SouriauJordanAttentionBridge
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-!
# Group inverse of the finite Fisher--Souriau Hessian

For a nonempty finite score space, this file proves that the centered
reciprocal-weight operator is the group inverse of the Fisher--Souriau
Hessian `diag(p) - p pᵀ`. This is distinct from the Markov transition
Laplacian `1 - P`.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.FisherSouriauGroupInverse

open scoped BigOperators
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
open InfoGeometry.Synthesis.SouriauJordanAttentionBridge
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

noncomputable section

variable {m : ℕ} [Nonempty (Fin m)]

/-- Arithmetic mean of a finite score vector. -/
def arithmeticMean (x : Fin m → ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, x i

/-- Orthogonal projection onto the Euclidean complement of constant scores. -/
def centerScores : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun x := fun i => x i - arithmeticMean x
  map_add' x y := by
    funext i
    simp [arithmeticMean, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    funext i
    change c * x i - arithmeticMean (fun j => c * x j) =
      c * (x i - arithmeticMean x)
    unfold arithmeticMean
    rw [← Finset.mul_sum]
    ring

/-- Coordinatewise reciprocal Gibbs weighting. -/
def reciprocalAttentionWeights (s : Fin m → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun x := fun i => (souriauAttentionWeight s i)⁻¹ * x i
  map_add' x y := by
    funext i
    simp [mul_add]
  map_smul' c x := by
    funext i
    simp [mul_comm, mul_assoc]

/-- The actual Fisher--Souriau Hessian as a linear endomorphism. -/
def fisherHessianEnd (s : Fin m → ℝ) : Module.End ℝ (Fin m → ℝ) :=
  Matrix.toLin' (fun i j => fisherSouriauHessian s i j)

/-- The centered reciprocal-weight candidate for the group inverse. -/
def fisherHessianGroupInverseCandidate (s : Fin m → ℝ) :
    Module.End ℝ (Fin m → ℝ) :=
  centerScores.comp ((reciprocalAttentionWeights s).comp centerScores)

/-- The canonical weights sum to one. -/
theorem attentionWeights_sum_eq_one (s : Fin m → ℝ) :
    ∑ i : Fin m, souriauAttentionWeight s i = 1 :=
  (massieu_free_entropy_legendre_identity s
    (Classical.choice ‹Nonempty (Fin m)›)).1

/-- The coordinate average of a centered score vector is zero. -/
theorem centerScores_sum_eq_zero (x : Fin m → ℝ) :
    ∑ i : Fin m, centerScores x i = 0 := by
  classical
  have hm : (m : ℝ) ≠ 0 := by
    have hmN : 0 < m := by
      simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin m)›)
    exact_mod_cast (Nat.ne_of_gt hmN)
  change (∑ i : Fin m, (x i - arithmeticMean x)) = 0
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  change (∑ i : Fin m, x i) - (m : ℝ) * arithmeticMean x = 0
  unfold arithmeticMean
  field_simp [hm]
  ring

/-- Arithmetic centering removes a uniform coordinate shift. -/
theorem arithmeticMean_sub_const (x : Fin m → ℝ) (c : ℝ) :
    arithmeticMean (fun i => x i - c) = arithmeticMean x - c := by
  classical
  have hm : (m : ℝ) ≠ 0 := by
    have hmN : 0 < m := by
      simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin m)›)
    exact_mod_cast (Nat.ne_of_gt hmN)
  unfold arithmeticMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hm]
  ring

/-- The Fisher Hessian acts by multiplying deviations from the weighted mean. -/
theorem fisherHessianEnd_apply (s x : Fin m → ℝ) (i : Fin m) :
    fisherHessianEnd s x i =
      souriauAttentionWeight s i *
        (x i - souriauMomentMap s x) := by
  change Matrix.mulVec (fisherSouriauHessian s) x i = _
  exact fisherSouriauHessian_mulVec_apply s x i

/-- The centering operator is idempotent. -/
theorem centerScores_idempotent :
    (centerScores (m := m)).comp (centerScores (m := m)) = centerScores (m := m) := by
  apply LinearMap.ext
  intro x
  funext i
  change centerScores x i - arithmeticMean (centerScores x) = centerScores x i
  simp [arithmeticMean, centerScores_sum_eq_zero]

/-- Pointwise form of centering idempotence. -/
theorem centerScores_idempotent_apply (x : Fin m → ℝ) :
    centerScores (centerScores x) = centerScores x := by
  exact congrArg (fun f : Module.End ℝ (Fin m → ℝ) => f x)
    centerScores_idempotent

/-- Centering removes the constant score gauge from the weighted mean. -/
theorem souriauMomentMap_centerScores (s x : Fin m → ℝ) :
    souriauMomentMap s (centerScores x) =
      souriauMomentMap s x - arithmeticMean x := by
  classical
  unfold souriauMomentMap centerScores
  have hnorm := attentionWeights_sum_eq_one s
  calc
    (∑ i : Fin m,
        souriauAttentionWeight s i * (x i - arithmeticMean x))
        = (∑ i : Fin m, souriauAttentionWeight s i * x i) -
            (∑ i : Fin m, souriauAttentionWeight s i * arithmeticMean x) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
    _ = (∑ i : Fin m, souriauAttentionWeight s i * x i) -
          arithmeticMean x * (∑ i : Fin m, souriauAttentionWeight s i) := by
            rw [← Finset.sum_mul]
            ring
    _ = souriauMomentMap s x - arithmeticMean x := by
          rw [hnorm]
          simp [souriauMomentMap]

/-- Centering after reciprocal weighting of a centered vector recovers that
vector after applying the Fisher Hessian. -/
theorem center_reciprocal_fisher (s x : Fin m → ℝ) :
    centerScores (reciprocalAttentionWeights s (fisherHessianEnd s x)) =
      centerScores x := by
  have hvec :
      reciprocalAttentionWeights s (fisherHessianEnd s x) =
        fun j => x j - souriauMomentMap s x := by
    funext j
    have hH := fisherHessianEnd_apply s x j
    have hp : souriauAttentionWeight s j ≠ 0 :=
      ne_of_gt (souriauAttentionWeight_pos s j)
    dsimp [reciprocalAttentionWeights]
    rw [hH]
    field_simp [hp]
  rw [hvec]
  funext i
  change (x i - souriauMomentMap s x) -
      arithmeticMean (fun j => x j - souriauMomentMap s x) =
    x i - arithmeticMean x
  rw [arithmeticMean_sub_const]
  ring

/-- Reciprocal weighting cancels the Gibbs weights in the Souriau moment. -/
theorem souriauMomentMap_reciprocal (s x : Fin m → ℝ) :
    souriauMomentMap s (reciprocalAttentionWeights s x) =
      ∑ i : Fin m, x i := by
  classical
  unfold souriauMomentMap reciprocalAttentionWeights
  apply Finset.sum_congr rfl
  intro i hi
  have hp : souriauAttentionWeight s i ≠ 0 :=
    ne_of_gt (souriauAttentionWeight_pos s i)
  change souriauAttentionWeight s i *
      ((souriauAttentionWeight s i)⁻¹ * x i) = x i
  calc
    souriauAttentionWeight s i *
        ((souriauAttentionWeight s i)⁻¹ * x i) =
      (souriauAttentionWeight s i * (souriauAttentionWeight s i)⁻¹) * x i := by
        ring
    _ = x i := by simp [hp]

/-- The Fisher Hessian has coordinate-sum zero, as expected for a graph
Laplacian on the score space. -/
theorem fisherHessianEnd_sum_eq_zero (s x : Fin m → ℝ) :
    ∑ i : Fin m, fisherHessianEnd s x i = 0 := by
  rw [Finset.sum_congr rfl (fun i _ => fisherHessianEnd_apply s x i)]
  have hsplit : ∀ i : Fin m,
      souriauAttentionWeight s i * (x i - souriauMomentMap s x) =
        souriauAttentionWeight s i * x i -
          souriauAttentionWeight s i * souriauMomentMap s x := by
    intro i
    rw [mul_sub]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i)]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [attentionWeights_sum_eq_one]
  simp [souriauMomentMap]

/-- Applying the centering projection after the Fisher Hessian does nothing. -/
theorem centerScores_fisherHessian (s x : Fin m → ℝ) :
    centerScores (fisherHessianEnd s x) = fisherHessianEnd s x := by
  funext i
  change fisherHessianEnd s x i - arithmeticMean (fisherHessianEnd s x) =
    fisherHessianEnd s x i
  unfold arithmeticMean
  rw [fisherHessianEnd_sum_eq_zero]
  simp

/-- The Hessian followed by the centered reciprocal operator is the
centering projector. -/
theorem fisherHessian_candidate_left (s x : Fin m → ℝ) :
    fisherHessianEnd s (fisherHessianGroupInverseCandidate s x) =
      centerScores x := by
  let z := reciprocalAttentionWeights s (centerScores x)
  have hmom : souriauMomentMap s (centerScores z) = -arithmeticMean z := by
    rw [souriauMomentMap_centerScores]
    rw [souriauMomentMap_reciprocal]
    rw [centerScores_sum_eq_zero]
    simp [z]
  funext i
  change fisherHessianEnd s (centerScores z) i = centerScores x i
  rw [fisherHessianEnd_apply, hmom]
  have hp : souriauAttentionWeight s i ≠ 0 :=
    ne_of_gt (souriauAttentionWeight_pos s i)
  dsimp [z, reciprocalAttentionWeights, centerScores]
  field_simp [hp]
  ring

/-- The centered reciprocal operator followed by the Hessian is the
centering projector. -/
theorem fisherHessian_candidate_right (s x : Fin m → ℝ) :
    fisherHessianGroupInverseCandidate s (fisherHessianEnd s x) =
      centerScores x := by
  change centerScores
      (reciprocalAttentionWeights s
        (centerScores (fisherHessianEnd s x))) = centerScores x
  rw [centerScores_fisherHessian]
  exact center_reciprocal_fisher s x

/-- The centered reciprocal-weight operator is the group inverse (equivalently,
the index-one Drazin inverse) of the finite Fisher--Souriau Hessian. -/
theorem fisherSouriauHessian_groupInverse_formula (s : Fin m → ℝ) :
    IsGroupInverse (fisherHessianEnd s)
      (fisherHessianGroupInverseCandidate s) := by
  constructor
  · apply LinearMap.ext
    intro x
    change fisherHessianEnd s
        (fisherHessianGroupInverseCandidate s (fisherHessianEnd s x)) =
      fisherHessianEnd s x
    rw [fisherHessian_candidate_left, centerScores_fisherHessian]
  constructor
  · apply LinearMap.ext
    intro x
    change fisherHessianGroupInverseCandidate s
        (fisherHessianEnd s (fisherHessianGroupInverseCandidate s x)) =
      fisherHessianGroupInverseCandidate s x
    rw [fisherHessian_candidate_left]
    change centerScores
        (reciprocalAttentionWeights s (centerScores (centerScores x))) =
      centerScores (reciprocalAttentionWeights s (centerScores x))
    rw [centerScores_idempotent_apply]
  · apply LinearMap.ext
    intro x
    change fisherHessianEnd s (fisherHessianGroupInverseCandidate s x) =
      fisherHessianGroupInverseCandidate s (fisherHessianEnd s x)
    rw [fisherHessian_candidate_left, fisherHessian_candidate_right]

/-- The explicit group-inverse formula agrees with the repository's
    finite-dimensional, choice-based Drazin inverse. -/
theorem fisherSouriauHessian_candidate_eq_drazinInverse
    (s : Fin m → ℝ) :
    fisherHessianGroupInverseCandidate s =
      InfoGeometry.Singular.Drazin.drazinInverse (fisherHessianEnd s) := by
  apply InfoGeometry.Singular.Drazin.drazinInverse_eq_of_spec_any_index
    (fisherHessianEnd s)
  have hGroup := fisherSouriauHessian_groupInverse_formula s
  have hCanonical :
      InfoGeometry.Canonical.Drazin.IsDrazinInverse
        (fisherHessianEnd s) (fisherHessianGroupInverseCandidate s) 1 :=
    IsGroupInverse.toDrazin hGroup
  exact InfoGeometry.Singular.Drazin.IsDrazinInverse.mk
    hCanonical.idempotent hCanonical.comm hCanonical.power.symm

/-- The concrete Drazin dynamic projector of the Fisher Hessian is the
Euclidean score-centering projection. -/
theorem fisherHessian_drazin_left_projector_eq_centerScores
    (s : Fin m → ℝ) :
    (fisherHessianEnd s).comp
        (InfoGeometry.Singular.Drazin.drazinInverse (fisherHessianEnd s)) =
      centerScores := by
  apply LinearMap.ext
  intro x
  change fisherHessianEnd s
      (InfoGeometry.Singular.Drazin.drazinInverse (fisherHessianEnd s) x) =
    centerScores x
  rw [← fisherSouriauHessian_candidate_eq_drazinInverse]
  exact fisherHessian_candidate_left s x

/-- The reverse Drazin dynamic projector has the same concrete action. -/
theorem fisherHessian_drazin_right_projector_eq_centerScores
    (s : Fin m → ℝ) :
    (InfoGeometry.Singular.Drazin.drazinInverse (fisherHessianEnd s)).comp
        (fisherHessianEnd s) = centerScores := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Singular.Drazin.drazinInverse (fisherHessianEnd s)
      (fisherHessianEnd s x) = centerScores x
  rw [← fisherSouriauHessian_candidate_eq_drazinInverse]
  exact fisherHessian_candidate_right s x

/-- The Fisher--Souriau Hessian annihilates exactly the constant score
vectors; its harmonic sector is the projective score-gauge direction. -/
theorem fisherHessianEnd_eq_zero_iff_constant
    (s x : Fin m → ℝ) :
    fisherHessianEnd s x = 0 ↔ ∃ c : ℝ, ∀ i : Fin m, x i = c := by
  change Matrix.mulVec (fisherSouriauHessian s) x = 0 ↔
    ∃ c : ℝ, ∀ i : Fin m, x i = c
  exact fisherSouriauHessian_kernel_iff_constant s x

/-- The group-inverse energy of a score is the reciprocal-weighted squared
    norm of its centered component. -/
theorem fisherHessian_groupInverse_energy_eq_centered_reciprocal_norm
    (s v : Fin m → ℝ) :
    (∑ i : Fin m,
      fisherHessianGroupInverseCandidate s v i *
        fisherHessianEnd s (fisherHessianGroupInverseCandidate s v) i) =
      ∑ i : Fin m,
        (centerScores v i) ^ 2 * (souriauAttentionWeight s i)⁻¹ := by
  have hcoordinate :
      (fun i : Fin m =>
        fisherHessianGroupInverseCandidate s v i * centerScores v i) =
      (fun i : Fin m =>
        (reciprocalAttentionWeights s (centerScores v) i -
          arithmeticMean (reciprocalAttentionWeights s (centerScores v))) *
            centerScores v i) := by
    funext i
    rfl
  have hpair :
      (∑ i : Fin m,
        fisherHessianGroupInverseCandidate s v i * centerScores v i) =
      ∑ i : Fin m,
        reciprocalAttentionWeights s (centerScores v) i * centerScores v i := by
    calc
      (∑ i : Fin m,
          fisherHessianGroupInverseCandidate s v i * centerScores v i) =
        ∑ i : Fin m,
          (reciprocalAttentionWeights s (centerScores v) i -
            arithmeticMean (reciprocalAttentionWeights s (centerScores v))) *
              centerScores v i := by
                exact congrArg (fun f : Fin m → ℝ => ∑ i : Fin m, f i)
                  hcoordinate
      _ = (∑ i : Fin m,
            reciprocalAttentionWeights s (centerScores v) i * centerScores v i) -
          ∑ i : Fin m,
            arithmeticMean (reciprocalAttentionWeights s (centerScores v)) *
              centerScores v i := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = ∑ i : Fin m,
          reciprocalAttentionWeights s (centerScores v) i * centerScores v i := by
            rw [← Finset.mul_sum, centerScores_sum_eq_zero]
            ring
  rw [fisherHessian_candidate_left s v, hpair]
  apply Finset.sum_congr rfl
  intro i hi
  simp [reciprocalAttentionWeights]
  ring

/-- The group-inverse energy is nonnegative. It vanishes on the constant-score
    gauge direction, so positivity is asserted only as semidefiniteness here. -/
theorem fisherHessian_groupInverse_energy_nonneg
    (s v : Fin m → ℝ) :
    0 ≤ ∑ i : Fin m,
      fisherHessianGroupInverseCandidate s v i *
        fisherHessianEnd s (fisherHessianGroupInverseCandidate s v) i := by
  rw [fisherHessian_groupInverse_energy_eq_centered_reciprocal_norm]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (le_of_lt (souriauAttentionWeight_pos s i)))

/-- The arithmetic mean of a constant score vector is that constant. -/
theorem arithmeticMean_const (c : ℝ) :
    arithmeticMean (fun _ : Fin m => c) = c := by
  classical
  have hm : (m : ℝ) ≠ 0 := by
    have hmN : 0 < m := by
      simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin m)›)
    exact_mod_cast (Nat.ne_of_gt hmN)
  unfold arithmeticMean
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hm]

/-- The group-inverse energy vanishes exactly on constant score vectors. -/
theorem fisherHessian_groupInverse_energy_eq_zero_iff_constant
    (s v : Fin m → ℝ) :
    (∑ i : Fin m,
      fisherHessianGroupInverseCandidate s v i *
        fisherHessianEnd s (fisherHessianGroupInverseCandidate s v) i) = 0 ↔
      ∃ c : ℝ, ∀ i : Fin m, v i = c := by
  rw [fisherHessian_groupInverse_energy_eq_centered_reciprocal_norm]
  constructor
  · intro h
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => mul_nonneg (sq_nonneg (centerScores v i))
        (inv_nonneg.mpr (le_of_lt (souriauAttentionWeight_pos s i))))).mp h
    refine ⟨arithmeticMean v, ?_⟩
    intro i
    have hterm := hterms i (Finset.mem_univ i)
    have hinv : (souriauAttentionWeight s i)⁻¹ ≠ 0 :=
      inv_ne_zero (ne_of_gt (souriauAttentionWeight_pos s i))
    have hsq : (centerScores v i) ^ 2 = 0 :=
      (mul_eq_zero.mp hterm).resolve_right hinv
    have hcenter : centerScores v i = 0 := (sq_eq_zero_iff).mp hsq
    change v i - arithmeticMean v = 0 at hcenter
    exact sub_eq_zero.mp hcenter
  · rintro ⟨c, hc⟩
    have hcenter : centerScores v = 0 := by
      funext i
      change v i - arithmeticMean v = 0
      rw [hc i]
      rw [show v = fun _ : Fin m => c by funext j; exact hc j, arithmeticMean_const]
      ring
    simp [hcenter]

end

end InfoGeometry.Synthesis.FisherSouriauGroupInverse
