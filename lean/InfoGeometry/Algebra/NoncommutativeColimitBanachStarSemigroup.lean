/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeColimitCStarCompletionAndOperatorSemigroup

/-!
# Banach $\star$-Algebra Structure & Global Operator Lindblad Semigroup on $\widehat{\mathcal{C}\ell}_\infty^{\mathrm{op}}(A)$

This module elevates `ClInfOpCompletion A` from a `NonUnitalNormedRing` to a full
**Banach $\star$-algebra** and extends the non-scalar operator Lindblad semigroup globally from
finite-scale coherent modes to all of `ClInfOpCompletion A`:

1. **Banach $\star$-Algebra Structure (`NormedSpace ℝ`, `StarRing`-laws, `NormedStarGroup`)**:
   Equips `ClInfOp A` and `ClInfOpCompletion A` with `NormedSpace ℝ`, `InvolutiveStar`,
   `StarAddMonoid`, `StarMul`, and `NormedStarGroup` (with `star := completionOpStar`),
   and proves $\star$-covariance of `completionSuperTrace` on all of `ClInfOpCompletion A`.
2. **Global Coherence Projection & Non-Scalar Operator Semigroup on `ClInfOpCompletion A`**:
   Proves that `coherenceMode` and `towerScalar n a * coherenceMode n X` commute with
   `bottEmbed`, lifting `coherenceProjOp` and `cohSemigroupOp m₀ t` to globally Lipschitz
   maps on `ClInfOp A` and hence to continuous maps `coherenceProjCompletion` and
   `cohSemigroupCompletion m₀ t` on `ClInfOpCompletion A`.
3. **Global Semigroup Law, Coercive Decay & Supertrace Annihilation**:
   Proves for ALL `z : ClInfOpCompletion A`:
   - `cohSemigroupCompletion m₀ 0 z = coherenceProjCompletion z`
   - `cohSemigroupCompletion m₀ (s + t) z = cohSemigroupCompletion m₀ s (cohSemigroupCompletion m₀ t z)`
   - `‖cohSemigroupCompletion m₀ t z‖ ≤ Real.exp (-t * μ^2) * ‖coherenceProjCompletion z‖`
   - `completionSuperTrace (cohSemigroupCompletion m₀ t z) = 0`.
-/

namespace InfoGeometry.Algebra.NoncommutativeColimitBanachStarSemigroup

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis
open InfoGeometry.Algebra.NoncommutativeColimitNormedLindbladBridge
open InfoGeometry.Algebra.NoncommutativeColimitSemigroupAndOperatorGap
open InfoGeometry.Algebra.NoncommutativeColimitCStarCompletionAndOperatorSemigroup

universe u

/-!
## Part 1: Banach $\star$-Algebra Structure on `ClInfOp A` and `ClInfOpCompletion A`
-/

section BanachStarAlgebra

variable {A : Type u} [NormedRing A]

private def toCl' (x : ClInfOp A) : ClInf A := x

noncomputable instance instSMulRealClInfOp [NormedAlgebra ℝ A] : SMul ℝ (ClInfOp A) :=
  inferInstanceAs (SMul ℝ (ClInf A))

noncomputable instance instModuleRealClInfOp [NormedAlgebra ℝ A] : Module ℝ (ClInfOp A) :=
  inferInstanceAs (Module ℝ (ClInf A))

lemma smul_toClInfOp [NormedAlgebra ℝ A] (r : ℝ) (n : ℕ) (X : ClTower A n) :
    r • toClInfOp n X = toClInfOp n (r • X) := rfl

noncomputable instance instNormedSpaceRealClInfOp [NormedAlgebra ℝ A] :
    NormedSpace ℝ (ClInfOp A) where
  norm_smul_le r x := by
    rcases exists_toClInf (toCl' x) with ⟨n, X, hx⟩
    have hrx : toCl' (r • x) = toClInf n (r • X) := by
      change r • toCl' x = toClInf n (r • X)
      rw [hx, smul_toClInf]
    change clInfOpNorm (toCl' (r • x)) ≤ ‖r‖ * clInfOpNorm (toCl' x)
    rw [hrx, hx, clInfOpNorm_toClInf, clInfOpNorm_toClInf, opSumNorm_smul, Real.norm_eq_abs]

lemma star_toClInfOp [StarRing A] (n : ℕ) (X : ClTower A n) :
    star (toClInfOp n X) = toClInfOp n (@Star.star _ (instStarRingClTower n).toStar X) :=
  star_toClInf n X

noncomputable instance instNormedStarGroupClInfOp [StarRing A] [NormedStarGroup A] :
    NormedStarGroup (ClInfOp A) where
  norm_star_le x := by
    have h_dist : dist (star x) (star (0 : ClInfOp A)) = dist x (0 : ClInfOp A) :=
      clInfOp_star_isometry.dist_eq x 0
    rw [star_zero, dist_zero_right, dist_zero_right] at h_dist
    exact h_dist.le

noncomputable instance instStarClInfOpCompletion [StarRing A] [NormedStarGroup A] :
    Star (ClInfOpCompletion A) where
  star := completionOpStar

lemma completionOpStar_coe [StarRing A] [NormedStarGroup A] (x : ClInfOp A) :
    star (x : ClInfOpCompletion A) = ((star x : ClInfOp A) : ClInfOpCompletion A) :=
  UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous x

noncomputable instance instInvolutiveStarClInfOpCompletion [StarRing A] [NormedStarGroup A] :
    InvolutiveStar (ClInfOpCompletion A) where
  star_involutive z := completionOpStar_isometry_and_involutive.2 z

noncomputable instance instStarAddMonoidClInfOpCompletion [StarRing A] [NormedStarGroup A] :
    StarAddMonoid (ClInfOpCompletion A) where
  star_add z w := by
    induction z, w using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          ((UniformSpace.Completion.continuous_map (f := (Star.star : ClInfOp A → ClInfOp A))).comp
            continuous_add)
          (((UniformSpace.Completion.continuous_map (f := (Star.star : ClInfOp A → ClInfOp A))).comp
            continuous_fst).add
           ((UniformSpace.Completion.continuous_map (f := (Star.star : ClInfOp A → ClInfOp A))).comp
            continuous_snd))
    | ih x y =>
        change completionOpStar ((x : ClInfOpCompletion A) + (y : ClInfOpCompletion A)) =
          completionOpStar (x : ClInfOpCompletion A) + completionOpStar (y : ClInfOpCompletion A)
        dsimp only [completionOpStar]
        rw [← UniformSpace.Completion.coe_add,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            ← UniformSpace.Completion.coe_add, star_add]

noncomputable instance instStarMulClInfOpCompletion [StarRing A] [NormedStarGroup A] :
    StarMul (ClInfOpCompletion A) where
  star_mul z w := by
    induction z, w using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          ((UniformSpace.Completion.continuous_map (f := (Star.star : ClInfOp A → ClInfOp A))).comp
            continuous_mul)
          (((UniformSpace.Completion.continuous_map (f := (Star.star : ClInfOp A → ClInfOp A))).comp
            continuous_snd).mul
           ((UniformSpace.Completion.continuous_map (f := (Star.star : ClInfOp A → ClInfOp A))).comp
            continuous_fst))
    | ih x y =>
        change completionOpStar ((x : ClInfOpCompletion A) * (y : ClInfOpCompletion A)) =
          completionOpStar (y : ClInfOpCompletion A) * completionOpStar (x : ClInfOpCompletion A)
        dsimp only [completionOpStar]
        rw [← clInfOpCompletion_coe_mul,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            ← clInfOpCompletion_coe_mul, star_mul]

noncomputable instance instNormedStarGroupClInfOpCompletion [StarRing A] [NormedStarGroup A] :
    NormedStarGroup (ClInfOpCompletion A) where
  norm_star_le z := by
    have h_dist : dist (star z) (star (0 : ClInfOpCompletion A)) = dist z (0 : ClInfOpCompletion A) :=
      completionOpStar_isometry_and_involutive.1.dist_eq z 0
    rw [star_zero, dist_zero_right, dist_zero_right] at h_dist
    exact h_dist.le

/-- Continuous $\star$-involution on the scalar completion `UniformSpace.Completion A`. -/
noncomputable def completionAStar [StarRing A] [NormedStarGroup A] :
    UniformSpace.Completion A → UniformSpace.Completion A :=
  UniformSpace.Completion.map (Star.star : A → A)

private lemma towerTrace_neg : ∀ (n : ℕ) (Y : ClTower A n), towerTrace (-Y) = -towerTrace Y
  | 0,     _ => rfl
  | n + 1, M => by
      dsimp only [towerTrace]
      have h00 : (-M) 0 0 = -M 0 0 := rfl
      have h11 : (-M) 1 1 = -M 1 1 := rfl
      rw [h00, h11, towerTrace_neg n (M 0 0), towerTrace_neg n (M 1 1), neg_add]

lemma superTrace_star_clTower [StarRing A] :
    ∀ (n : ℕ) (X : ClTower A n),
      superTrace (@Star.star _ (instStarRingClTower n).toStar X) = star (superTrace X)
  | 0,     a => by simp [superTrace, towerTrace, chiralityOp]
  | n + 1, M => by
      let _ : StarRing (ClTower A n) := instStarRingClTower n
      dsimp only [superTrace, towerTrace, chiralityOp]
      have h00 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) *
          (@Star.star _ (instStarRingClTower (n + 1)).toStar M)) 0 0 =
          chiralityOp n * star (M 0 0) := by
        simp [mat2, Matrix.mul_apply, Fin.sum_univ_two]
      have h11 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) *
          (@Star.star _ (instStarRingClTower (n + 1)).toStar M)) 1 1 =
          -(chiralityOp n * star (M 1 1)) := by
        simp [mat2, Matrix.mul_apply, Fin.sum_univ_two]
      have h00' : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 0 =
          chiralityOp n * M 0 0 := by
        simp [mat2, Matrix.mul_apply, Fin.sum_univ_two]
      have h11' : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 1 =
          -(chiralityOp n * M 1 1) := by
        simp [mat2, Matrix.mul_apply, Fin.sum_univ_two]
      change towerTrace ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) *
              (@Star.star _ (instStarRingClTower (n + 1)).toStar M)) 0 0) +
             towerTrace ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) *
              (@Star.star _ (instStarRingClTower (n + 1)).toStar M)) 1 1) =
             star (towerTrace ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 0) +
                   towerTrace ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 1))
      rw [h00, h11, h00', h11', towerTrace_neg, towerTrace_neg, star_add, star_neg]
      have ih0 := superTrace_star_clTower n (M 0 0)
      have ih1 := superTrace_star_clTower n (M 1 1)
      dsimp only [superTrace] at ih0 ih1
      rw [ih0, ih1]

lemma clInfSuperTrace_star [StarRing A] (x : ClInf A) :
    clInfSuperTrace (star x) = star (clInfSuperTrace x) := by
  rcases exists_toClInf x with ⟨n, X, rfl⟩
  rw [star_toClInf]
  dsimp only [clInfSuperTrace, toClInf]
  rw [Quotient.lift_mk, Quotient.lift_mk]
  exact superTrace_star_clTower n X

/-- **Global $\star$-Covariance of `completionSuperTrace`**:
For every `z : ClInfOpCompletion A`, `completionSuperTrace (star z) = completionAStar (completionSuperTrace z)`. -/
theorem completionSuperTrace_star [StarRing A] [NormedStarGroup A]
    (z : ClInfOpCompletion A) :
    completionSuperTrace (star z) = completionAStar (completionSuperTrace z) := by
  have h_lip_str : UniformContinuous (fun x : ClInfOp A => clInfSuperTrace (x : ClInf A)) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by
      change dist (clInfSuperTrace (x : ClInf A)) (clInfSuperTrace (y : ClInf A)) ≤ 1 * dist x y
      rw [one_mul]
      exact clInfSuperTrace_global_lipschitz x y)).uniformContinuous
  have h_star_A : UniformContinuous (Star.star : A → A) :=
    (Isometry.of_dist_eq (fun a b => by
      rw [dist_eq_norm, dist_eq_norm, ← star_sub, norm_star])).uniformContinuous
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map)
        (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map)
  | ih x =>
      change completionSuperTrace (completionOpStar (x : ClInfOpCompletion A)) =
        completionAStar (completionSuperTrace (x : ClInfOpCompletion A))
      dsimp only [completionSuperTrace, completionAStar, completionOpStar]
      rw [UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
          UniformSpace.Completion.map_coe h_lip_str,
          UniformSpace.Completion.map_coe h_lip_str,
          UniformSpace.Completion.map_coe h_star_A]
      congr 1
      exact clInfSuperTrace_star (toCl' x)

end BanachStarAlgebra

/-!
## Part 2: Global Coherence Projection & Non-Scalar Semigroup on `ClInfOpCompletion A`
-/

section GlobalOperatorSemigroup

variable {A : Type u} [NormedRing A]

lemma bottEmbed_towerScalar_mul (n : ℕ) (a : A) (X : ClTower A n) :
    bottEmbed (towerScalar n a * X) = towerScalar (n + 1) a * bottEmbed X := by
  apply ext_fin2 <;> simp [bottEmbed, towerScalar, mat2]

lemma bottEmbed_coherenceMode (n : ℕ) (X : ClTower A n) :
    bottEmbed (coherenceMode n X) = coherenceMode (n + 1) (bottEmbed X) := by
  dsimp [coherenceMode, bottEmbed]
  have hP : cantorProj (A := A) (n + 1) = mat2 (cantorProj n) 0 0 0 := rfl
  have h1P : (1 : ClTower A (n + 1)) - mat2 (cantorProj n) 0 0 0 =
      mat2 (1 - cantorProj n) 0 0 1 := by
    apply ext_fin2 <;> simp [mat2]
  rw [hP, h1P]
  apply ext_fin2 <;> simp [mat2]

lemma bottEmbedIter_coherenceMode {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (coherenceMode n X) = coherenceMode (n + k) (bottEmbedIter k X) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [bottEmbedIter]
      change bottEmbed (bottEmbedIter k (coherenceMode n X)) =
        coherenceMode ((n + k) + 1) (bottEmbed (bottEmbedIter k X))
      rw [ih, bottEmbed_coherenceMode]

lemma bottEmbedIter_towerScalar_coherence {n : ℕ} (k : ℕ) (a : A) (X : ClTower A n) :
    bottEmbedIter k (towerScalar n a * coherenceMode n X) =
      towerScalar (n + k) a * coherenceMode (n + k) (bottEmbedIter k X) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [bottEmbedIter]
      change bottEmbed (bottEmbedIter k (towerScalar n a * coherenceMode n X)) =
        towerScalar ((n + k) + 1) a * coherenceMode ((n + k) + 1) (bottEmbed (bottEmbedIter k X))
      rw [ih, bottEmbed_towerScalar_mul, bottEmbed_coherenceMode]

lemma coherenceMode_idem (n : ℕ) (X : ClTower A n) :
    coherenceMode n (coherenceMode n X) = coherenceMode n X := by
  have hP := cantorProj_idem (A := A) n
  have h1P : (1 - cantorProj (A := A) n) * (1 - cantorProj n) = 1 - cantorProj n := by
    calc (1 - cantorProj (A := A) n) * (1 - cantorProj n)
      _ = 1 - cantorProj n - cantorProj n + cantorProj n * cantorProj n := by noncomm_ring
      _ = 1 - cantorProj n := by rw [hP]; abel
  dsimp [coherenceMode]
  calc (1 - cantorProj n) * ((1 - cantorProj n) * X * cantorProj n) * cantorProj n
    _ = ((1 - cantorProj n) * (1 - cantorProj n)) * X * (cantorProj n * cantorProj n) := by
        noncomm_ring
    _ = (1 - cantorProj n) * X * cantorProj n := by rw [h1P, hP]

lemma opSumNorm_cantorProj (n : ℕ) :
    opSumNorm n (cantorProj (A := A) n) = ‖(1 : A)‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show cantorProj (A := A) (n + 1) = bottEmbed (cantorProj n) from rfl,
          opSumNorm_bottEmbed, ih]

lemma opSumNorm_coherenceMode_le (n : ℕ) (X : ClTower A n) :
    opSumNorm n (coherenceMode n X) ≤ (‖(1 : A)‖ + ‖(1 : A)‖ ^ 2) * opSumNorm n X := by
  have h_eq : coherenceMode n X = X * cantorProj n - cantorProj n * X * cantorProj n := by
    dsimp [coherenceMode]
    noncomm_ring
  rw [h_eq, sub_eq_add_neg]
  refine le_trans (opSumNorm_add_le n _ _) ?_
  rw [opSumNorm_neg]
  have h1 : opSumNorm n (X * cantorProj n) ≤ opSumNorm n X * ‖(1 : A)‖ := by
    simpa only [opSumNorm_cantorProj] using opSumNorm_mul_le n X (cantorProj n)
  have h2 : opSumNorm n (cantorProj n * X * cantorProj n) ≤ ‖(1 : A)‖ ^ 2 * opSumNorm n X := by
    calc opSumNorm n (cantorProj n * X * cantorProj n)
      _ ≤ opSumNorm n (cantorProj n * X) * opSumNorm n (cantorProj n) := opSumNorm_mul_le n _ _
      _ ≤ (opSumNorm n (cantorProj n) * opSumNorm n X) * opSumNorm n (cantorProj n) :=
          mul_le_mul_of_nonneg_right (opSumNorm_mul_le n _ _) (opSumNorm_nonneg n _)
      _ = ‖(1 : A)‖ ^ 2 * opSumNorm n X := by
          rw [opSumNorm_cantorProj]; ring
  linarith

private lemma heq_coherenceMode {m n : ℕ} (h : m = n) {X : ClTower A m} {Y : ClTower A n}
    (heq : HEq X Y) : HEq (coherenceMode m X) (coherenceMode n Y) := by
  subst h; cases eq_of_heq heq; rfl

private lemma heq_towerScalar_coherenceMode (a : A) {m n : ℕ} (h : m = n)
    {X : ClTower A m} {Y : ClTower A n} (heq : HEq X Y) :
    HEq (towerScalar m a * coherenceMode m X) (towerScalar n a * coherenceMode n Y) := by
  subst h; cases eq_of_heq heq; rfl

/-- Global coherence-sector projection `P_coh : ClInfOp A → ClInfOp A`. -/
def coherenceProjOp (x : ClInfOp A) : ClInfOp A :=
  Quotient.liftOn (toCl' x)
    (fun u => toClInf u.1 (coherenceMode u.1 u.2))
    (fun _ _ ⟨k₁, k₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨k₁, k₂, h_dim, ?_⟩
      rw [bottEmbedIter_coherenceMode, bottEmbedIter_coherenceMode]
      exact heq_coherenceMode h_dim heq_u)

lemma coherenceProjOp_toClInfOp (n : ℕ) (X : ClTower A n) :
    coherenceProjOp (toClInfOp n X) = toClInfOp n (coherenceMode n X) := rfl

lemma coherenceProjOp_sub (x y : ClInfOp A) :
    coherenceProjOp (x - y) = coherenceProjOp x - coherenceProjOp y := by
  rcases toClInf_lift_two (toCl' x) (toCl' y) with ⟨n, X, Y, hx, hy⟩
  have hx' : x = toClInfOp n X := hx
  have hy' : y = toClInfOp n Y := hy
  rw [hx', hy', sub_toClInfOp, coherenceProjOp_toClInfOp, coherenceProjOp_toClInfOp,
      coherenceProjOp_toClInfOp, sub_toClInfOp]
  congr 1
  dsimp [coherenceMode]
  noncomm_ring

theorem coherenceProjOp_lipschitz :
    LipschitzWith ⟨‖(1 : A)‖ + ‖(1 : A)‖ ^ 2, by positivity⟩ (coherenceProjOp (A := A)) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← coherenceProjOp_sub]
  rcases exists_toClInf (toCl' (x - y)) with ⟨n, Z, hxy⟩
  have hxy' : x - y = toClInfOp n Z := hxy
  rw [hxy', coherenceProjOp_toClInfOp, norm_toClInfOp, norm_toClInfOp]
  exact opSumNorm_coherenceMode_le n Z

/-- Continuous global coherence-sector projection on `ClInfOpCompletion A`. -/
noncomputable def coherenceProjCompletion : ClInfOpCompletion A → ClInfOpCompletion A :=
  UniformSpace.Completion.map (coherenceProjOp (A := A))

lemma coherenceProjCompletion_coe (x : ClInfOp A) :
    coherenceProjCompletion (x : ClInfOpCompletion A) =
      ((coherenceProjOp x : ClInfOp A) : ClInfOpCompletion A) :=
  UniformSpace.Completion.map_coe coherenceProjOp_lipschitz.uniformContinuous x

/-- Global non-scalar operator Lindblad semigroup `T_t : ClInfOp A → ClInfOp A` on the coherence sector. -/
noncomputable def cohSemigroupOp [NormedAlgebra ℝ A] (m₀ : A) (t : ℝ) (x : ClInfOp A) :
    ClInfOp A :=
  Quotient.liftOn (toCl' x)
    (fun u => toClInf u.1 (towerScalar u.1 (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode u.1 u.2))
    (fun _ _ ⟨k₁, k₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨k₁, k₂, h_dim, ?_⟩
      rw [bottEmbedIter_towerScalar_coherence, bottEmbedIter_towerScalar_coherence]
      exact heq_towerScalar_coherenceMode _ h_dim heq_u)

lemma cohSemigroupOp_toClInfOp [NormedAlgebra ℝ A] (m₀ : A) (t : ℝ) (n : ℕ) (X : ClTower A n) :
    cohSemigroupOp m₀ t (toClInfOp n X) =
      toClInfOp n (towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode n X) := rfl

lemma cohSemigroupOp_sub [NormedAlgebra ℝ A] (m₀ : A) (t : ℝ) (x y : ClInfOp A) :
    cohSemigroupOp m₀ t (x - y) = cohSemigroupOp m₀ t x - cohSemigroupOp m₀ t y := by
  rcases toClInf_lift_two (toCl' x) (toCl' y) with ⟨n, X, Y, hx, hy⟩
  have hx' : x = toClInfOp n X := hx
  have hy' : y = toClInfOp n Y := hy
  rw [hx', hy', sub_toClInfOp, cohSemigroupOp_toClInfOp, cohSemigroupOp_toClInfOp,
      cohSemigroupOp_toClInfOp, sub_toClInfOp]
  congr 1
  dsimp [coherenceMode]
  noncomm_ring

theorem cohSemigroupOp_lipschitz [NormedAlgebra ℝ A] (m₀ : A) (t : ℝ) :
    LipschitzWith
      ⟨‖NormedSpace.exp (-t • (m₀ * m₀))‖ * (‖(1 : A)‖ + ‖(1 : A)‖ ^ 2), by positivity⟩
      (cohSemigroupOp m₀ t) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← cohSemigroupOp_sub]
  rcases exists_toClInf (toCl' (x - y)) with ⟨n, Z, hxy⟩
  have hxy' : x - y = toClInfOp n Z := hxy
  rw [hxy', cohSemigroupOp_toClInfOp, norm_toClInfOp, norm_toClInfOp]
  calc opSumNorm n (towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode n Z)
    _ ≤ ‖NormedSpace.exp (-t • (m₀ * m₀))‖ * opSumNorm n (coherenceMode n Z) :=
        opSumNorm_towerScalar_mul_le n _ _
    _ ≤ ‖NormedSpace.exp (-t • (m₀ * m₀))‖ * ((‖(1 : A)‖ + ‖(1 : A)‖ ^ 2) * opSumNorm n Z) :=
        mul_le_mul_of_nonneg_left (opSumNorm_coherenceMode_le n Z) (norm_nonneg _)
    _ = (‖NormedSpace.exp (-t • (m₀ * m₀))‖ * (‖(1 : A)‖ + ‖(1 : A)‖ ^ 2)) * opSumNorm n Z := by
        ring

/-- Global continuous non-scalar operator Lindblad semigroup on `ClInfOpCompletion A`. -/
noncomputable def cohSemigroupCompletion [NormedAlgebra ℝ A] (m₀ : A) (t : ℝ) :
    ClInfOpCompletion A → ClInfOpCompletion A :=
  UniformSpace.Completion.map (cohSemigroupOp m₀ t)

lemma cohSemigroupCompletion_coe [NormedAlgebra ℝ A] (m₀ : A) (t : ℝ) (x : ClInfOp A) :
    cohSemigroupCompletion m₀ t (x : ClInfOpCompletion A) =
      ((cohSemigroupOp m₀ t x : ClInfOp A) : ClInfOpCompletion A) :=
  UniformSpace.Completion.map_coe (cohSemigroupOp_lipschitz m₀ t).uniformContinuous x

/-- **Global Semigroup Identity Law on `ClInfOpCompletion A`**: `T_0(z) = P_coh(z)`. -/
theorem cohSemigroupCompletion_zero [NormedAlgebra ℝ A] (m₀ : A) (z : ClInfOpCompletion A) :
    cohSemigroupCompletion m₀ 0 z = coherenceProjCompletion z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq UniformSpace.Completion.continuous_map UniformSpace.Completion.continuous_map
  | ih x =>
      rcases exists_toClInf (toCl' x) with ⟨n, X, hx⟩
      have hx' : x = toClInfOp n X := hx
      rw [hx', cohSemigroupCompletion_coe, coherenceProjCompletion_coe,
          cohSemigroupOp_toClInfOp, coherenceProjOp_toClInfOp]
      simp [NormedSpace.exp_zero, towerScalar_one]

/-- **Global Semigroup Composition Law on `ClInfOpCompletion A`**: `T_{s+t}(z) = T_s(T_t(z))`. -/
theorem cohSemigroupCompletion_add [NormedAlgebra ℝ A] [CompleteSpace A] (m₀ : A) (s t : ℝ)
    (z : ClInfOpCompletion A) :
    cohSemigroupCompletion m₀ (s + t) z =
      cohSemigroupCompletion m₀ s (cohSemigroupCompletion m₀ t z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        UniformSpace.Completion.continuous_map
        (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map)
  | ih x =>
      rcases exists_toClInf (toCl' x) with ⟨n, X, hx⟩
      have hx' : x = toClInfOp n X := hx
      rw [hx', cohSemigroupCompletion_coe m₀ (s + t), cohSemigroupCompletion_coe m₀ t,
          cohSemigroupOp_toClInfOp, cohSemigroupOp_toClInfOp,
          cohSemigroupCompletion_coe m₀ s, cohSemigroupOp_toClInfOp]
      congr 2
      have h_comm : Commute (-s • (m₀ * m₀)) (-t • (m₀ * m₀)) := by
        dsimp [Commute, SemiconjBy]
        simp [mul_assoc, smul_comm t s]
      have h_exp : NormedSpace.exp (-(s + t) • (m₀ * m₀)) =
          NormedSpace.exp (-s • (m₀ * m₀)) * NormedSpace.exp (-t • (m₀ * m₀)) := by
        let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
        rw [show -(s + t) • (m₀ * m₀) = -s • (m₀ * m₀) + -t • (m₀ * m₀) by
          rw [← add_smul, neg_add]]
        exact NormedSpace.exp_add_of_commute h_comm
      have h_coh_mul : coherenceMode n (towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) *
          coherenceMode n X) =
          towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode n X := by
        have h_comm_coh :
            coherenceMode n (towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode n X) =
            towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode n (coherenceMode n X) := by
          dsimp [coherenceMode]
          calc (1 - cantorProj n) * (towerScalar n _ * ((1 - cantorProj n) * X * cantorProj n)) *
              cantorProj n
            _ = ((1 - cantorProj n) * towerScalar n _) *
                ((1 - cantorProj n) * X * cantorProj n) * cantorProj n := by noncomm_ring
            _ = (towerScalar n _ * (1 - cantorProj n)) *
                ((1 - cantorProj n) * X * cantorProj n) * cantorProj n := by
                rw [sub_mul, mul_sub, one_mul, mul_one, ← towerScalar_comm_cantorProj]
            _ = towerScalar n _ * ((1 - cantorProj n) * ((1 - cantorProj n) * X * cantorProj n) *
                cantorProj n) := by noncomm_ring
        rw [h_comm_coh, coherenceMode_idem]
      rw [h_coh_mul, ← mul_assoc, ← towerScalar_mul, h_exp]

/-- **Global Coercive Exponential Decay on ALL of `ClInfOpCompletion A`**:
Under the Euler mass-gap contraction bound, `‖T_t(z)‖ ≤ exp(-t μ²) * ‖P_coh(z)‖` for every
`z : ClInfOpCompletion A` (not merely finite-scale elements). -/
theorem cohSemigroupCompletion_coercive_decay [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
    (m₀ : A) (t μ : ℝ)
    (h_gap : ∀ k : ℕ, t * (μ * μ) ≤ k →
      ‖1 - (t / (k : ℝ)) • (m₀ * m₀)‖ ≤ 1 - (t / (k : ℝ)) * (μ * μ))
    (z : ClInfOpCompletion A) :
    ‖cohSemigroupCompletion m₀ t z‖ ≤
      Real.exp (-t * (μ * μ)) * ‖coherenceProjCompletion z‖ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_le
        (continuous_norm.comp UniformSpace.Completion.continuous_map)
        (continuous_const.mul (continuous_norm.comp UniformSpace.Completion.continuous_map))
  | ih x =>
      rcases exists_toClInf (toCl' x) with ⟨n, X, hx⟩
      have hx' : x = toClInfOp n X := hx
      rw [hx', cohSemigroupCompletion_coe, coherenceProjCompletion_coe,
          cohSemigroupOp_toClInfOp, coherenceProjOp_toClInfOp]
      exact operator_lindblad_coercive_decay m₀ t μ h_gap n X

private lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by simp [towerTrace, towerTrace_zero n]

lemma superTrace_towerScalar_coherenceMode (a : A) :
    ∀ (n : ℕ) (X : ClTower A n),
      superTrace (towerScalar n a * coherenceMode n X) = 0
  | 0,     X => by simp [superTrace, towerTrace, coherenceMode, cantorProj]
  | n + 1, X => by
      dsimp only [superTrace]
      have h1P : (1 : ClTower A (n + 1)) - mat2 (cantorProj n) 0 0 0 =
          mat2 (1 - cantorProj n) 0 0 1 := by
        apply ext_fin2 <;> simp [mat2]
      let Xm : ClTower A (n + 1) := X
      let M : ClTower A (n + 1) :=
        mat2 (chiralityOp n) 0 0 (-chiralityOp n) *
          (mat2 (towerScalar n a) 0 0 (towerScalar n a) *
            (mat2 (1 - cantorProj n) 0 0 1 * Xm * mat2 (cantorProj n) 0 0 0))
      have h_prod :
          chiralityOp (A := A) (n + 1) * (towerScalar (n + 1) a * coherenceMode (n + 1) X) = M := by
        dsimp only [chiralityOp, towerScalar, coherenceMode, M]
        change mat2 (chiralityOp n) 0 0 (-chiralityOp n) *
          (mat2 (towerScalar n a) 0 0 (towerScalar n a) *
            ((1 - mat2 (cantorProj n) 0 0 0) * Xm * mat2 (cantorProj n) 0 0 0)) = _
        rw [h1P]
      rw [h_prod]
      have h00 : M 0 0 = chiralityOp n * (towerScalar n a * coherenceMode n (Xm 0 0)) := by
        dsimp only [M, coherenceMode]
        simp [mat2, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]
      have h11 : M 1 1 = 0 := by
        dsimp only [M]
        simp [mat2, Matrix.mul_apply, Fin.sum_univ_two]
      dsimp only [towerTrace]
      rw [h00, h11, towerTrace_zero n, add_zero]
      exact superTrace_towerScalar_coherenceMode a n (Xm 0 0)

/-- **Global Supertrace Annihilation on the Coherence Semigroup**:
`completionSuperTrace (cohSemigroupCompletion m₀ t z) = 0` for all `z : ClInfOpCompletion A`. -/
theorem completionSuperTrace_cohSemigroupCompletion [NormedAlgebra ℝ A] (m₀ : A) (t : ℝ)
    (z : ClInfOpCompletion A) :
    completionSuperTrace (cohSemigroupCompletion m₀ t z) = 0 := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map)
        continuous_const
  | ih x =>
      rcases exists_toClInf (toCl' x) with ⟨n, X, hx⟩
      have hx' : x = toClInfOp n X := hx
      rw [hx', cohSemigroupCompletion_coe, cohSemigroupOp_toClInfOp, completionSuperTrace_coe]
      change ((superTrace (towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) *
        coherenceMode n X) : A) : UniformSpace.Completion A) = 0
      rw [superTrace_towerScalar_coherenceMode, UniformSpace.Completion.coe_zero]

private theorem banachStar_noncomm_witness {A : Type u} [NormedRing A] [Nontrivial A] :
    ∃ x y : ClInfOpCompletion A, x * y ≠ y * x := by
  let e01 : ClTower A 1 := mat2 (0 : A) 1 0 0
  let e10 : ClTower A 1 := mat2 (0 : A) 0 1 0
  refine ⟨(toClInfOp 1 e01 : ClInfOp A), (toClInfOp 1 e10 : ClInfOp A), ?_⟩
  intro h
  rw [← clInfOpCompletion_coe_mul, ← clInfOpCompletion_coe_mul] at h
  have h_inj : (toClInfOp 1 e01 * toClInfOp 1 e10 : ClInfOp A) =
      toClInfOp 1 e10 * toClInfOp 1 e01 :=
    UniformSpace.Completion.coe_inj.mp h
  have h_zero : toClInfOp 1 (e01 * e10 - e10 * e01) = 0 := by
    rw [← sub_toClInfOp, ← mul_toClInfOp, ← mul_toClInfOp, h_inj, sub_self]
  have h_norm : opSumNorm 1 (e01 * e10 - e10 * e01) = 0 := by
    rw [← norm_toClInfOp, h_zero, norm_zero]
  have h1 : (0 : ℝ) < ‖(1 : A)‖ := norm_pos_iff.mpr one_ne_zero
  have h00 : (e01 * e10 - e10 * e01) 0 0 = (1 : A) := by
    simp [e01, e10, mat2, Matrix.mul_apply, Fin.sum_univ_two]
  have h00' : opSumNorm 0 ((e01 * e10 - e10 * e01) 0 0) = ‖(1 : A)‖ := by rw [h00]; rfl
  have h01 := opSumNorm_nonneg 0 ((e01 * e10 - e10 * e01) 0 1)
  have h10 := opSumNorm_nonneg 0 ((e01 * e10 - e10 * e01) 1 0)
  have h11 := opSumNorm_nonneg 0 ((e01 * e10 - e10 * e01) 1 1)
  have h_pos : 0 < opSumNorm 1 (e01 * e10 - e10 * e01) := by
    change 0 < opSumNorm 0 ((e01 * e10 - e10 * e01) 0 0) +
      opSumNorm 0 ((e01 * e10 - e10 * e01) 0 1) +
      opSumNorm 0 ((e01 * e10 - e10 * e01) 1 0) +
      opSumNorm 0 ((e01 * e10 - e10 * e01) 1 1)
    linarith
  linarith

private theorem matrix2_tower_noncomm_witness {A : Type u} [Ring A] [Nontrivial A] :
    ∃ x y : Matrix (Fin 2) (Fin 2) (ClTower A 0), x * y ≠ y * x := by
  refine ⟨mat2 0 1 0 0, mat2 0 0 1 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [mat2, Matrix.mul_apply, Fin.sum_univ_two] at h00

end GlobalOperatorSemigroup

end InfoGeometry.Algebra.NoncommutativeColimitBanachStarSemigroup
