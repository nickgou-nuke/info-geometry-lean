/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeColimitNormedLindbladBridge

/-!
# Iterated Lindblad Semigroup, Continuous $\star$/Supertrace Extension & Operator Mass-Gap Bound

This module extends `NoncommutativeColimitNormedLindbladBridge` in three directions:

1. **Iterated Euler Decay & Continuous-Time Exponential Semigroup in `ClInfCompletion A`**:
   Equips `ClInf A` with `NormedSpace ℝ (ClInf A)`, proves exact $k$-step iterated Euler
   damping `(eulerLindbladStep m₀ t n)^[k] (coherenceMode n X) = (1 - t * m₀^2)^k • coherenceMode n X`,
   preserves `cantorProj n` identically, and proves Trotter/Euler convergence
   `(1 - (t / k) * m₀^2)^k • Ψ_coh → Real.exp (-t * m₀^2) • Ψ_coh` in `ClInfCompletion A`.
2. **Continuous Extension of `star` & Stage-Wise Lipschitz Bound for `clInfSuperTrace`**:
   Lifts the isometric involution `star` on `ClInf A` to an involutive isometry `completionStar`
   on `ClInfCompletion A` via `UniformSpace.Completion.map`, and proves that `clInfSuperTrace`
   is $(2^n)$-Lipschitz on each finite-scale image `toClInf n`.
3. **Non-Scalar Operator Mass-Gap Bound**:
   Proves `towerNorm n (towerScalar n a * X) ≤ ‖a‖ * towerNorm n X` for arbitrary
   noncommutative `a : A` over `[NormedRing A]`, yielding operator-norm bounds on
   `lindbladDissipator (massGapOp m₀ n)` without scalarizing `m₀`.
-/

namespace InfoGeometry.Algebra.NoncommutativeColimitSemigroupAndOperatorGap

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis
open InfoGeometry.Algebra.NoncommutativeColimitNormedLindbladBridge

universe u

/-!
## Part 1: `NormedSpace ℝ (ClInf A)`, Iterated Euler Flow & Continuous-Time Semigroup Limit
-/

section IteratedEulerSemigroup

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A]

lemma bottEmbed_smul (r : ℝ) (n : ℕ) (X : ClTower A n) :
    bottEmbed (r • X) = r • bottEmbed X := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbedIter_smul (r : ℝ) {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (r • X) = r • bottEmbedIter k X := by
  induction k with
  | zero => rfl
  | succ k ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_smul]

private lemma heq_smul_tower (r : ℝ) {m n : ℕ} (h : m = n) {X : ClTower A m} {Y : ClTower A n}
    (heq : HEq X Y) : HEq (r • X) (r • Y) := by
  subst h; cases eq_of_heq heq; rfl

private noncomputable def smulClInf (r : ℝ) (x : ClInf A) : ClInf A :=
  Quotient.liftOn x
    (fun u => toClInf u.1 (r • u.2))
    (fun _ _ ⟨k₁, k₂, h_dim, heq_u⟩ => by
      apply Quotient.sound
      refine ⟨k₁, k₂, h_dim, ?_⟩
      rw [bottEmbedIter_smul, bottEmbedIter_smul]
      exact heq_smul_tower r h_dim heq_u)

noncomputable instance instSMulRealClInf : SMul ℝ (ClInf A) where
  smul := smulClInf

@[simp] lemma smul_toClInf (r : ℝ) (n : ℕ) (X : ClTower A n) :
    r • toClInf n X = toClInf n (r • X) := rfl

noncomputable instance instMulActionRealClInf : MulAction ℝ (ClInf A) where
  one_smul x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    simp [one_smul]
  mul_smul r s x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    simp [mul_smul]

noncomputable instance instDistribMulActionRealClInf : DistribMulAction ℝ (ClInf A) where
  smul_zero r := by
    rw [← toClInf_zero 0, smul_toClInf, smul_zero, toClInf_zero]
  smul_add r x y := by
    rcases toClInf_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
    simp [smul_add]

noncomputable instance instModuleRealClInf : Module ℝ (ClInf A) where
  add_smul r s x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    simp [add_smul]
  zero_smul x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    simp [zero_smul, toClInf_zero]

noncomputable instance instNormedSpaceRealClInf : NormedSpace ℝ (ClInf A) where
  norm_smul_le r x := by
    rcases exists_toClInf x with ⟨n, X, rfl⟩
    rw [smul_toClInf, norm_toClInf, norm_toClInf, towerNorm_smul, Real.norm_eq_abs]

/-- Single Euler step of the Metriplectic Lindblad mass-gap flow at scale `n`. -/
noncomputable def eulerLindbladStep (m₀ t : ℝ) (n : ℕ) (X : ClTower A n) : ClTower A n :=
  X + t • lindbladDissipator (massGapOp (algebraMap ℝ A m₀) n) X

lemma tower_smul_mul (r : ℝ) :
    ∀ (n : ℕ) (X Y : ClTower A n), (r • X) * Y = r • (X * Y)
  | 0,     a, b => smul_mul_assoc r a b
  | n + 1, M, N => by
      apply ext_fin2 <;>
      · simp [tower_smul_mul r n, smul_add]

lemma tower_mul_smul (r : ℝ) :
    ∀ (n : ℕ) (X Y : ClTower A n), X * (r • Y) = r • (X * Y)
  | 0,     a, b => mul_smul_comm r a b
  | n + 1, M, N => by
      apply ext_fin2 <;>
      · simp [tower_mul_smul r n, smul_add]

lemma lindbladDissipator_smul (H : ClTower A n) (r : ℝ) (ρ : ClTower A n) :
    lindbladDissipator H (r • ρ) = r • lindbladDissipator H ρ := by
  dsimp [lindbladDissipator]
  simp only [Ring.lie_def, tower_mul_smul, tower_smul_mul, ← smul_sub, smul_neg]

lemma eulerLindbladStep_vac (m₀ t : ℝ) (n : ℕ) :
    eulerLindbladStep (A := A) m₀ t n (cantorProj n) = cantorProj n := by
  dsimp [eulerLindbladStep]
  have h := (lindblad_mass_gap_damping_and_colimit_stability (algebraMap ℝ A m₀) n 0 0 (cantorProj n)).2.1
  rw [h, smul_zero, add_zero]

lemma eulerLindbladStep_iterate_vac (m₀ t : ℝ) (n k : ℕ) :
    (eulerLindbladStep (A := A) m₀ t n)^[k] (cantorProj n) = cantorProj n := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, eulerLindbladStep_vac]

lemma eulerLindbladStep_smul_coh (m₀ t c : ℝ) (n : ℕ) (X : ClTower A n) :
    eulerLindbladStep (A := A) m₀ t n (c • coherenceMode n X) =
      ((1 - t * (m₀ * m₀)) * c) • coherenceMode n X := by
  dsimp [eulerLindbladStep]
  rw [lindbladDissipator_smul]
  have h := (lindblad_mass_gap_damping_and_colimit_stability (algebraMap ℝ A m₀) n 0 0 X).2.2.1
  rw [h]
  have hm2 : towerScalar n (algebraMap ℝ A m₀ * algebraMap ℝ A m₀) * coherenceMode n X =
      (m₀ * m₀) • coherenceMode n X := by
    rw [← map_mul, towerScalar_algebraMap_mul]
  rw [hm2, smul_neg, smul_neg, ← sub_eq_add_neg, smul_smul, smul_smul, ← sub_smul]
  congr 1
  ring

lemma eulerLindbladStep_iterate_coh (m₀ t : ℝ) (n k : ℕ) (X : ClTower A n) :
    (eulerLindbladStep (A := A) m₀ t n)^[k] (coherenceMode n X) =
      (1 - t * (m₀ * m₀)) ^ k • coherenceMode n X := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, eulerLindbladStep_smul_coh, pow_succ']

/-- **Iterated Euler Contraction & Continuous-Time Semigroup Limit Theorem**:
For any scalar mass `m₀ : ℝ` and horizon `t : ℝ`:
1. *Decoherence-Free Vacuum*: `(eulerLindbladStep m₀ t n)^[k] (cantorProj n) = cantorProj n` for all `k`.
2. *Exact $k$-Step Norm Decay*: When `0 ≤ t` and `t * (m₀ * m₀) ≤ 1`,
   `‖((toClInf n ((eulerLindbladStep m₀ t n)^[k] (coherenceMode n X)) : ClInf A) : ClInfCompletion A)‖ = (1 - t * (m₀ * m₀)) ^ k * ‖...‖`.
3. *Trotter/Euler Semigroup Convergence*: In `ClInfCompletion A`,
   `(eulerLindbladStep m₀ (t / k) n)^[k] (coherenceMode n X)` converges as `k → ∞` to
   `Real.exp (-t * (m₀ * m₀)) • ((toClInf n (coherenceMode n X) : ClInf A) : ClInfCompletion A)`. -/
theorem lindblad_iterated_euler_contraction_and_semigroup_limit
    (m₀ t : ℝ) (n : ℕ) (X : ClTower A n) :
    let Ψ_coh := coherenceMode n X
    (∀ k : ℕ, (eulerLindbladStep (A := A) m₀ t n)^[k] (cantorProj n) = cantorProj n) ∧
    (0 ≤ t → t * (m₀ * m₀) ≤ 1 → ∀ k : ℕ,
      ‖((toClInf n ((eulerLindbladStep (A := A) m₀ t n)^[k] Ψ_coh) : ClInf A) :
          ClInfCompletion A)‖ =
        (1 - t * (m₀ * m₀)) ^ k *
          ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖) ∧
    Filter.Tendsto
      (fun k : ℕ =>
        ((toClInf n ((eulerLindbladStep (A := A) m₀ (t / (k : ℝ)) n)^[k] Ψ_coh) : ClInf A) :
          ClInfCompletion A))
      Filter.atTop
      (nhds (Real.exp (-t * (m₀ * m₀)) •
        ((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A))) := by
  intro Ψ_coh
  refine ⟨fun k => eulerLindbladStep_iterate_vac m₀ t n k, ?_, ?_⟩
  · intro _ht h_cfl k
    rw [eulerLindbladStep_iterate_coh]
    simp only [UniformSpace.Completion.norm_coe, norm_toClInf, towerNorm_smul]
    rw [abs_of_nonneg (pow_nonneg (sub_nonneg.mpr h_cfl) k)]
  · have h_scalar :
        Filter.Tendsto (fun k : ℕ => (1 - t / (k : ℝ) * (m₀ * m₀)) ^ k)
          Filter.atTop (nhds (Real.exp (-t * (m₀ * m₀)))) := by
      have h_exp := Real.tendsto_one_add_div_pow_exp (-t * (m₀ * m₀))
      refine h_exp.congr (fun k => ?_)
      congr 1
      ring
    have h_smul := h_scalar.smul_const ((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)
    refine h_smul.congr (fun k => ?_)
    rw [eulerLindbladStep_iterate_coh, ← smul_toClInf, UniformSpace.Completion.coe_smul]

end IteratedEulerSemigroup

/-!
## Part 2: Continuous Extension of `star` & Stage-Wise Lipschitz Bound for `clInfSuperTrace`
-/

section ContinuousExtensions

section StarCompletion

variable {A : Type u} [NormedRing A] [StarRing A] [NormedStarGroup A]

theorem clInf_star_isometry_dist : Isometry (star : ClInf A → ClInf A) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← star_sub, clInf_star_isometry]

/-- Continuous involutive extension of `star` to the Cauchy completion `ClInfCompletion A`. -/
noncomputable def completionStar : ClInfCompletion A → ClInfCompletion A :=
  UniformSpace.Completion.map (star : ClInf A → ClInf A)

@[simp] lemma completionStar_coe (x : ClInf A) :
    completionStar (x : ClInfCompletion A) = ((star x : ClInf A) : ClInfCompletion A) :=
  UniformSpace.Completion.map_coe clInf_star_isometry_dist.uniformContinuous x

theorem completionStar_involutive (z : ClInfCompletion A) :
    completionStar (completionStar z) = z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((UniformSpace.Completion.continuous_map).comp UniformSpace.Completion.continuous_map)
        continuous_id
  | ih x => simp [star_star]

theorem completionStar_isometry : Isometry (completionStar (A := A)) := by
  exact clInf_star_isometry_dist.completion_map

end StarCompletion

section SuperTraceLipschitz

variable {A : Type u} [NormedRing A]

lemma towerTrace_norm_le :
    ∀ (n : ℕ) (X : ClTower A n), ‖towerTrace X‖ ≤ (2 : ℝ) ^ n * towerNorm n X
  | 0,     a => by simp [towerTrace, towerNorm]
  | n + 1, M => by
      dsimp [towerTrace, towerNorm]
      calc ‖towerTrace (M 0 0) + towerTrace (M 1 1)‖
        _ ≤ ‖towerTrace (M 0 0)‖ + ‖towerTrace (M 1 1)‖ := norm_add_le _ _
        _ ≤ (2 : ℝ) ^ n * towerNorm n (M 0 0) + (2 : ℝ) ^ n * towerNorm n (M 1 1) :=
            add_le_add (towerTrace_norm_le n (M 0 0)) (towerTrace_norm_le n (M 1 1))
        _ ≤ (2 : ℝ) ^ n * max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                              (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1))) +
            (2 : ℝ) ^ n * max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                              (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1))) := by
            refine add_le_add ?_ ?_ <;>
              exact mul_le_mul_of_nonneg_left
                (by first
                  | exact le_trans (le_max_left _ _) (le_max_left _ _)
                  | exact le_trans (le_max_right _ _) (le_max_right _ _))
                (by positivity)
        _ = (2 : ℝ) ^ (n + 1) * max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                                    (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1))) := by
            ring

lemma towerNorm_chiralityOp_mul :
    ∀ (n : ℕ) (X : ClTower A n), towerNorm n (chiralityOp n * X) = towerNorm n X
  | 0,     a => by simp [chiralityOp, towerNorm]
  | n + 1, M => by
      dsimp [chiralityOp, towerNorm]
      have h00 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 0 =
          chiralityOp n * M 0 0 := by simp [mat2]
      have h01 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 1 =
          chiralityOp n * M 0 1 := by simp [mat2]
      have h10 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 0 =
          -(chiralityOp n * M 1 0) := by simp [mat2]
      have h11 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 1 =
          -(chiralityOp n * M 1 1) := by simp [mat2]
      change max (max (towerNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 0))
                      (towerNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 1)))
                 (max (towerNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 0))
                      (towerNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 1))) =
             max (max (towerNorm n (M 0 0)) (towerNorm n (M 0 1)))
                 (max (towerNorm n (M 1 0)) (towerNorm n (M 1 1)))
      rw [h00, h01, h10, h11, towerNorm_neg, towerNorm_neg,
          towerNorm_chiralityOp_mul n (M 0 0), towerNorm_chiralityOp_mul n (M 0 1),
          towerNorm_chiralityOp_mul n (M 1 0), towerNorm_chiralityOp_mul n (M 1 1)]

lemma towerTrace_sub (n : ℕ) (X Y : ClTower A n) :
    towerTrace (X - Y) = towerTrace X - towerTrace Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [towerTrace]
      change towerTrace (X 0 0 - Y 0 0) + towerTrace (X 1 1 - Y 1 1) =
             (towerTrace (X 0 0) + towerTrace (X 1 1)) -
             (towerTrace (Y 0 0) + towerTrace (Y 1 1))
      rw [ih (X 0 0) (Y 0 0), ih (X 1 1) (Y 1 1)]
      abel

/-- **Stage-Wise Supertrace Lipschitz Theorem**:
At every tower scale `n`, `clInfSuperTrace ∘ toClInf n` is `(2 ^ n)`-Lipschitz with respect to
the inductive-limit metric on `ClInf A`. -/
theorem clInfSuperTrace_lipschitz_at_scale (n : ℕ) (X Y : ClTower A n) :
    dist (clInfSuperTrace (toClInf n X)) (clInfSuperTrace (toClInf n Y)) ≤
      (2 : ℝ) ^ n * dist (toClInf n X) (toClInf n Y) := by
  rw [dist_eq_norm, dist_eq_norm]
  dsimp only [clInfSuperTrace, toClInf]
  rw [Quotient.lift_mk, Quotient.lift_mk]
  dsimp only [superTrace]
  rw [← towerTrace_sub, ← mul_sub]
  have h_sub : toClInf n X - toClInf n Y = toClInf n (X - Y) := by
    rw [sub_eq_add_neg, neg_toClInf, add_toClInf, sub_eq_add_neg]
  change ‖towerTrace (chiralityOp n * (X - Y))‖ ≤ (2 : ℝ) ^ n * ‖toClInf n X - toClInf n Y‖
  rw [h_sub, norm_toClInf]
  calc ‖towerTrace (chiralityOp n * (X - Y))‖
    _ ≤ (2 : ℝ) ^ n * towerNorm n (chiralityOp n * (X - Y)) := towerTrace_norm_le n _
    _ = (2 : ℝ) ^ n * towerNorm n (X - Y) := by rw [towerNorm_chiralityOp_mul]

end SuperTraceLipschitz

end ContinuousExtensions

/-!
## Part 3: Non-Scalar Operator Mass-Gap Bound
-/

section NonScalarOperatorMassGap

variable {A : Type u} [NormedRing A]

lemma towerNorm_towerScalar_mul_le (n : ℕ) (a : A) (X : ClTower A n) :
    towerNorm n (towerScalar n a * X) ≤ ‖a‖ * towerNorm n X := by
  induction n with
  | zero => exact norm_mul_le a X
  | succ n ih =>
      dsimp [towerNorm, towerScalar]
      have h00 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 0 =
          towerScalar n a * X 0 0 := by simp [mat2]
      have h01 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 1 =
          towerScalar n a * X 0 1 := by simp [mat2]
      have h10 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 0 =
          towerScalar n a * X 1 0 := by simp [mat2]
      have h11 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 1 =
          towerScalar n a * X 1 1 := by simp [mat2]
      change max (max (towerNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 0))
                      (towerNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 1)))
                 (max (towerNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 0))
                      (towerNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 1))) ≤
             ‖a‖ * max (max (towerNorm n (X 0 0)) (towerNorm n (X 0 1)))
                       (max (towerNorm n (X 1 0)) (towerNorm n (X 1 1)))
      rw [h00, h01, h10, h11]
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
      · exact le_trans (ih (X 0 0))
          (mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_left _ _)) (norm_nonneg a))
      · exact le_trans (ih (X 0 1))
          (mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_left _ _)) (norm_nonneg a))
      · exact le_trans (ih (X 1 0))
          (mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_right _ _)) (norm_nonneg a))
      · exact le_trans (ih (X 1 1))
          (mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_right _ _)) (norm_nonneg a))

/-- **Non-Scalar Operator Mass-Gap Lindblad Bound**:
For any genuinely noncommutative mass operator `m₀ : A` and step `t : ℝ`, on any transition
coherence `Ψ_coh := coherenceMode n X`:
1. The Lindblad dissipation increment is bounded by `|t| * ‖m₀‖ ^ 2 * ‖Ψ_coh‖`.
2. The Euler step `Ψ_coh + t • lindbladDissipator (massGapOp m₀ n) Ψ_coh` is bounded in
   `ClInfCompletion A` by `(1 + |t| * ‖m₀‖ ^ 2) * ‖Ψ_coh‖`. -/
theorem operator_massGap_lindblad_bound [NormedAlgebra ℝ A]
    (m₀ : A) (t : ℝ) (n : ℕ) (X : ClTower A n) :
    let Δ_n   := massGapOp m₀ n
    let Ψ_coh := coherenceMode n X
    ‖((toClInf n (t • lindbladDissipator Δ_n Ψ_coh) : ClInf A) : ClInfCompletion A)‖ ≤
      |t| * ‖m₀‖ ^ 2 * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ ∧
    ‖((toClInf n (Ψ_coh + t • lindbladDissipator Δ_n Ψ_coh) : ClInf A) : ClInfCompletion A)‖ ≤
      (1 + |t| * ‖m₀‖ ^ 2) * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ := by
  intro Δ_n Ψ_coh
  have h_damp := (lindblad_mass_gap_damping_and_colimit_stability m₀ n 0 0 X).2.2.1
  have h_inc :
      ‖((toClInf n (t • lindbladDissipator Δ_n Ψ_coh) : ClInf A) : ClInfCompletion A)‖ ≤
        |t| * ‖m₀‖ ^ 2 * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ := by
    simp only [UniformSpace.Completion.norm_coe, norm_toClInf]
    rw [h_damp, towerNorm_smul, towerNorm_neg]
    calc |t| * towerNorm n (towerScalar n (m₀ * m₀) * Ψ_coh)
      _ ≤ |t| * (‖m₀ * m₀‖ * towerNorm n Ψ_coh) :=
          mul_le_mul_of_nonneg_left (towerNorm_towerScalar_mul_le n (m₀ * m₀) Ψ_coh) (abs_nonneg t)
      _ ≤ |t| * ((‖m₀‖ * ‖m₀‖) * towerNorm n Ψ_coh) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (norm_mul_le m₀ m₀) (towerNorm_nonneg n Ψ_coh))
            (abs_nonneg t)
      _ = |t| * ‖m₀‖ ^ 2 * towerNorm n Ψ_coh := by ring
  refine ⟨h_inc, ?_⟩
  calc ‖((toClInf n (Ψ_coh + t • lindbladDissipator Δ_n Ψ_coh) : ClInf A) : ClInfCompletion A)‖
    _ = ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A) +
          ((toClInf n (t • lindbladDissipator Δ_n Ψ_coh) : ClInf A) : ClInfCompletion A)‖ := by
        rw [← UniformSpace.Completion.coe_add, add_toClInf]
    _ ≤ ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ +
          ‖((toClInf n (t • lindbladDissipator Δ_n Ψ_coh) : ClInf A) : ClInfCompletion A)‖ :=
        norm_add_le _ _
    _ ≤ ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ +
          |t| * ‖m₀‖ ^ 2 * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ :=
        add_le_add le_rfl h_inc
    _ = (1 + |t| * ‖m₀‖ ^ 2) * ‖((toClInf n Ψ_coh : ClInf A) : ClInfCompletion A)‖ := by ring

end NonScalarOperatorMassGap

/-- Non-commutativity witness for `ClInfCompletion A`. -/
private theorem clInf_completion_noncomm_witness {A : Type u} [NormedRing A] [Nontrivial A] :
    ∃ x y : ClInf A, x * y ≠ y * x := by
  refine ⟨toClInf 1 (mat2 (0 : A) 1 0 0), toClInf 1 (mat2 (0 : A) 0 1 0), ?_⟩
  intro h
  have h_left := congrArg (fun z => toClInf 1 (mat2 (1 : A) 0 0 0) * z) h
  simp only [mul_toClInf] at h_left
  have h_lhs : mat2 (1 : A) 0 0 0 * (mat2 0 1 0 0 * mat2 0 0 1 0) = mat2 1 0 0 0 := by
    apply ext_fin2 <;> simp [mat2]
  have h_rhs : mat2 (1 : A) 0 0 0 * (mat2 0 0 1 0 * mat2 0 1 0 0) = 0 := by
    apply ext_fin2 <;> simp [mat2]
  rw [h_lhs, h_rhs] at h_left
  have h_str := congrArg clInfSuperTrace h_left
  have h1_eq : mat2 (1 : A) 0 0 0 = cantorProj 1 := rfl
  rw [h1_eq] at h_str
  have h1 : clInfSuperTrace (toClInf 1 (cantorProj (A := A) 1)) = 1 :=
    (clInf_vacuum_stabilization_and_supertrace 1 (cantorProj 1)).2.2
  have h0 : clInfSuperTrace (toClInf 1 (0 : ClTower A 1)) = 0 := by
    rw [toClInf_zero]
    change clInfSuperTrace (toClInf 0 (0 : A)) = 0
    dsimp [clInfSuperTrace, toClInf, superTrace, chiralityOp, towerTrace]
    exact mul_zero 1
  rw [h1, h0] at h_str
  exact one_ne_zero h_str

end InfoGeometry.Algebra.NoncommutativeColimitSemigroupAndOperatorGap
