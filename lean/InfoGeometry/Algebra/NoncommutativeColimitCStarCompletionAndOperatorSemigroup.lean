/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeColimitSemigroupAndOperatorGap

/-!
# $\widehat{\mathcal{C}\ell}_\infty(A)$ as a Complete Non-Unital Normed $\star$-Algebra & Non-Scalar Operator Semigroup

This module closes the remaining two structural milestones for the inductive Bott–Clifford
operator algebra over an arbitrary noncommutative normed ring `A`:

1. **Continuous Multiplication & Globally 1-Lipschitz Supertrace on $\widehat{\mathcal{C}\ell}_\infty(A)$**:
   Equips `ClInfOp A` (a type synonym of `ClInf A`) with the inductive-limit $\ell_1$-block norm
   `opSumNorm`, proving `opSumNorm n (X * Y) ≤ opSumNorm n X * opSumNorm n Y` and making
   `ClInfOp A` a genuine `NonUnitalNormedRing`. Its completion
   `ClInfOpCompletion A := UniformSpace.Completion (ClInfOp A)` is a complete `NonUnitalNormedRing`
   with continuous bilinear multiplication, an involutive isometry `completionOpStar`, and a
   **globally 1-Lipschitz** supertrace `completionSuperTrace : ClInfOpCompletion A → Completion A`.
2. **Non-Scalar Operator Exponential Semigroup**:
   For genuinely noncommutative `m₀ : A` in a complete normed `ℝ`-algebra (`[NormedRing A]`,
   `[NormedAlgebra ℝ A]`, `[CompleteSpace A]`, `[NormOneClass A]`), proves the Banach-algebra
   Trotter/Euler limit `(1 + k⁻¹ • x)^k → NormedSpace.exp x`, the exact operator-valued
   Lindblad iteration `(opEulerLindbladStep m₀ t n)^[k] Ψ_coh = towerScalar n ((1 - t • m₀^2)^k) * Ψ_coh`,
   convergence in `ClInfOpCompletion A` to `towerScalar n (exp (-t • m₀^2)) * Ψ_coh`, and
   coercive exponential decay `≤ Real.exp (-t * μ^2) * ‖Ψ_coh‖`.
-/

namespace InfoGeometry.Algebra.NoncommutativeColimitCStarCompletionAndOperatorSemigroup

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis
open InfoGeometry.Algebra.NoncommutativeColimitNormedLindbladBridge
open InfoGeometry.Algebra.NoncommutativeColimitSemigroupAndOperatorGap

universe u

/-!
## Part 1: Submultiplicative $\ell_1$-Block Norm, `NonUnitalNormedRing`, and `ClInfOpCompletion A`
-/

section SubmultiplicativeOpNorm

variable {A : Type u} [NormedRing A]

/-- Submultiplicative $\ell_1$-block norm on `ClTower A n`, invariant under `bottEmbed`. -/
def opSumNorm : ∀ (n : ℕ), ClTower A n → ℝ
  | 0,     a => ‖a‖
  | n + 1, M =>
      opSumNorm n (M 0 0) + opSumNorm n (M 0 1) +
      opSumNorm n (M 1 0) + opSumNorm n (M 1 1)

lemma opSumNorm_nonneg : ∀ (n : ℕ) (X : ClTower A n), 0 ≤ opSumNorm n X
  | 0,     a => norm_nonneg a
  | n + 1, M => by
      dsimp [opSumNorm]
      linarith [opSumNorm_nonneg n (M 0 0), opSumNorm_nonneg n (M 0 1),
                opSumNorm_nonneg n (M 1 0), opSumNorm_nonneg n (M 1 1)]

lemma opSumNorm_zero : ∀ (n : ℕ), opSumNorm n (0 : ClTower A n) = 0
  | 0     => norm_zero
  | n + 1 => by
      dsimp [opSumNorm]
      change opSumNorm n (0 : ClTower A n) + opSumNorm n 0 +
             opSumNorm n 0 + opSumNorm n 0 = 0
      rw [opSumNorm_zero n]
      ring

lemma eq_zero_of_opSumNorm_eq_zero :
    ∀ {n : ℕ} {X : ClTower A n}, opSumNorm n X = 0 → X = 0
  | 0,     a, h => norm_eq_zero.mp h
  | n + 1, M, h => by
      dsimp [opSumNorm] at h
      have h00 := opSumNorm_nonneg n (M 0 0)
      have h01 := opSumNorm_nonneg n (M 0 1)
      have h10 := opSumNorm_nonneg n (M 1 0)
      have h11 := opSumNorm_nonneg n (M 1 1)
      have e00 : opSumNorm n (M 0 0) = 0 := by linarith
      have e01 : opSumNorm n (M 0 1) = 0 := by linarith
      have e10 : opSumNorm n (M 1 0) = 0 := by linarith
      have e11 : opSumNorm n (M 1 1) = 0 := by linarith
      apply ext_fin2
      · exact eq_zero_of_opSumNorm_eq_zero e00
      · exact eq_zero_of_opSumNorm_eq_zero e01
      · exact eq_zero_of_opSumNorm_eq_zero e10
      · exact eq_zero_of_opSumNorm_eq_zero e11

lemma opSumNorm_neg : ∀ (n : ℕ) (X : ClTower A n), opSumNorm n (-X) = opSumNorm n X
  | 0,     a => norm_neg a
  | n + 1, M => by
      dsimp [opSumNorm]
      change opSumNorm n (-M 0 0) + opSumNorm n (-M 0 1) +
             opSumNorm n (-M 1 0) + opSumNorm n (-M 1 1) =
             opSumNorm n (M 0 0) + opSumNorm n (M 0 1) +
             opSumNorm n (M 1 0) + opSumNorm n (M 1 1)
      rw [opSumNorm_neg n (M 0 0), opSumNorm_neg n (M 0 1),
          opSumNorm_neg n (M 1 0), opSumNorm_neg n (M 1 1)]

lemma opSumNorm_add_le :
    ∀ (n : ℕ) (X Y : ClTower A n), opSumNorm n (X + Y) ≤ opSumNorm n X + opSumNorm n Y
  | 0,     a, b => norm_add_le a b
  | n + 1, M, N => by
      dsimp [opSumNorm]
      change opSumNorm n (M 0 0 + N 0 0) + opSumNorm n (M 0 1 + N 0 1) +
             opSumNorm n (M 1 0 + N 1 0) + opSumNorm n (M 1 1 + N 1 1) ≤
             (opSumNorm n (M 0 0) + opSumNorm n (M 0 1) +
              opSumNorm n (M 1 0) + opSumNorm n (M 1 1)) +
             (opSumNorm n (N 0 0) + opSumNorm n (N 0 1) +
              opSumNorm n (N 1 0) + opSumNorm n (N 1 1))
      linarith [opSumNorm_add_le n (M 0 0) (N 0 0),
                opSumNorm_add_le n (M 0 1) (N 0 1),
                opSumNorm_add_le n (M 1 0) (N 1 0),
                opSumNorm_add_le n (M 1 1) (N 1 1)]

lemma opSumNorm_mul_le :
    ∀ (n : ℕ) (X Y : ClTower A n), opSumNorm n (X * Y) ≤ opSumNorm n X * opSumNorm n Y
  | 0,     a, b => norm_mul_le a b
  | n + 1, M, N => by
      dsimp [opSumNorm]
      have h00 : (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
      have h01 : (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
      have h10 : (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
      have h11 : (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
      have b00 := le_trans (opSumNorm_add_le n _ _)
        (add_le_add (opSumNorm_mul_le n (M 0 0) (N 0 0)) (opSumNorm_mul_le n (M 0 1) (N 1 0)))
      have b01 := le_trans (opSumNorm_add_le n _ _)
        (add_le_add (opSumNorm_mul_le n (M 0 0) (N 0 1)) (opSumNorm_mul_le n (M 0 1) (N 1 1)))
      have b10 := le_trans (opSumNorm_add_le n _ _)
        (add_le_add (opSumNorm_mul_le n (M 1 0) (N 0 0)) (opSumNorm_mul_le n (M 1 1) (N 1 0)))
      have b11 := le_trans (opSumNorm_add_le n _ _)
        (add_le_add (opSumNorm_mul_le n (M 1 0) (N 0 1)) (opSumNorm_mul_le n (M 1 1) (N 1 1)))
      rw [← h00] at b00; rw [← h01] at b01; rw [← h10] at b10; rw [← h11] at b11
      have n00 := opSumNorm_nonneg n (M 0 0)
      have n01 := opSumNorm_nonneg n (M 0 1)
      have n10 := opSumNorm_nonneg n (M 1 0)
      have n11 := opSumNorm_nonneg n (M 1 1)
      have m00 := opSumNorm_nonneg n (N 0 0)
      have m01 := opSumNorm_nonneg n (N 0 1)
      have m10 := opSumNorm_nonneg n (N 1 0)
      have m11 := opSumNorm_nonneg n (N 1 1)
      nlinarith

lemma opSumNorm_bottEmbed (n : ℕ) (X : ClTower A n) :
    opSumNorm (n + 1) (bottEmbed X) = opSumNorm n X := by
  dsimp [opSumNorm, bottEmbed, mat2]
  simp [opSumNorm_zero]

lemma opSumNorm_bottEmbedIter {n : ℕ} (k : ℕ) (X : ClTower A n) :
    opSumNorm (n + k) (bottEmbedIter k X) = opSumNorm n X := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp [bottEmbedIter]
      change opSumNorm ((n + k) + 1) (bottEmbed (bottEmbedIter k X)) = opSumNorm n X
      rw [opSumNorm_bottEmbed, ih]

private lemma opSumNorm_eq_of_heq {n m : ℕ} {X : ClTower A n} {Y : ClTower A m}
    (h_dim : n = m) (h_heq : X ≍ Y) :
    opSumNorm n X = opSumNorm m Y := by
  subst h_dim
  cases eq_of_heq h_heq
  rfl

private lemma clInfOpNorm_well_defined
    (u v : Σ n : ℕ, ClTower A n) (h_rel : ClInfRel u v) :
    opSumNorm u.1 u.2 = opSumNorm v.1 v.2 := by
  rcases h_rel with ⟨k₁, k₂, h_dim, h_heq⟩
  calc opSumNorm u.1 u.2
    _ = opSumNorm (u.1 + k₁) (bottEmbedIter k₁ u.2) := (opSumNorm_bottEmbedIter k₁ u.2).symm
    _ = opSumNorm (v.1 + k₂) (bottEmbedIter k₂ v.2) := opSumNorm_eq_of_heq h_dim h_heq
    _ = opSumNorm v.1 v.2                            := opSumNorm_bottEmbedIter k₂ v.2

/-- Quotient-lifted submultiplicative inductive-limit norm on `ClInf A`. -/
def clInfOpNorm : ClInf A → ℝ :=
  Quotient.lift (fun u => opSumNorm u.1 u.2) clInfOpNorm_well_defined

@[simp] lemma clInfOpNorm_toClInf (n : ℕ) (X : ClTower A n) :
    clInfOpNorm (toClInf n X) = opSumNorm n X := rfl

/-- Type synonym for `ClInf A` equipped with the submultiplicative `opSumNorm` (`NonUnitalNormedRing`). -/
def ClInfOp (A : Type u) [NormedRing A] : Type u := ClInf A

instance instNonUnitalRingClInfOp : NonUnitalRing (ClInfOp A) :=
  inferInstanceAs (NonUnitalRing (ClInf A))

instance instStarClInfOp [StarRing A] : Star (ClInfOp A) :=
  inferInstanceAs (Star (ClInf A))

instance instInvolutiveStarClInfOp [StarRing A] : InvolutiveStar (ClInfOp A) :=
  inferInstanceAs (InvolutiveStar (ClInf A))

instance instStarAddMonoidClInfOp [StarRing A] : StarAddMonoid (ClInfOp A) :=
  inferInstanceAs (StarAddMonoid (ClInf A))

instance instStarMulClInfOp [StarRing A] : StarMul (ClInfOp A) :=
  inferInstanceAs (StarMul (ClInf A))

/-- Coercion helper from `ClInfOp A` to `ClInf A` with explicit target type. -/
private def toCl (x : ClInfOp A) : ClInf A := x

noncomputable instance instNormedAddCommGroupClInfOp : NormedAddCommGroup (ClInfOp A) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => clInfOpNorm (toCl x)
      map_zero' := by
        change clInfOpNorm (0 : ClInf A) = 0
        rw [← toClInf_zero 0, clInfOpNorm_toClInf, opSumNorm_zero]
      add_le' := fun x y => by
        rcases toClInf_lift_two (toCl x) (toCl y) with ⟨n, X, Y, hx, hy⟩
        have hxy : toCl (x + y) = toClInf n (X + Y) := by
          change toCl x + toCl y = toClInf n (X + Y)
          rw [hx, hy, add_toClInf]
        rw [hxy, hx, hy, clInfOpNorm_toClInf, clInfOpNorm_toClInf, clInfOpNorm_toClInf]
        exact opSumNorm_add_le n X Y
      neg' := fun x => by
        rcases exists_toClInf (toCl x) with ⟨n, X, hx⟩
        have hnx : toCl (-x) = toClInf n (-X) := by
          change -(toCl x) = toClInf n (-X)
          rw [hx, neg_toClInf]
        rw [hnx, hx, clInfOpNorm_toClInf, clInfOpNorm_toClInf]
        exact opSumNorm_neg n X
      eq_zero_of_map_eq_zero' := fun x hx => by
        rcases exists_toClInf (toCl x) with ⟨n, X, h_eq⟩
        rw [h_eq, clInfOpNorm_toClInf] at hx
        change toCl x = 0
        rw [h_eq, eq_zero_of_opSumNorm_eq_zero hx, toClInf_zero] }

/-- **Genuine `NonUnitalNormedRing` structure on `ClInfOp A`** (submultiplicative across all scales). -/
noncomputable instance instNonUnitalNormedRingClInfOp : NonUnitalNormedRing (ClInfOp A) where
  __ : NormedAddCommGroup (ClInfOp A) := inferInstance
  __ : NonUnitalRing (ClInfOp A) := inferInstance
  norm_mul_le := fun x y => by
    rcases toClInf_lift_two (toCl x) (toCl y) with ⟨n, X, Y, hx, hy⟩
    have hxy : toCl (x * y) = toClInf n (X * Y) := by
      change toCl x * toCl y = toClInf n (X * Y)
      rw [hx, hy, mul_toClInf]
    change clInfOpNorm (toCl (x * y)) ≤ clInfOpNorm (toCl x) * clInfOpNorm (toCl y)
    rw [hxy, hx, hy, clInfOpNorm_toClInf, clInfOpNorm_toClInf, clInfOpNorm_toClInf]
    exact opSumNorm_mul_le n X Y

/-- Canonical injection into `ClInfOp A`. -/
def toClInfOp (n : ℕ) (X : ClTower A n) : ClInfOp A := toClInf n X

@[simp] lemma norm_toClInfOp (n : ℕ) (X : ClTower A n) :
    ‖toClInfOp n X‖ = opSumNorm n X := rfl

lemma add_toClInfOp (n : ℕ) (X Y : ClTower A n) :
    toClInfOp n X + toClInfOp n Y = toClInfOp n (X + Y) :=
  add_toClInf n X Y

lemma neg_toClInfOp (n : ℕ) (X : ClTower A n) :
    -toClInfOp n X = toClInfOp n (-X) :=
  neg_toClInf n X

lemma sub_toClInfOp (n : ℕ) (X Y : ClTower A n) :
    toClInfOp n X - toClInfOp n Y = toClInfOp n (X - Y) := by
  rw [sub_eq_add_neg, neg_toClInfOp, add_toClInfOp, sub_eq_add_neg]

lemma mul_toClInfOp (n : ℕ) (X Y : ClTower A n) :
    toClInfOp n X * toClInfOp n Y = toClInfOp n (X * Y) :=
  mul_toClInf n X Y

/-- Complete non-unital normed algebra $\widehat{\mathcal{C}\ell}_\infty(A) = \mathrm{Completion}(\mathcal{C}\ell_\infty^{\mathrm{op}}(A))$. -/
abbrev ClInfOpCompletion (A : Type u) [NormedRing A] := UniformSpace.Completion (ClInfOp A)

noncomputable instance instMulClInfOpCompletion : Mul (ClInfOpCompletion A) :=
  ⟨Function.curry <|
    (UniformSpace.Completion.isDenseInducing_coe.prodMap
      UniformSpace.Completion.isDenseInducing_coe).extend
      ((↑) ∘ Function.uncurry (· * ·))⟩

@[norm_cast]
lemma clInfOpCompletion_coe_mul (a b : ClInfOp A) :
    ((a * b : ClInfOp A) : ClInfOpCompletion A) = (a : ClInfOpCompletion A) * b :=
  ((UniformSpace.Completion.isDenseInducing_coe.prodMap
    UniformSpace.Completion.isDenseInducing_coe).extend_eq
    ((UniformSpace.Completion.continuous_coe (ClInfOp A)).comp continuous_mul) (a, b)).symm

instance instContinuousMulClInfOpCompletion : ContinuousMul (ClInfOpCompletion A) where
  continuous_mul := by
    let m := (AddMonoidHom.mul : ClInfOp A →+ ClInfOp A →+ ClInfOp A).compr₂
      UniformSpace.Completion.toCompl
    have hcont : Continuous fun p : ClInfOp A × ClInfOp A => m p.1 p.2 :=
      (UniformSpace.Completion.continuous_coe (ClInfOp A)).comp continuous_mul
    have di : IsDenseInducing (UniformSpace.Completion.toCompl : ClInfOp A → ClInfOpCompletion A) :=
      UniformSpace.Completion.isDenseInducing_coe
    exact (di.extend_Z_bilin di hcont :)

noncomputable instance instNonUnitalRingClInfOpCompletion :
    NonUnitalRing (ClInfOpCompletion A) where
  zero_mul a :=
    UniformSpace.Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
      fun a => by rw [← UniformSpace.Completion.coe_zero, ← clInfOpCompletion_coe_mul, zero_mul]
  mul_zero a :=
    UniformSpace.Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
      fun a => by rw [← UniformSpace.Completion.coe_zero, ← clInfOpCompletion_coe_mul, mul_zero]
  mul_assoc a b c :=
    UniformSpace.Completion.induction_on₃ a b c
      (isClosed_eq (by fun_prop) (by fun_prop))
      fun a b c => by
        rw [← clInfOpCompletion_coe_mul, ← clInfOpCompletion_coe_mul,
            ← clInfOpCompletion_coe_mul, ← clInfOpCompletion_coe_mul, mul_assoc]
  left_distrib a b c :=
    UniformSpace.Completion.induction_on₃ a b c
      (isClosed_eq (by fun_prop) (by fun_prop))
      fun a b c => by
        rw [← UniformSpace.Completion.coe_add, ← clInfOpCompletion_coe_mul,
            ← clInfOpCompletion_coe_mul, ← clInfOpCompletion_coe_mul,
            ← UniformSpace.Completion.coe_add, left_distrib]
  right_distrib a b c :=
    UniformSpace.Completion.induction_on₃ a b c
      (isClosed_eq (by fun_prop) (by fun_prop))
      fun a b c => by
        rw [← UniformSpace.Completion.coe_add, ← clInfOpCompletion_coe_mul,
            ← clInfOpCompletion_coe_mul, ← clInfOpCompletion_coe_mul,
            ← UniformSpace.Completion.coe_add, right_distrib]

noncomputable instance instNonUnitalNormedRingClInfOpCompletion :
    NonUnitalNormedRing (ClInfOpCompletion A) where
  __ : NormedAddCommGroup (ClInfOpCompletion A) := inferInstance
  __ : NonUnitalRing (ClInfOpCompletion A) := inferInstance
  norm_mul_le x y := by
    induction x, y using UniformSpace.Completion.induction_on₂ with
    | hp => apply isClosed_le <;> fun_prop
    | ih x y =>
        simpa only [← clInfOpCompletion_coe_mul, UniformSpace.Completion.norm_coe] using
          norm_mul_le x y

/-- **Continuous Multiplication & Isometric Completion Theorem**:
`ClInfOpCompletion A` is a complete `NonUnitalNormedRing`, `toClInfOp n` is an isometric
non-unital ring homomorphism into `ClInfOpCompletion A`, and multiplication on
`ClInfOpCompletion A` extends `mul` on `ClInfOp A` continuously. -/
theorem clInfOp_completion_nonunital_normed_ring (n : ℕ) (X Y : ClTower A n) :
    ‖((toClInfOp n X : ClInfOp A) : ClInfOpCompletion A)‖ = opSumNorm n X ∧
    ((toClInfOp n X : ClInfOp A) : ClInfOpCompletion A) *
      ((toClInfOp n Y : ClInfOp A) : ClInfOpCompletion A) =
      ((toClInfOp n (X * Y) : ClInfOp A) : ClInfOpCompletion A) ∧
    (∀ z w : ClInfOpCompletion A, ‖z * w‖ ≤ ‖z‖ * ‖w‖) := by
  refine ⟨by rw [UniformSpace.Completion.norm_coe, norm_toClInfOp], ?_, fun z w => norm_mul_le z w⟩
  rw [← clInfOpCompletion_coe_mul, mul_toClInfOp]

lemma opSumNorm_star [StarRing A] [NormedStarGroup A] :
    ∀ (n : ℕ) (X : ClTower A n), opSumNorm n (star X) = opSumNorm n X
  | 0,     a => norm_star a
  | n + 1, M => by
      let _ : StarRing (ClTower A n) := instStarRingClTower n
      dsimp [opSumNorm]
      change opSumNorm n (star (M 0 0)) + opSumNorm n (star (M 1 0)) +
             opSumNorm n (star (M 0 1)) + opSumNorm n (star (M 1 1)) =
             opSumNorm n (M 0 0) + opSumNorm n (M 0 1) +
             opSumNorm n (M 1 0) + opSumNorm n (M 1 1)
      rw [opSumNorm_star n (M 0 0), opSumNorm_star n (M 1 0),
          opSumNorm_star n (M 0 1), opSumNorm_star n (M 1 1)]
      ring

theorem clInfOp_star_isometry [StarRing A] [NormedStarGroup A] :
    Isometry (Star.star : ClInfOp A → ClInfOp A) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rcases toClInf_lift_two (toCl x) (toCl y) with ⟨n, X, Y, hx, hy⟩
  let _ : StarRing (ClTower A n) := instStarRingClTower n
  have hxy : toCl (x - y) = toClInf n (X - Y) := by
    change toCl x - toCl y = toClInf n (X - Y)
    rw [hx, hy, sub_eq_add_neg, neg_toClInf, add_toClInf, sub_eq_add_neg]
  have hsxy : toCl (star x - star y) = toClInf n (star (X - Y)) := by
    change star (toCl x) - star (toCl y) = toClInf n (star (X - Y))
    rw [hx, hy, star_toClInf, star_toClInf, sub_eq_add_neg, neg_toClInf, add_toClInf,
        ← sub_eq_add_neg, star_sub]
  rw [dist_eq_norm, dist_eq_norm]
  change clInfOpNorm (toCl (star x - star y)) = clInfOpNorm (toCl (x - y))
  rw [hsxy, hxy, clInfOpNorm_toClInf, clInfOpNorm_toClInf, opSumNorm_star]

/-- Continuous involutive $\star$-extension on `ClInfOpCompletion A`. -/
noncomputable def completionOpStar [StarRing A] [NormedStarGroup A] :
    ClInfOpCompletion A → ClInfOpCompletion A :=
  UniformSpace.Completion.map (Star.star : ClInfOp A → ClInfOp A)

theorem completionOpStar_isometry_and_involutive [StarRing A] [NormedStarGroup A] :
    Isometry (completionOpStar (A := A)) ∧
    (∀ z : ClInfOpCompletion A, completionOpStar (completionOpStar z) = z) := by
  refine ⟨?_, fun z => ?_⟩
  · refine Isometry.of_dist_eq (fun z w => ?_)
    induction z, w using UniformSpace.Completion.induction_on₂ with
    | hp =>
        exact isClosed_eq
          ((UniformSpace.Completion.continuous_map.comp continuous_fst).dist
           (UniformSpace.Completion.continuous_map.comp continuous_snd))
          continuous_dist
    | ih x y =>
        change dist (UniformSpace.Completion.map Star.star (x : ClInfOpCompletion A))
          (UniformSpace.Completion.map Star.star (y : ClInfOpCompletion A)) =
          dist (x : ClInfOpCompletion A) (y : ClInfOpCompletion A)
        rw [UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            dist_eq_norm, dist_eq_norm, ← UniformSpace.Completion.coe_sub,
            ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe,
            UniformSpace.Completion.norm_coe, ← dist_eq_norm, ← dist_eq_norm]
        exact clInfOp_star_isometry.dist_eq x y
  · induction z using UniformSpace.Completion.induction_on with
    | hp =>
        exact isClosed_eq
          (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map)
          continuous_id
    | ih x =>
        change UniformSpace.Completion.map Star.star
          (UniformSpace.Completion.map Star.star (x : ClInfOpCompletion A)) =
          (x : ClInfOpCompletion A)
        rw [UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            UniformSpace.Completion.map_coe clInfOp_star_isometry.uniformContinuous,
            star_star]

lemma towerTrace_norm_le_opSumNorm :
    ∀ (n : ℕ) (X : ClTower A n), ‖towerTrace X‖ ≤ opSumNorm n X
  | 0,     a => le_rfl
  | n + 1, M => by
      dsimp [towerTrace, opSumNorm]
      have h01 := opSumNorm_nonneg n (M 0 1)
      have h10 := opSumNorm_nonneg n (M 1 0)
      linarith [norm_add_le (towerTrace (M 0 0)) (towerTrace (M 1 1)),
                towerTrace_norm_le_opSumNorm n (M 0 0),
                towerTrace_norm_le_opSumNorm n (M 1 1)]

lemma opSumNorm_chiralityOp_mul :
    ∀ (n : ℕ) (X : ClTower A n), opSumNorm n (chiralityOp n * X) = opSumNorm n X
  | 0,     a => by simp [chiralityOp, opSumNorm]
  | n + 1, M => by
      dsimp [chiralityOp, opSumNorm]
      have h00 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 0 =
          chiralityOp n * M 0 0 := by simp [mat2]
      have h01 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 1 =
          chiralityOp n * M 0 1 := by simp [mat2]
      have h10 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 0 =
          -(chiralityOp n * M 1 0) := by simp [mat2]
      have h11 : (mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 1 =
          -(chiralityOp n * M 1 1) := by simp [mat2]
      change opSumNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 0) +
             opSumNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 0 1) +
             opSumNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 0) +
             opSumNorm n ((mat2 (chiralityOp (A := A) n) 0 0 (-chiralityOp n) * M) 1 1) =
             opSumNorm n (M 0 0) + opSumNorm n (M 0 1) +
             opSumNorm n (M 1 0) + opSumNorm n (M 1 1)
      rw [h00, h01, h10, h11, opSumNorm_neg, opSumNorm_neg,
          opSumNorm_chiralityOp_mul n (M 0 0), opSumNorm_chiralityOp_mul n (M 0 1),
          opSumNorm_chiralityOp_mul n (M 1 0), opSumNorm_chiralityOp_mul n (M 1 1)]

lemma clInfSuperTrace_sub (x y : ClInf A) :
    clInfSuperTrace (x - y) = clInfSuperTrace x - clInfSuperTrace y := by
  rcases toClInf_lift_two x y with ⟨n, X, Y, rfl, rfl⟩
  have h_sub : toClInf n X - toClInf n Y = toClInf n (X - Y) := by
    rw [sub_eq_add_neg, neg_toClInf, add_toClInf, sub_eq_add_neg]
  rw [h_sub]
  dsimp only [clInfSuperTrace, toClInf]
  rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
  dsimp only [superTrace]
  rw [mul_sub,
    InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis.towerTrace_sub]

/-- `clInfSuperTrace` is **globally 1-Lipschitz** on `ClInfOp A` (independent of scale `n`). -/
theorem clInfSuperTrace_global_lipschitz (x y : ClInfOp A) :
    dist (clInfSuperTrace (x : ClInf A)) (clInfSuperTrace (y : ClInf A)) ≤ dist x y := by
  have h_eq : clInfSuperTrace (x : ClInf A) - clInfSuperTrace (y : ClInf A) =
      clInfSuperTrace ((x : ClInf A) - (y : ClInf A)) :=
    (clInfSuperTrace_sub (x : ClInf A) (y : ClInf A)).symm
  rw [dist_eq_norm, dist_eq_norm, h_eq]
  rcases exists_toClInf ((x : ClInf A) - (y : ClInf A)) with ⟨n, Z, hz⟩
  change ‖clInfSuperTrace ((x : ClInf A) - (y : ClInf A))‖ ≤
    clInfOpNorm ((x - y : ClInfOp A) : ClInf A)
  have h_sub_coe : ((x - y : ClInfOp A) : ClInf A) = (x : ClInf A) - (y : ClInf A) := rfl
  rw [h_sub_coe, hz, clInfOpNorm_toClInf]
  dsimp only [clInfSuperTrace, toClInf]
  rw [Quotient.lift_mk]
  dsimp only [superTrace]
  calc ‖towerTrace (chiralityOp n * Z)‖
    _ ≤ opSumNorm n (chiralityOp n * Z) := towerTrace_norm_le_opSumNorm n _
    _ = opSumNorm n Z := opSumNorm_chiralityOp_mul n Z

/-- Globally continuous supertrace $\mathrm{Str}_\infty : \widehat{\mathcal{C}\ell}_\infty(A) \to \widehat{A}$. -/
noncomputable def completionSuperTrace :
    ClInfOpCompletion A → UniformSpace.Completion A :=
  UniformSpace.Completion.map (fun x : ClInfOp A => clInfSuperTrace (x : ClInf A))

theorem completionSuperTrace_coe (n : ℕ) (X : ClTower A n) :
    completionSuperTrace ((toClInfOp n X : ClInfOp A) : ClInfOpCompletion A) =
      ((clInfSuperTrace (toClInf n X) : A) : UniformSpace.Completion A) :=
  UniformSpace.Completion.map_coe
    (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by
      simpa only [NNReal.coe_one, one_mul] using clInfSuperTrace_global_lipschitz x y)).uniformContinuous
    (toClInfOp n X)

end SubmultiplicativeOpNorm

/-!
## Part 2: Non-Scalar Operator Exponential Semigroup in Banach Algebras
-/

section NonScalarOperatorSemigroup

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A]

lemma opSumNorm_smul (c : ℝ) :
    ∀ (n : ℕ) (X : ClTower A n), opSumNorm n (c • X) = |c| * opSumNorm n X
  | 0,     a => by
      dsimp [opSumNorm]
      rw [norm_smul, Real.norm_eq_abs]
  | n + 1, M => by
      dsimp [opSumNorm]
      change opSumNorm n (c • M 0 0) + opSumNorm n (c • M 0 1) +
             opSumNorm n (c • M 1 0) + opSumNorm n (c • M 1 1) =
             |c| * (opSumNorm n (M 0 0) + opSumNorm n (M 0 1) +
                    opSumNorm n (M 1 0) + opSumNorm n (M 1 1))
      rw [opSumNorm_smul c n (M 0 0), opSumNorm_smul c n (M 0 1),
          opSumNorm_smul c n (M 1 0), opSumNorm_smul c n (M 1 1)]
      ring

omit [NormedAlgebra ℝ A] in
lemma opSumNorm_towerScalar_mul_le (n : ℕ) (a : A) (X : ClTower A n) :
    opSumNorm n (towerScalar n a * X) ≤ ‖a‖ * opSumNorm n X := by
  induction n with
  | zero => exact norm_mul_le a X
  | succ n ih =>
      dsimp [opSumNorm, towerScalar]
      have h00 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 0 =
          towerScalar n a * X 0 0 := by simp [mat2]
      have h01 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 1 =
          towerScalar n a * X 0 1 := by simp [mat2]
      have h10 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 0 =
          towerScalar n a * X 1 0 := by simp [mat2]
      have h11 : (mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 1 =
          towerScalar n a * X 1 1 := by simp [mat2]
      change opSumNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 0) +
             opSumNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 0 1) +
             opSumNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 0) +
             opSumNorm n ((mat2 (towerScalar n a) 0 0 (towerScalar n a) * X) 1 1) ≤
             ‖a‖ * (opSumNorm n (X 0 0) + opSumNorm n (X 0 1) +
                    opSumNorm n (X 1 0) + opSumNorm n (X 1 1))
      rw [h00, h01, h10, h11]
      linarith [ih (X 0 0), ih (X 0 1), ih (X 1 0), ih (X 1 1)]

omit [NormedAlgebra ℝ A] in
lemma towerScalar_one (n : ℕ) : towerScalar n (1 : A) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [towerScalar]
      apply ext_fin2 <;> simp [mat2, ih]

omit [NormedAlgebra ℝ A] in
lemma towerScalar_sub (n : ℕ) (a b : A) :
    towerScalar n (a - b) = towerScalar n a - towerScalar n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [towerScalar]
      apply ext_fin2 <;> simp [mat2, ih]

lemma towerScalar_smul (n : ℕ) (r : ℝ) (a : A) :
    towerScalar n (r • a) = r • towerScalar n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp [towerScalar]
      apply ext_fin2 <;> simp [mat2, ih]

/-- Operator-valued Euler Lindblad step for noncommutative `m₀ : A`. -/
noncomputable def opEulerLindbladStep (m₀ : A) (t : ℝ) (n : ℕ) (X : ClTower A n) : ClTower A n :=
  X + t • lindbladDissipator (massGapOp m₀ n) X

omit [NormedAlgebra ℝ A] in
lemma lindbladDissipator_towerScalar_coh (m₀ a : A) (n : ℕ) (X : ClTower A n) :
    lindbladDissipator (massGapOp m₀ n) (towerScalar n a * coherenceMode n X) =
      -(towerScalar n (m₀ * m₀ * a) * coherenceMode n X) := by
  have hP := cantorProj_idem (A := A) n
  have h_orth : cantorProj n * (towerScalar n a * coherenceMode n X) = 0 := by
    dsimp [coherenceMode]
    calc cantorProj n * (towerScalar n a * ((1 - cantorProj n) * X * cantorProj n))
      _ = (cantorProj n * towerScalar n a) * (1 - cantorProj n) * X * cantorProj n := by
          noncomm_ring
      _ = (towerScalar n a * cantorProj n) * (1 - cantorProj n) * X * cantorProj n := by
          rw [← towerScalar_comm_cantorProj]
      _ = towerScalar n a * (cantorProj n - cantorProj n * cantorProj n) * X * cantorProj n := by
          noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero, zero_mul, zero_mul]
  have h_ann_L := (massGap_vacuum_annihilation_coercivity_and_colimit_stability m₀ n _ h_orth).2.1
  have h_coer := (massGap_vacuum_annihilation_coercivity_and_colimit_stability m₀ n _ h_orth).2.2.1
  have h_right : (towerScalar n a * coherenceMode n X) * massGapOp m₀ n = 0 := by
    dsimp [coherenceMode]
    calc towerScalar n a * ((1 - cantorProj n) * X * cantorProj n) * massGapOp m₀ n
      _ = towerScalar n a * (1 - cantorProj n) * X * (cantorProj n * massGapOp m₀ n) := by
          noncomm_ring
      _ = 0 := by rw [h_ann_L, mul_zero]
  have h_orth2 : cantorProj n * (towerScalar n (m₀ * a) * coherenceMode n X) = 0 := by
    dsimp [coherenceMode]
    calc cantorProj n * (towerScalar n (m₀ * a) * ((1 - cantorProj n) * X * cantorProj n))
      _ = (cantorProj n * towerScalar n (m₀ * a)) * (1 - cantorProj n) * X * cantorProj n := by
          noncomm_ring
      _ = (towerScalar n (m₀ * a) * cantorProj n) * (1 - cantorProj n) * X * cantorProj n := by
          rw [← towerScalar_comm_cantorProj]
      _ = towerScalar n (m₀ * a) * (cantorProj n - cantorProj n * cantorProj n) * X * cantorProj n := by
          noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero, zero_mul, zero_mul]
  have h_coer2 := (massGap_vacuum_annihilation_coercivity_and_colimit_stability m₀ n _ h_orth2).2.2.1
  have h_right2 : (towerScalar n (m₀ * a) * coherenceMode n X) * massGapOp m₀ n = 0 := by
    dsimp [coherenceMode]
    calc towerScalar n (m₀ * a) * ((1 - cantorProj n) * X * cantorProj n) * massGapOp m₀ n
      _ = towerScalar n (m₀ * a) * (1 - cantorProj n) * X * (cantorProj n * massGapOp m₀ n) := by
          noncomm_ring
      _ = 0 := by rw [h_ann_L, mul_zero]
  dsimp [lindbladDissipator]
  rw [Ring.lie_def (massGapOp m₀ n) (towerScalar n a * coherenceMode n X),
      h_coer, h_right, sub_zero, ← mul_assoc, ← towerScalar_mul]
  rw [Ring.lie_def, h_coer2, h_right2, sub_zero, ← mul_assoc, ← towerScalar_mul, mul_assoc]

lemma opEulerLindbladStep_iterate_coh (m₀ : A) (t : ℝ) (n k : ℕ) (X : ClTower A n) :
    (opEulerLindbladStep m₀ t n)^[k] (coherenceMode n X) =
      towerScalar n ((1 - t • (m₀ * m₀)) ^ k) * coherenceMode n X := by
  induction k with
  | zero => simp [towerScalar_one]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      dsimp [opEulerLindbladStep]
      rw [lindbladDissipator_towerScalar_coh, smul_neg, ← sub_eq_add_neg, pow_succ']
      have h_rhs :
          towerScalar n ((1 - t • (m₀ * m₀)) * (1 - t • (m₀ * m₀)) ^ k) * coherenceMode n X =
          towerScalar n ((1 - t • (m₀ * m₀)) ^ k) * coherenceMode n X -
            t • (towerScalar n (m₀ * m₀ * (1 - t • (m₀ * m₀)) ^ k) *
              coherenceMode n X) := by
        rw [towerScalar_mul, towerScalar_sub, towerScalar_one, towerScalar_smul]
        rw [sub_mul, sub_mul, one_mul, tower_smul_mul, tower_smul_mul,
            ← towerScalar_mul (n := n) (m₀ * m₀)]
      exact h_rhs.symm

/-- **Banach-Algebra Trotter/Euler Exponential Limit**:
In any complete normed algebra `A` over `ℝ`, `(1 + (k : ℝ)⁻¹ • x) ^ k → NormedSpace.exp x`. -/
theorem tendsto_one_add_inv_smul_pow_exp [CompleteSpace A] [NormOneClass A] (x : A) :
    Filter.Tendsto (fun k : ℕ => (1 + (k : ℝ)⁻¹ • x) ^ k)
      Filter.atTop (nhds (NormedSpace.exp x)) := by
  have h_sum_A :
      Filter.Tendsto (fun k : ℕ => ∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ • x ^ j)
        Filter.atTop (nhds (NormedSpace.exp x)) := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
    have h_tsum := (NormedSpace.expSeries_summable (𝕂 := ℝ) x).hasSum.tendsto_sum_nat.comp
      (Filter.tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, NormedSpace.expSeries_apply_eq] using h_tsum
  have h_sum_R :
      Filter.Tendsto (fun k : ℕ => ∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ * ‖x‖ ^ j)
        Filter.atTop (nhds (Real.exp ‖x‖)) := by
    have h_tsum := (NormedSpace.expSeries_summable (𝕂 := ℝ) ‖x‖).hasSum.tendsto_sum_nat.comp
      (Filter.tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, NormedSpace.expSeries_apply_eq, smul_eq_mul] at h_tsum
    have h_exp_eq : Real.exp ‖x‖ = ∑' (n : ℕ), (n.factorial : ℝ)⁻¹ * ‖x‖ ^ n := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
      simp only [smul_eq_mul]
    rwa [h_exp_eq]
  have h_pow_R :
      Filter.Tendsto (fun k : ℕ => (1 + (k : ℝ)⁻¹ * ‖x‖) ^ k)
        Filter.atTop (nhds (Real.exp ‖x‖)) := by
    refine (Real.tendsto_one_add_div_pow_exp ‖x‖).congr (fun k => ?_)
    rw [div_eq_inv_mul]
  have h_diff_zero :
      Filter.Tendsto
        (fun k : ℕ =>
          (∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ * ‖x‖ ^ j) -
            (1 + (k : ℝ)⁻¹ * ‖x‖) ^ k)
        Filter.atTop (nhds 0) := by
    simpa [sub_self] using h_sum_R.sub h_pow_R
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero
    (g := fun k : ℕ =>
      ((∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ * ‖x‖ ^ j) -
        (1 + (k : ℝ)⁻¹ * ‖x‖) ^ k) +
      ‖(∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ • x ^ j) - NormedSpace.exp x‖)
    (fun k => norm_nonneg _) (fun k => ?_) ?_
  · have h_bin :
        (1 + (k : ℝ)⁻¹ • x) ^ k =
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℝ) * (k : ℝ)⁻¹ ^ j) • x ^ j := by
      have h_comm : Commute ((k : ℝ)⁻¹ • x) (1 : A) := Commute.one_right _
      rw [add_comm (1 : A), h_comm.add_pow]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [one_pow, mul_one, smul_pow, ← (Nat.cast_commute (k.choose j) _).eq,
          ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have h_bin_R :
        (1 + (k : ℝ)⁻¹ * ‖x‖) ^ k =
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℝ) * (k : ℝ)⁻¹ ^ j) * ‖x‖ ^ j := by
      rw [add_comm (1 : ℝ), add_pow]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [one_pow, mul_one, mul_pow]
      ring
    have h_coeff_le : ∀ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (k : ℝ)⁻¹ ^ j ≤ (j.factorial : ℝ)⁻¹ := by
      intro j _
      by_cases hk : k = 0
      · subst hk
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp
        · simp [Nat.choose_eq_zero_of_lt hj]
      · have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
        have h_desc : (k.choose j * j.factorial : ℝ) ≤ (k : ℝ) ^ j := by
          exact_mod_cast (by
            rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
            exact Nat.descFactorial_le_pow k j)
        have hj_pos : (0 : ℝ) < j.factorial := Nat.cast_pos.mpr (Nat.factorial_pos j)
        rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hk_pos j)]
        rw [← div_eq_inv_mul, le_div_iff₀ hj_pos]
        exact h_desc
    have h_step1 :
        ‖(1 + (k : ℝ)⁻¹ • x) ^ k -
          ∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ • x ^ j‖ ≤
        (∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ * ‖x‖ ^ j) -
          (1 + (k : ℝ)⁻¹ * ‖x‖) ^ k := by
      rw [h_bin, h_bin_R, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j hj => ?_))
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have h_le := h_coeff_le j hj
      have h_neg : ((k.choose j : ℝ) * (k : ℝ)⁻¹ ^ j - (j.factorial : ℝ)⁻¹) ≤ 0 :=
        sub_nonpos.mpr h_le
      rw [abs_of_nonpos h_neg, neg_sub, ← sub_mul]
      have h_pow_le : ‖x ^ j‖ ≤ ‖x‖ ^ j := by
        rcases Nat.eq_zero_or_pos j with rfl | hj_pos
        · simp [norm_one]
        · exact norm_pow_le' x hj_pos
      exact mul_le_mul_of_nonneg_left h_pow_le (sub_nonneg.mpr h_le)
    exact le_trans (norm_sub_le_norm_sub_add_norm_sub _
      (∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ • x ^ j) _)
      (add_le_add h_step1 le_rfl)
  · have h_S_norm :
        Filter.Tendsto
          (fun k : ℕ => ‖(∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ • x ^ j) -
            NormedSpace.exp x‖)
          Filter.atTop (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp h_sum_A
    simpa [add_zero] using h_diff_zero.add h_S_norm

/-- **Non-Scalar Operator Lindblad Semigroup Convergence in `ClInfOpCompletion A`**:
For any noncommutative `m₀ : A`, `t : ℝ`, and coherent mode `coherenceMode n X`, the iterated
Euler–Lindblad step `(opEulerLindbladStep m₀ (t / k) n)^[k] (coherenceMode n X)` converges in
`ClInfOpCompletion A` to the operator exponential `towerScalar n (exp (-t • (m₀ * m₀))) * Ψ_coh`. -/
theorem operator_lindblad_semigroup_convergence [CompleteSpace A] [NormOneClass A]
    (m₀ : A) (t : ℝ) (n : ℕ) (X : ClTower A n) :
    Filter.Tendsto
      (fun k : ℕ =>
        ((toClInfOp n ((opEulerLindbladStep m₀ (t / (k : ℝ)) n)^[k] (coherenceMode n X)) :
          ClInfOp A) : ClInfOpCompletion A))
      Filter.atTop
      (nhds ((toClInfOp n
        (towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode n X) :
          ClInfOp A) : ClInfOpCompletion A)) := by
  let x : A := -t • (m₀ * m₀)
  have h_lim := tendsto_one_add_inv_smul_pow_exp x
  have h_norm_zero :
      Filter.Tendsto
        (fun k : ℕ =>
          ‖(1 + (k : ℝ)⁻¹ • x) ^ k - NormedSpace.exp x‖ *
            opSumNorm n (coherenceMode n X))
        Filter.atTop (nhds 0) := by
    have h0 := (tendsto_iff_norm_sub_tendsto_zero.mp h_lim).mul_const
      (opSumNorm n (coherenceMode n X))
    simpa [zero_mul] using h0
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun k => norm_nonneg (_ : ClInfOpCompletion A)) (fun k => ?_) h_norm_zero
  rw [opEulerLindbladStep_iterate_coh]
  have h_step : 1 - (t / (k : ℝ)) • (m₀ * m₀) = 1 + (k : ℝ)⁻¹ • x := by
    dsimp [x]
    rw [sub_eq_add_neg, ← neg_smul, smul_smul]
    congr 1
    ring
  rw [h_step]
  have h_sub_coe :
      ((toClInfOp n (towerScalar n ((1 + (k : ℝ)⁻¹ • x) ^ k) * coherenceMode n X) :
        ClInfOp A) : ClInfOpCompletion A) -
      ((toClInfOp n (towerScalar n (NormedSpace.exp x) * coherenceMode n X) :
        ClInfOp A) : ClInfOpCompletion A) =
      ((toClInfOp n (towerScalar n ((1 + (k : ℝ)⁻¹ • x) ^ k - NormedSpace.exp x) *
        coherenceMode n X) : ClInfOp A) : ClInfOpCompletion A) := by
    rw [← UniformSpace.Completion.coe_sub, sub_toClInfOp, ← sub_mul, ← towerScalar_sub]
  rw [h_sub_coe, UniformSpace.Completion.norm_coe, norm_toClInfOp]
  exact opSumNorm_towerScalar_mul_le n _ _

/-- **Coercive Exponential Decay of the Non-Scalar Operator Lindblad Semigroup**:
If the Euler contraction bound `‖1 - (t / k) • (m₀ * m₀)‖ ≤ 1 - (t / k) * μ²` holds for large `k`,
then the limiting operator-exponential state in `ClInfOpCompletion A` satisfies the coercive
mass-gap bound `‖exp(-t m₀²) Ψ_coh‖ ≤ exp(-t μ²) ‖Ψ_coh‖`. -/
theorem operator_lindblad_coercive_decay [CompleteSpace A] [NormOneClass A]
    (m₀ : A) (t μ : ℝ)
    (h_gap : ∀ k : ℕ, t * (μ * μ) ≤ k →
      ‖1 - (t / (k : ℝ)) • (m₀ * m₀)‖ ≤ 1 - (t / (k : ℝ)) * (μ * μ))
    (n : ℕ) (X : ClTower A n) :
    ‖((toClInfOp n
      (towerScalar n (NormedSpace.exp (-t • (m₀ * m₀))) * coherenceMode n X) :
        ClInfOp A) : ClInfOpCompletion A)‖ ≤
      Real.exp (-t * (μ * μ)) *
        ‖((toClInfOp n (coherenceMode n X) : ClInfOp A) : ClInfOpCompletion A)‖ := by
  have h_lhs := (operator_lindblad_semigroup_convergence m₀ t n X).norm
  have h_rhs_base :
      Filter.Tendsto (fun k : ℕ => (1 + (k : ℝ)⁻¹ * (-t * (μ * μ))) ^ k)
        Filter.atTop (nhds (Real.exp (-t * (μ * μ)))) := by
    refine (Real.tendsto_one_add_div_pow_exp (-t * (μ * μ))).congr (fun k => ?_)
    rw [div_eq_inv_mul]
  have h_rhs := h_rhs_base.mul_const
    ‖((toClInfOp n (coherenceMode n X) : ClInfOp A) : ClInfOpCompletion A)‖
  refine le_of_tendsto_of_tendsto h_lhs h_rhs ?_
  refine Filter.eventually_atTop.mpr ⟨Nat.ceil (max 1 (t * (μ * μ))), fun k hk => ?_⟩
  have hk_ge_1 : (1 : ℝ) ≤ k := by
    exact le_trans (le_max_left 1 (t * (μ * μ))) (Nat.le_of_ceil_le hk)
  have hk_pos : 0 < k := by
    have : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk_ge_1
    exact Nat.cast_pos.mp this
  have hk_gap : t * (μ * μ) ≤ k :=
    le_trans (le_max_right 1 (t * (μ * μ))) (Nat.le_of_ceil_le hk)
  dsimp only
  rw [opEulerLindbladStep_iterate_coh, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, norm_toClInfOp, norm_toClInfOp]
  refine le_trans (opSumNorm_towerScalar_mul_le n _ _) ?_
  refine mul_le_mul_of_nonneg_right ?_ (opSumNorm_nonneg n (coherenceMode n X))
  have h_pow_norm :
      ‖(1 - (t / (k : ℝ)) • (m₀ * m₀)) ^ k‖ ≤ ‖1 - (t / (k : ℝ)) • (m₀ * m₀)‖ ^ k :=
    norm_pow_le' _ hk_pos
  have h_pow_gap :
      ‖1 - (t / (k : ℝ)) • (m₀ * m₀)‖ ^ k ≤ (1 - (t / (k : ℝ)) * (μ * μ)) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (h_gap k hk_gap) k
  have h_eq : (1 - (t / (k : ℝ)) * (μ * μ)) ^ k = (1 + (k : ℝ)⁻¹ * (-t * (μ * μ))) ^ k := by
    congr 1
    ring
  rw [← h_eq]
  exact le_trans h_pow_norm h_pow_gap

private theorem clInfOp_noncomm_witness {A : Type u} [NormedRing A] [Nontrivial A] :
    ∃ x y : ClInfOp A, x * y ≠ y * x := by
  let e01 : ClTower A 1 := mat2 (0 : A) 1 0 0
  let e10 : ClTower A 1 := mat2 (0 : A) 0 1 0
  refine ⟨toClInfOp 1 e01, toClInfOp 1 e10, ?_⟩
  intro h
  have h_zero : toClInfOp 1 (e01 * e10 - e10 * e01) = 0 := by
    rw [← sub_toClInfOp, ← mul_toClInfOp, ← mul_toClInfOp, h, sub_self]
  have h_norm : ‖toClInfOp 1 (e01 * e10 - e10 * e01)‖ = 0 := by
    rw [h_zero, norm_zero]
  rw [norm_toClInfOp] at h_norm
  have h_pos : 0 < opSumNorm 1 (e01 * e10 - e10 * e01) := by
    have h1 : (0 : ℝ) < ‖(1 : A)‖ := norm_pos_iff.mpr one_ne_zero
    have h00 : (e01 * e10 - e10 * e01) 0 0 = (1 : A) := by
      simp [e01, e10, mat2, Matrix.mul_apply, Fin.sum_univ_two]
    have h00' : opSumNorm 0 ((e01 * e10 - e10 * e01) 0 0) = ‖(1 : A)‖ := by
      rw [h00]; rfl
    have h01 := opSumNorm_nonneg 0 ((e01 * e10 - e10 * e01) 0 1)
    have h10 := opSumNorm_nonneg 0 ((e01 * e10 - e10 * e01) 1 0)
    have h11 := opSumNorm_nonneg 0 ((e01 * e10 - e10 * e01) 1 1)
    change 0 < opSumNorm 0 _ + opSumNorm 0 _ + opSumNorm 0 _ + opSumNorm 0 _
    rw [h00']
    linarith
  linarith

end NonScalarOperatorSemigroup

end InfoGeometry.Algebra.NoncommutativeColimitCStarCompletionAndOperatorSemigroup
