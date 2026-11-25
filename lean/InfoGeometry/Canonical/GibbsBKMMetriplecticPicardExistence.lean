/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Picard–Lindelöf existence, uniqueness, and unconditional Second Law for the Gibbs–BKM flow

This module resolves the open Bucket 3 analytical boundary documented in
`BKMMetriplecticTrajectorySecondLaw`: internal ODE existence and uniqueness for
the nonlinear noncommutative Gibbs–BKM metriplectic equation

  H'(t) = -i [H_eq, H(t)] - K_{D_{H(t)}}(ρ_{H(t)} - σ).

1. **Infinite-dimensional Banach-algebra smoothness of `exponentialDerivative`:**
   For any complete real Banach algebra `A`, `NormedSpace.exp : A → A` is
   `ContDiff ℝ (⊤ : WithTop ℕ∞)`, its real Fréchet derivative equals
   `exponentialDerivative (𝕜 := ℝ)`, and `exponentialDerivative` is itself
   `ContDiff ℝ (⊤ : WithTop ℕ∞)`.
2. **Closed self-adjoint real Banach subspace `SelfAdjointOp n`:**
   Self-adjoint operators in `FiniteOperatorAlgebra n` form a closed `ℝ`-linear
   subspace (hence a `CompleteSpace`), with continuous `ℝ`-linear inclusion
   `selfAdjointSubtypeL` and self-adjoint projection `symPartCLM`.
3. **Ambient & restricted smooth Gibbs–BKM vector fields:**
   On `{ H | tracedExponential H ≠ 0 }`, the ambient vector field
   `H ↦ gibbsUnitaryVectorField H_eq H - (tracedExponential H)⁻¹ • exponentialDerivative (𝕜 := ℝ) H (normalizedExponential H - σ)`
   is analytic-smooth (`ContDiffAt ℝ (⊤ : WithTop ℕ∞)`); on `SelfAdjointOp n`,
   `tracedExponential` has strictly positive real part everywhere, making
   `gibbsMetriplecticFieldSA` `C¹` everywhere on `SelfAdjointOp n` and equal
   to `gibbsMetriplecticFlow` on every self-adjoint operator.
4. **Internal Cauchy–Lipschitz / Picard–Lindelöf existence & Grönwall uniqueness:**
   Derives `IsPicardLindelof`, local integral trajectories, Lipschitz local flows,
   and two-sided (forward and backward) uniqueness on `Set.Icc tmin tmax` via
   Grönwall's inequality.
5. **Unconditional end-to-end Second Law & primal density ODE:**
   Combines internal existence with `BKMMetriplecticTrajectorySecondLaw` so no
   externally supplied `HasDerivAt` trajectory hypothesis is needed.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace InfoGeometry.Canonical.GibbsBKMMetriplecticPicardExistence

open MeasureTheory
open scoped Interval NNReal
open SouriauOnsagerBKM
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsSecondDerivativeCenteredBridge
open InfoGeometry.Canonical.BKMMetriplecticTrajectorySecondLaw

/-! ## Section 1: Infinite-Dimensional Banach-Algebra Smoothness -/

section InfiniteDimExpSmoothness

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In any complete real Banach algebra, `NormedSpace.exp` is real analytic, hence
`ContDiff ℝ (⊤ : WithTop ℕ∞)`. -/
theorem contDiff_exp_real :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (NormedSpace.exp : A → A) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  rw [contDiff_iff_contDiffAt]
  intro a
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := A) a).contDiffAt

/-- The real Fréchet derivative `fderiv ℝ NormedSpace.exp a` equals the
noncommutative changed-origin derivative `exponentialDerivative (𝕜 := ℝ) a`. -/
theorem fderiv_exp_eq_exponentialDerivative (a : A) :
    fderiv ℝ (NormedSpace.exp : A → A) a = exponentialDerivative (𝕜 := ℝ) a := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact (hasFDerivAt_exp_noncommutative (𝕜 := ℝ) (A := A) a).fderiv

/-- The noncommutative exponential derivative `a ↦ exponentialDerivative (𝕜 := ℝ) a`
is `ContDiff ℝ (⊤ : WithTop ℕ∞)` into `A →L[ℝ] A` on any complete real Banach algebra. -/
theorem contDiff_exponentialDerivative :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (exponentialDerivative (𝕜 := ℝ) : A → (A →L[ℝ] A)) := by
  have hfd :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (NormedSpace.exp : A → A)) :=
    (contDiff_exp_real (A := A)).fderiv_right le_top
  simpa only [show (fderiv ℝ (NormedSpace.exp : A → A)) =
      (exponentialDerivative (𝕜 := ℝ) : A → (A →L[ℝ] A)) from
    funext (fderiv_exp_eq_exponentialDerivative (A := A))] using hfd

/-- Composition of `exponentialDerivative` with `ContDiffAt` curve and direction
maps remains `ContDiffAt` at the same order. -/
theorem contDiffAt_exponentialDerivative_apply
    {m : WithTop ℕ∞} {g v : E → A} {x₀ : E}
    (hg : ContDiffAt ℝ m g x₀) (hv : ContDiffAt ℝ m v x₀) :
    ContDiffAt ℝ m (fun x => exponentialDerivative (𝕜 := ℝ) (g x) (v x)) x₀ := by
  have hexp :
      ContDiffAt ℝ m (fun x => exponentialDerivative (𝕜 := ℝ) (g x)) x₀ :=
    ((contDiff_exponentialDerivative (A := A)).of_le (le_top : m ≤ ⊤)).contDiffAt.comp x₀ hg
  exact hexp.clm_apply hv

end InfiniteDimExpSmoothness

/-! ## Section 2: Closed Real Banach Subspace of Self-Adjoint Operators -/

section SelfAdjointSubspace

private theorem adjoint_real_smul {n : ℕ} (r : ℝ) (X : FiniteOperatorAlgebra n) :
    ContinuousLinearMap.adjoint (r • X) = r • ContinuousLinearMap.adjoint X := by
  change star ((r : ℂ) • X) = (r : ℂ) • star X
  rw [star_smul, Complex.star_def, Complex.conj_ofReal]

/-- Real submodule of self-adjoint operators in `FiniteOperatorAlgebra n`. -/
def selfAdjointSubmodule (n : ℕ) : Submodule ℝ (FiniteOperatorAlgebra n) where
  carrier := { H | IsSelfAdjoint H }
  zero_mem' := by
    change ContinuousLinearMap.adjoint (0 : FiniteOperatorAlgebra n) = 0
    simp
  add_mem' := by
    intro X Y hX hY
    change ContinuousLinearMap.adjoint (X + Y) = X + Y
    have hX' : ContinuousLinearMap.adjoint X = X := hX
    have hY' : ContinuousLinearMap.adjoint Y = Y := hY
    rw [map_add, hX', hY']
  smul_mem' := by
    intro r X (hX : IsSelfAdjoint X)
    change ContinuousLinearMap.adjoint (r • X) = r • X
    rw [adjoint_real_smul r X]
    exact congrArg (r • ·) hX.star_eq

/-- The real Banach subspace of self-adjoint finite operators. -/
abbrev SelfAdjointOp (n : ℕ) := selfAdjointSubmodule n

/-- `selfAdjointSubmodule n` is closed in `FiniteOperatorAlgebra n`. -/
theorem isClosed_selfAdjointSubmodule (n : ℕ) :
    IsClosed (selfAdjointSubmodule n : Set (FiniteOperatorAlgebra n)) := by
  have hcont_star : Continuous (star : FiniteOperatorAlgebra n → FiniteOperatorAlgebra n) :=
    ContinuousLinearMap.adjoint.continuous
  have hcont : Continuous (fun X : FiniteOperatorAlgebra n => star X - X) :=
    hcont_star.sub continuous_id
  have heq :
      (selfAdjointSubmodule n : Set (FiniteOperatorAlgebra n)) =
        (fun X : FiniteOperatorAlgebra n => star X - X) ⁻¹' {(0 : FiniteOperatorAlgebra n)} := by
    ext X
    simp [selfAdjointSubmodule, sub_eq_zero]
    rfl
  rw [heq]
  exact isClosed_singleton.preimage hcont

/-- Every closed subspace of a complete space is complete. -/
instance instCompleteSpaceSelfAdjointOp (n : ℕ) : CompleteSpace (SelfAdjointOp n) :=
  (isClosed_selfAdjointSubmodule n).completeSpace_coe

/-- Continuous `ℝ`-linear inclusion `SelfAdjointOp n →L[ℝ] FiniteOperatorAlgebra n`. -/
noncomputable def selfAdjointSubtypeL (n : ℕ) :
    SelfAdjointOp n →L[ℝ] FiniteOperatorAlgebra n :=
  (selfAdjointSubmodule n).subtypeL

@[simp] theorem selfAdjointSubtypeL_apply (n : ℕ) (H : SelfAdjointOp n) :
    selfAdjointSubtypeL n H = H.1 :=
  rfl

/-- `selfAdjointSubtypeL n` is isometric (`‖H.1‖ = ‖H‖`). -/
theorem norm_selfAdjointSubtypeL (n : ℕ) (H : SelfAdjointOp n) :
    ‖selfAdjointSubtypeL n H‖ = ‖H‖ :=
  rfl

/-- Algebraic `ℝ`-linear self-adjoint part projection `X ↦ (1/2 : ℝ) • (X + star X)`. -/
noncomputable def symPartLinear (n : ℕ) :
    FiniteOperatorAlgebra n →ₗ[ℝ] SelfAdjointOp n where
  toFun X :=
    ⟨((1 / 2 : ℝ) • (X + star X)), by
      change ContinuousLinearMap.adjoint ((1 / 2 : ℝ) • (X + star X)) =
        (1 / 2 : ℝ) • (X + star X)
      rw [adjoint_real_smul, map_add]
      change (1 / 2 : ℝ) • (star X + star (star X)) = (1 / 2 : ℝ) • (X + star X)
      rw [star_star, add_comm]⟩
  map_add' X Y := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • ((X + Y) + ContinuousLinearMap.adjoint (X + Y)) =
      (1 / 2 : ℝ) • (X + ContinuousLinearMap.adjoint X) +
        (1 / 2 : ℝ) • (Y + ContinuousLinearMap.adjoint Y)
    rw [map_add]
    have hr :
        (X + Y) + (ContinuousLinearMap.adjoint X + ContinuousLinearMap.adjoint Y) =
          (X + ContinuousLinearMap.adjoint X) + (Y + ContinuousLinearMap.adjoint Y) := by
      abel
    rw [hr, smul_add]
  map_smul' r X := by
    apply Subtype.ext
    change (1 / 2 : ℝ) • (r • X + ContinuousLinearMap.adjoint (r • X)) =
      r • ((1 / 2 : ℝ) • (X + ContinuousLinearMap.adjoint X))
    rw [adjoint_real_smul, smul_add, smul_add, smul_add,
      smul_comm (1 / 2 : ℝ) r X, smul_comm (1 / 2 : ℝ) r (ContinuousLinearMap.adjoint X)]

/-- Continuous `ℝ`-linear symmetrization map `FiniteOperatorAlgebra n →L[ℝ] SelfAdjointOp n`. -/
noncomputable def symPartCLM (n : ℕ) :
    FiniteOperatorAlgebra n →L[ℝ] SelfAdjointOp n where
  toLinearMap := symPartLinear n
  cont := by
    have hcont : Continuous (fun X : FiniteOperatorAlgebra n => (1 / 2 : ℝ) • (X + star X)) :=
      (continuous_id.add ContinuousLinearMap.adjoint.continuous).const_smul (1 / 2 : ℝ)
    exact hcont.subtype_mk _

@[simp] theorem symPartCLM_apply (n : ℕ) (X : FiniteOperatorAlgebra n) :
    (symPartCLM n X).1 = (1 / 2 : ℝ) • (X + star X) :=
  rfl

/-- `symPartCLM n` is a left inverse to `selfAdjointSubtypeL n`. -/
@[simp] theorem symPartCLM_selfAdjointSubtypeL (n : ℕ) (H : SelfAdjointOp n) :
    symPartCLM n (selfAdjointSubtypeL n H) = H := by
  apply Subtype.ext
  rw [symPartCLM_apply, selfAdjointSubtypeL_apply, H.2.star_eq]
  rw [← two_smul ℝ H.1, smul_smul]
  norm_num

/-- On a self-adjoint ambient operator `X`, `selfAdjointSubtypeL n (symPartCLM n X) = X`. -/
theorem selfAdjointSubtypeL_symPartCLM_of_isSelfAdjoint
    {n : ℕ} {X : FiniteOperatorAlgebra n} (hX : IsSelfAdjoint X) :
    selfAdjointSubtypeL n (symPartCLM n X) = X := by
  rw [selfAdjointSubtypeL_apply, symPartCLM_apply, hX.star_eq]
  rw [← two_smul ℝ X, smul_smul]
  norm_num

end SelfAdjointSubspace

/-! ## Section 3: Smooth Ambient & Self-Adjoint Gibbs–BKM Vector Fields -/

section SmoothGibbsVectorField

private theorem isBoundedBilinearMap_complex_smul_real (n : ℕ) :
    IsBoundedBilinearMap ℝ
      (fun p : ℂ × FiniteOperatorAlgebra n => p.1 • p.2) where
  add_left := fun c₁ c₂ X => add_smul c₁ c₂ X
  smul_left := fun r c X => by
    rw [real_smul_eq_complex_smul, smul_smul]
    rfl
  add_right := fun c X₁ X₂ => smul_add c X₁ X₂
  smul_right := fun r c X => by
    rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul, smul_comm]
  bound := ⟨1, zero_lt_one, fun c X => by
    rw [one_mul]
    exact norm_smul_le c X⟩

private theorem contDiffAt_complex_smul_real
    {n : ℕ} {m : WithTop ℕ∞}
    {c : FiniteOperatorAlgebra n → ℂ} {f : FiniteOperatorAlgebra n → FiniteOperatorAlgebra n}
    {H₀ : FiniteOperatorAlgebra n}
    (hc : ContDiffAt ℝ m c H₀) (hf : ContDiffAt ℝ m f H₀) :
    ContDiffAt ℝ m (fun H => c H • f H) H₀ :=
  ((isBoundedBilinearMap_complex_smul_real n).contDiff.of_le (le_top : m ≤ ⊤)).comp₂_contDiffAt hc hf

/-- Ambient nonlinear Gibbs–BKM metriplectic vector field on `FiniteOperatorAlgebra n`:
`-i [H_eq, H] - (tracedExponential H)⁻¹ • exponentialDerivative (𝕜 := ℝ) H (normalizedExponential H - σ)`. -/
noncomputable def gibbsMetriplecticFieldAmbient
    {n : ℕ} (H_eq σ H : FiniteOperatorAlgebra n) : FiniteOperatorAlgebra n :=
  gibbsUnitaryVectorField H_eq H -
    (tracedExponential H)⁻¹ •
      exponentialDerivative (𝕜 := ℝ) H (normalizedExponential H - σ)

/-- On any self-adjoint operator `H` in nonzero dimension, `gibbsMetriplecticFieldAmbient`
agrees identically with `gibbsMetriplecticFlow`. -/
theorem gibbsMetriplecticFieldAmbient_eq_gibbsMetriplecticFlow
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ H : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) :
    gibbsMetriplecticFieldAmbient H_eq σ H = gibbsMetriplecticFlow H_eq σ H hH := by
  have hZ : 0 < gibbsPartitionReal H := tracedExponential_re_pos_of_isSelfAdjoint H hH
  let D := faithfulGibbsDensity H hH hZ
  have hρ : normalizedExponential H = D.rho :=
    (faithfulGibbsDensity_rho_eq_normalizedExponential H hH hZ).symm
  have hdiss :
      (tracedExponential H)⁻¹ •
          exponentialDerivative (𝕜 := ℝ) H (normalizedExponential H - σ) =
        D.kuboMoriTransform (D.rho - σ) := by
    rw [hρ, gibbs_exponentialDerivative_eq_duhamelDerivative H]
    exact inv_tracedExponential_smul_duhamelDerivative_eq_kuboMoriTransform H (D.rho - σ) hH hZ
  unfold gibbsMetriplecticFieldAmbient gibbsMetriplecticFlow gibbsBKMDissipativeField
  rw [hdiss, sub_eq_add_neg]

/-- `tracedExponential` is `ContDiff ℝ (⊤ : WithTop ℕ∞)` as a real map
`FiniteOperatorAlgebra n → ℂ`. -/
theorem contDiff_tracedExponential_real (n : ℕ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (tracedExponential : FiniteOperatorAlgebra n → ℂ) := by
  have htr :
      (tracedExponential : FiniteOperatorAlgebra n → ℂ) =
        fun H => (finiteOperatorTraceRealCLM n) (NormedSpace.exp H) := rfl
  rw [htr]
  exact ((finiteOperatorTraceRealCLM n).contDiff.of_le le_top).comp
    (contDiff_exp_real (A := FiniteOperatorAlgebra n))

/-- `normalizedExponential` is `ContDiffAt ℝ (⊤ : WithTop ℕ∞)` at any point where
`tracedExponential H₀ ≠ 0`. -/
theorem contDiffAt_normalizedExponential_real
    {n : ℕ} {H₀ : FiniteOperatorAlgebra n} (hZ : tracedExponential H₀ ≠ 0) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (normalizedExponential : FiniteOperatorAlgebra n → FiniteOperatorAlgebra n) H₀ := by
  have hinv : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun H => (tracedExponential H)⁻¹) H₀ :=
    ((contDiff_tracedExponential_real n).contDiffAt).inv hZ
  have hexp :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (NormedSpace.exp : FiniteOperatorAlgebra n → FiniteOperatorAlgebra n) H₀ :=
    (contDiff_exp_real (A := FiniteOperatorAlgebra n)).contDiffAt
  exact contDiffAt_complex_smul_real hinv hexp

/-- `gibbsUnitaryVectorField H_eq` is a continuous `ℝ`-linear endomorphism, hence `C^∞`. -/
noncomputable def gibbsUnitaryCLM {n : ℕ} (H_eq : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n →L[ℝ] FiniteOperatorAlgebra n where
  toFun H := gibbsUnitaryVectorField H_eq H
  map_add' X Y := by
    unfold gibbsUnitaryVectorField
    rw [mul_add, add_mul]
    have hr : H_eq * X + H_eq * Y - (X * H_eq + Y * H_eq) =
        (H_eq * X - X * H_eq) + (H_eq * Y - Y * H_eq) := by abel
    rw [hr, smul_add]
  map_smul' r X := by
    unfold gibbsUnitaryVectorField
    change -Complex.I • (H_eq * ((r : ℂ) • X) - ((r : ℂ) • X) * H_eq) =
      (r : ℂ) • (-Complex.I • (H_eq * X - X * H_eq))
    rw [mul_smul_comm, smul_mul_assoc]
    have hsub :
        (r : ℂ) • (H_eq * X) - (r : ℂ) • (X * H_eq) =
          (r : ℂ) • (H_eq * X - X * H_eq) :=
      (smul_sub (r : ℂ) _ _).symm
    rw [hsub, smul_comm]
  cont := by
    unfold gibbsUnitaryVectorField
    exact ((continuous_const.mul continuous_id).sub
      (continuous_id.mul continuous_const)).const_smul (-Complex.I)

@[simp] theorem gibbsUnitaryCLM_apply {n : ℕ} (H_eq H : FiniteOperatorAlgebra n) :
    gibbsUnitaryCLM H_eq H = gibbsUnitaryVectorField H_eq H :=
  rfl

/-- Smoothness (`ContDiffAt ℝ (⊤ : WithTop ℕ∞)`) of `gibbsMetriplecticFieldAmbient H_eq σ`
at every point with nonvanishing traced exponential. -/
theorem contDiffAt_gibbsMetriplecticFieldAmbient
    {n : ℕ} (H_eq σ H₀ : FiniteOperatorAlgebra n) (hZ : tracedExponential H₀ ≠ 0) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (gibbsMetriplecticFieldAmbient H_eq σ) H₀ := by
  have hrev :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun H => gibbsUnitaryVectorField H_eq H) H₀ := by
    change ContDiffAt ℝ (⊤ : WithTop ℕ∞) (gibbsUnitaryCLM H_eq) H₀
    exact ((gibbsUnitaryCLM H_eq).contDiff.of_le le_top).contDiffAt
  have hinv : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun H => (tracedExponential H)⁻¹) H₀ :=
    ((contDiff_tracedExponential_real n).contDiffAt).inv hZ
  have hnorm : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun H => normalizedExponential H - σ) H₀ :=
    (contDiffAt_normalizedExponential_real hZ).sub contDiffAt_const
  have hexp_dir :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun H => exponentialDerivative (𝕜 := ℝ) H (normalizedExponential H - σ)) H₀ :=
    contDiffAt_exponentialDerivative_apply contDiffAt_id hnorm
  have hdiss :
      ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun H =>
          (tracedExponential H)⁻¹ •
            exponentialDerivative (𝕜 := ℝ) H (normalizedExponential H - σ)) H₀ :=
    contDiffAt_complex_smul_real hinv hexp_dir
  exact hrev.sub hdiss

/-- Self-adjoint restriction of the Gibbs–BKM metriplectic vector field onto
the closed Banach subspace `SelfAdjointOp n`. -/
noncomputable def gibbsMetriplecticFieldSA
    {n : ℕ} (H_eq σ : FiniteOperatorAlgebra n) (H : SelfAdjointOp n) : SelfAdjointOp n :=
  symPartCLM n (gibbsMetriplecticFieldAmbient H_eq σ (selfAdjointSubtypeL n H))

/-- `selfAdjointSubtypeL` sends `gibbsMetriplecticFieldSA` back to `gibbsMetriplecticFlow`
without projection loss whenever `H_eq` and `σ` are self-adjoint. -/
theorem selfAdjointSubtypeL_gibbsMetriplecticFieldSA
    {n : ℕ} [Nonempty (Fin n)]
    {H_eq σ : FiniteOperatorAlgebra n} (hH_eq : IsSelfAdjoint H_eq) (hσ : IsSelfAdjoint σ)
    (H : SelfAdjointOp n) :
    selfAdjointSubtypeL n (gibbsMetriplecticFieldSA H_eq σ H) =
      gibbsMetriplecticFlow H_eq σ H.1 H.2 := by
  unfold gibbsMetriplecticFieldSA
  rw [selfAdjointSubtypeL_apply, selfAdjointSubtypeL_apply]
  rw [gibbsMetriplecticFieldAmbient_eq_gibbsMetriplecticFlow H_eq σ H.1 H.2]
  exact selfAdjointSubtypeL_symPartCLM_of_isSelfAdjoint
    (isSelfAdjoint_gibbsMetriplecticFlow hH_eq hσ H.2)

/-- `gibbsMetriplecticFieldSA` is everywhere `C^1` on `SelfAdjointOp n`. -/
theorem contDiffAt_gibbsMetriplecticFieldSA
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (H₀ : SelfAdjointOp n) :
    ContDiffAt ℝ (1 : WithTop ℕ∞) (gibbsMetriplecticFieldSA H_eq σ) H₀ := by
  have hZ : tracedExponential H₀.1 ≠ 0 :=
    Complex.slitPlane_ne_zero (tracedExponential_mem_slitPlane_of_isSelfAdjoint H₀.1 H₀.2)
  have hamb :
      ContDiffAt ℝ (1 : WithTop ℕ∞)
        (gibbsMetriplecticFieldAmbient H_eq σ) (selfAdjointSubtypeL n H₀) :=
    (contDiffAt_gibbsMetriplecticFieldAmbient H_eq σ H₀.1 hZ).of_le le_top
  have hsub_bd : IsBoundedLinearMap ℝ (fun H : SelfAdjointOp n => selfAdjointSubtypeL n H) :=
    { map_add := fun _ _ => rfl
      map_smul := fun r H => by
        change (r • H).1 = (r : ℂ) • H.1
        rfl
      bound := ⟨1, zero_lt_one, fun H => by rw [one_mul]; rfl⟩ }
  have hsym_bd : IsBoundedLinearMap ℝ (fun X : FiniteOperatorAlgebra n => symPartCLM n X) :=
    { map_add := fun X Y => (symPartCLM n).map_add X Y
      map_smul := fun r X => by
        apply Subtype.ext
        change (1 / 2 : ℝ) • ((r : ℂ) • X + ContinuousLinearMap.adjoint ((r : ℂ) • X)) =
          (r • symPartCLM n X).1
        have hs : ContinuousLinearMap.adjoint ((r : ℂ) • X) = (r : ℂ) • ContinuousLinearMap.adjoint X :=
          adjoint_real_smul r X
        rw [hs]
        apply ContinuousLinearMap.ext
        intro v
        ext i
        simp [real_smul_eq_complex_smul]
        ring_nf
        rfl
      bound := ⟨1, zero_lt_one, fun X => by
        change ‖(symPartCLM n X).1‖ ≤ 1 * ‖X‖
        rw [symPartCLM_apply, one_mul, norm_smul, Real.norm_of_nonneg (by positivity)]
        have hadd : ‖X + star X‖ ≤ ‖X‖ + ‖star X‖ := norm_add_le _ _
        have hstar : ‖star X‖ = ‖X‖ := by
          change ‖ContinuousLinearMap.adjoint X‖ = ‖X‖
          exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint X
        linarith⟩ }
  have hsub :
      ContDiffAt ℝ (1 : WithTop ℕ∞) (fun H : SelfAdjointOp n => selfAdjointSubtypeL n H) H₀ :=
    hsub_bd.contDiff.contDiffAt
  have hsym :
      ContDiffAt ℝ (1 : WithTop ℕ∞) (fun X : FiniteOperatorAlgebra n => symPartCLM n X)
        (gibbsMetriplecticFieldAmbient H_eq σ (selfAdjointSubtypeL n H₀)) :=
    hsym_bd.contDiff.contDiffAt
  exact hsym.comp H₀ (hamb.comp H₀ hsub)

end SmoothGibbsVectorField

/-! ## Section 4: Internal Picard–Lindelöf Existence, Lipschitz Flow & Uniqueness -/

section PicardExistenceAndUniqueness

/-- Every self-adjoint initial Hamiltonian `H₀` satisfies the Cauchy–Lipschitz /
Picard–Lindelöf hypothesis for `gibbsMetriplecticFieldSA` around any base time `t₀`. -/
theorem exists_isPicardLindelof_gibbsMetriplecticFieldSA
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (H₀ : SelfAdjointOp n) :
    ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r),
      ∀ (t₀ : ℝ),
        IsPicardLindelof (fun _ => gibbsMetriplecticFieldSA H_eq σ)
          (tmin := t₀ - ε) (tmax := t₀ + ε)
          ⟨t₀, by simp [le_of_lt hε]⟩ H₀ a r L K :=
  IsPicardLindelof.of_contDiffAt_one (contDiffAt_gibbsMetriplecticFieldSA H_eq σ H₀)

/-- Internal Picard–Lindelöf existence of a local solution `H : ℝ → FiniteOperatorAlgebra n`
on `[t₀ - ε, t₀ + ε]` preserving self-adjointness and solving `gibbsMetriplecticFlow`. -/
theorem exists_gibbsMetriplectic_trajectory
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n)
    (hH_eq : IsSelfAdjoint H_eq) (hσ : IsSelfAdjoint σ)
    (H₀ : FiniteOperatorAlgebra n) (hH₀ : IsSelfAdjoint H₀) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : ℝ → FiniteOperatorAlgebra n,
      H t₀ = H₀ ∧
      ∃ hSA : ∀ t, IsSelfAdjoint (H t),
        (∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt H (gibbsMetriplecticFlow H_eq σ (H t) (hSA t))
            (Set.Icc (t₀ - ε) (t₀ + ε)) t) ∧
        (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) (hSA t)) t) := by
  let H₀SA : SelfAdjointOp n := ⟨H₀, hH₀⟩
  obtain ⟨ε, hε, a, r, L, K, _, hpl⟩ :=
    exists_isPicardLindelof_gibbsMetriplecticFieldSA H_eq σ H₀SA
  have hpl0 := hpl t₀
  obtain ⟨α, hα0, hα_deriv⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hpl0
      (Metric.mem_closedBall_self (NNReal.coe_nonneg r))
  let H : ℝ → FiniteOperatorAlgebra n := fun t => selfAdjointSubtypeL n (α t)
  have hSA : ∀ t, IsSelfAdjoint (H t) := fun t => (α t).2
  have hderiv_within :
      ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
        HasDerivWithinAt H (gibbsMetriplecticFlow H_eq σ (H t) (hSA t))
          (Set.Icc (t₀ - ε) (t₀ + ε)) t := by
    intro t ht
    have hcomp :
        HasDerivWithinAt ((selfAdjointSubtypeL n) ∘ α)
          (selfAdjointSubtypeL n (gibbsMetriplecticFieldSA H_eq σ (α t)))
          (Set.Icc (t₀ - ε) (t₀ + ε)) t :=
      (selfAdjointSubtypeL n).hasFDerivAt.comp_hasDerivWithinAt t (hα_deriv t ht)
    rw [selfAdjointSubtypeL_gibbsMetriplecticFieldSA hH_eq hσ (α t)] at hcomp
    exact hcomp
  have hderiv_open :
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) (hSA t)) t := by
    intro t ht
    exact (hderiv_within t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hinit : H t₀ = H₀ := by
    change selfAdjointSubtypeL n (α t₀) = H₀
    rw [hα0]
    rfl
  exact ⟨ε, hε, H, hinit, hSA, hderiv_within, hderiv_open⟩

/-- Local flow `Φ : SelfAdjointOp n → ℝ → SelfAdjointOp n` with explicit `LipschitzOnWith`
dependence on initial Hamiltonians in `Metric.closedBall H₀ r`. -/
theorem exists_gibbsMetriplectic_localFlow_lipschitzOnWith
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n) (H₀ : SelfAdjointOp n) (t₀ : ℝ) :
    ∃ (ε : ℝ) (_ : 0 < ε) (r L' : ℝ≥0) (_ : 0 < r)
      (Φ : SelfAdjointOp n → ℝ → SelfAdjointOp n),
      (∀ H ∈ Metric.closedBall H₀ r, Φ H t₀ = H ∧
        ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt (Φ H) (gibbsMetriplecticFieldSA H_eq σ (Φ H t))
            (Set.Icc (t₀ - ε) (t₀ + ε)) t) ∧
      (∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
        LipschitzOnWith L' (fun H => Φ H t) (Metric.closedBall H₀ r)) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    exists_isPicardLindelof_gibbsMetriplecticFieldSA H_eq σ H₀
  obtain ⟨Φ, hΦ_sol, L', hΦ_lip⟩ :=
    (hpl t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  exact ⟨ε, hε, r, L', hr, Φ, hΦ_sol, hΦ_lip⟩

private theorem ode_unique_on_Icc_of_lipschitzOnWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E → E) {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (U : Set E) {K : ℝ≥0}
    (hv_lip : LipschitzOnWith K v U)
    {x y : ℝ → E}
    (hx_cont : ContinuousOn x (Set.Icc tmin tmax))
    (hx_deriv : ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt x (v (x t)) (Set.Icc tmin tmax) t)
    (hx_mem : ∀ t ∈ Set.Icc tmin tmax, x t ∈ U)
    (hy_cont : ContinuousOn y (Set.Icc tmin tmax))
    (hy_deriv : ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt y (v (y t)) (Set.Icc tmin tmax) t)
    (hy_mem : ∀ t ∈ Set.Icc tmin tmax, y t ∈ U)
    (hinit : x t₀ = y t₀) :
    ∀ t ∈ Set.Icc tmin tmax, x t = y t := by
  have hfwd : ∀ t ∈ Set.Icc (t₀ : ℝ) tmax, x t = y t := by
    have hdist :=
      dist_le_of_trajectories_ODE_of_mem (v := fun _ => v) (s := fun _ => U)
        (a := (t₀ : ℝ)) (b := tmax) (δ := 0)
        (fun _ _ => hv_lip)
        (hx_cont.mono (Set.Icc_subset_Icc_left t₀.2.1))
        (fun t ht => (hx_deriv t ⟨t₀.2.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨t₀.2.1.trans ht.1, ht.2⟩))
        (fun t ht => hx_mem t ⟨t₀.2.1.trans ht.1, ht.2.le⟩)
        (hy_cont.mono (Set.Icc_subset_Icc_left t₀.2.1))
        (fun t ht => (hy_deriv t ⟨t₀.2.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨t₀.2.1.trans ht.1, ht.2⟩))
        (fun t ht => hy_mem t ⟨t₀.2.1.trans ht.1, ht.2.le⟩)
        (by simp [hinit])
    intro t ht
    have h0 := hdist t ht
    rw [zero_mul] at h0
    exact dist_le_zero.mp h0
  have hbwd : ∀ t ∈ Set.Icc tmin (t₀ : ℝ), x t = y t := by
    let phi : ℝ → ℝ := fun s => 2 * (t₀ : ℝ) - s
    let g₁ : ℝ → E := x ∘ phi
    let g₂ : ℝ → E := y ∘ phi
    let T_rev : Set ℝ := Set.Icc (t₀ : ℝ) (2 * (t₀ : ℝ) - tmin)
    have hmaps : Set.MapsTo phi T_rev (Set.Icc tmin tmax) := by
      intro s hs
      exact ⟨by linarith [hs.2], by linarith [hs.1, t₀.2.2]⟩
    have hphi_cont : Continuous phi := by fun_prop
    have hphi_deriv : ∀ s : ℝ, HasDerivAt phi (-1) s := by
      intro s
      have h := (hasDerivAt_const s (2 * (t₀ : ℝ))).fun_sub (hasDerivAt_id s)
      rw [zero_sub] at h
      exact h
    have hv_neg_lip : LipschitzOnWith K (fun z : E => -v z) U := by
      intro a ha b hb
      dsimp only
      rw [edist_neg_neg]
      exact hv_lip ha hb
    have hcomp_deriv :
        ∀ (c : ℝ → E),
          (∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt c (v (c t)) (Set.Icc tmin tmax) t) →
          ∀ s ∈ Set.Ico (t₀ : ℝ) (2 * (t₀ : ℝ) - tmin),
            HasDerivWithinAt (c ∘ phi) (-v ((c ∘ phi) s)) (Set.Ici s) s := by
      intro c hc s hs
      have hs_Icc : s ∈ T_rev := Set.Ico_subset_Icc_self hs
      have hderiv_c : HasDerivWithinAt c (v (c (phi s))) (Set.Icc tmin tmax) (phi s) :=
        hc (phi s) (hmaps hs_Icc)
      have hcomp := hderiv_c.scomp s (hphi_deriv s).hasDerivWithinAt hmaps
      rw [neg_one_smul] at hcomp
      exact hcomp.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    have hdist :=
      dist_le_of_trajectories_ODE_of_mem (v := fun _ z => -v z) (s := fun _ => U)
        (a := (t₀ : ℝ)) (b := 2 * (t₀ : ℝ) - tmin) (δ := 0)
        (fun _ _ => hv_neg_lip)
        (hx_cont.comp hphi_cont.continuousOn hmaps)
        (hcomp_deriv x hx_deriv)
        (fun s hs => hx_mem (phi s) (hmaps (Set.Ico_subset_Icc_self hs)))
        (hy_cont.comp hphi_cont.continuousOn hmaps)
        (hcomp_deriv y hy_deriv)
        (fun s hs => hy_mem (phi s) (hmaps (Set.Ico_subset_Icc_self hs)))
        (by
          have hp0 : phi (t₀ : ℝ) = (t₀ : ℝ) := by dsimp [phi]; ring
          simp [hp0, hinit])
    intro t ht
    have hs_mem : 2 * (t₀ : ℝ) - t ∈ T_rev :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h0 := hdist (2 * (t₀ : ℝ) - t) hs_mem
    rw [zero_mul] at h0
    have heq := dist_le_zero.mp h0
    have hp_inv : phi (2 * (t₀ : ℝ) - t) = t := by dsimp [phi]; ring
    simpa [g₁, g₂, hp_inv] using heq
  intro t ht
  by_cases hle : (t₀ : ℝ) ≤ t
  · exact hfwd t ⟨hle, ht.2⟩
  · exact hbwd t ⟨ht.1, le_of_not_ge hle⟩

/-- Two-sided uniqueness of self-adjoint solutions on `[tmin, tmax]` inside a
Picard–Lindelöf ball via Grönwall's inequality. -/
theorem gibbsMetriplectic_trajectory_unique_on_Icc
    {n : ℕ} (H_eq σ : FiniteOperatorAlgebra n)
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax) (H₀ : SelfAdjointOp n) {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof (fun _ => gibbsMetriplecticFieldSA H_eq σ) t₀ H₀ a r L K)
    {H₁ H₂ : ℝ → SelfAdjointOp n}
    (hH₁_cont : ContinuousOn H₁ (Set.Icc tmin tmax))
    (hH₁_deriv : ∀ t ∈ Set.Icc tmin tmax,
      HasDerivWithinAt H₁ (gibbsMetriplecticFieldSA H_eq σ (H₁ t)) (Set.Icc tmin tmax) t)
    (hH₁_ball : ∀ t ∈ Set.Icc tmin tmax, H₁ t ∈ Metric.closedBall H₀ a)
    (hH₂_cont : ContinuousOn H₂ (Set.Icc tmin tmax))
    (hH₂_deriv : ∀ t ∈ Set.Icc tmin tmax,
      HasDerivWithinAt H₂ (gibbsMetriplecticFieldSA H_eq σ (H₂ t)) (Set.Icc tmin tmax) t)
    (hH₂_ball : ∀ t ∈ Set.Icc tmin tmax, H₂ t ∈ Metric.closedBall H₀ a)
    (hinit : H₁ t₀ = H₂ t₀) :
    ∀ t ∈ Set.Icc tmin tmax, H₁ t = H₂ t :=
  ode_unique_on_Icc_of_lipschitzOnWith (gibbsMetriplecticFieldSA H_eq σ) t₀
    (Metric.closedBall H₀ a) (hpl.lipschitzOnWith t₀ t₀.2)
    hH₁_cont hH₁_deriv hH₁_ball hH₂_cont hH₂_deriv hH₂_ball hinit

end PicardExistenceAndUniqueness

/-! ## Section 5: Unconditional End-to-End Metriplectic Second Law & Primal Density Flow -/

section UnconditionalSecondLaw

/-- **Unconditional internal ODE existence + trajectory-level Metriplectic Second Law
+ induced primal density flow**: given any self-adjoint stationary Hamiltonian `H_eq`,
target self-adjoint density `σ` commuting with `H_eq`, and initial self-adjoint `H₀`,
there exists a genuine differentiable trajectory `H` on `(t₀ - ε, t₀ + ε)` solving
the nonlinear Gibbs–BKM metriplectic ODE, satisfying monotone free-energy descent
`AntitoneOn`, strict dissipation off equilibrium (`normalizedExponential (H t) ≠ σ`),
and the induced Kubo–Mori / Heisenberg ODE on `ρ(t) = normalizedExponential (H t)`. -/
theorem exists_gibbsMetriplectic_trajectory_with_second_law
    {n : ℕ} [Nonempty (Fin n)]
    (H_eq σ : FiniteOperatorAlgebra n)
    (hH_eq : IsSelfAdjoint H_eq) (hσ : IsSelfAdjoint σ) (hcomm_σ : Commute σ H_eq)
    (H₀ : FiniteOperatorAlgebra n) (hH₀ : IsSelfAdjoint H₀) (t₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : ℝ → FiniteOperatorAlgebra n,
      H t₀ = H₀ ∧
      ∃ hSA : ∀ t, IsSelfAdjoint (H t),
        (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt H (gibbsMetriplecticFlow H_eq σ (H t) (hSA t)) t) ∧
        AntitoneOn (fun t => gibbsRelativePotential σ (H t)) (Set.Icc (t₀ - ε) (t₀ + ε)) ∧
        (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          normalizedExponential (H t) ≠ σ →
            deriv (fun s => gibbsRelativePotential σ (H s)) t < 0) ∧
        (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun s => normalizedExponential (H s))
            (gibbsUnitaryVectorField H_eq
                (faithfulGibbsDensity (H t) (hSA t)
                  (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hSA t))).rho -
              (faithfulGibbsDensity (H t) (hSA t)
                  (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hSA t))).kuboMoriTransform
                (centeredStatistic
                  (faithfulGibbsDensity (H t) (hSA t)
                    (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hSA t)))
                  ((faithfulGibbsDensity (H t) (hSA t)
                      (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hSA t))).kuboMoriTransform
                    ((faithfulGibbsDensity (H t) (hSA t)
                        (tracedExponential_re_pos_of_isSelfAdjoint (H t) (hSA t))).rho - σ)))) t) := by
  obtain ⟨ε, hε, H, hinit, hSA, hderiv_within, hderiv_open⟩ :=
    exists_gibbsMetriplectic_trajectory H_eq σ hH_eq hσ H₀ hH₀ t₀
  have hcont_H : ContinuousOn H (Set.Icc (t₀ - ε) (t₀ + ε)) := fun t ht =>
    (hderiv_within t ht).continuousWithinAt
  have hcont_Φ :
      ContinuousOn (fun t => gibbsRelativePotential σ (H t)) (Set.Icc (t₀ - ε) (t₀ + ε)) := by
    intro t ht
    have hΦ_cont :
        ContinuousAt (gibbsRelativePotential σ) (H t) :=
      (hasFDerivAt_gibbsRelativePotential_of_isSelfAdjoint σ (H t) (hSA t)).continuousAt
    exact hΦ_cont.comp_continuousWithinAt (hcont_H t ht)
  have hint_eq :
      interior (Set.Icc (t₀ - ε) (t₀ + ε)) = Set.Ioo (t₀ - ε) (t₀ + ε) :=
    interior_Icc
  have hanti :
      AntitoneOn (fun t => gibbsRelativePotential σ (H t)) (Set.Icc (t₀ - ε) (t₀ + ε)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (t₀ - ε) (t₀ + ε)) hcont_Φ
    · intro t ht
      rw [hint_eq] at ht
      exact (hasDerivAt_gibbsRelativePotential_metriplectic H_eq σ hσ hcomm_σ
        H (hSA t) (hderiv_open t ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [hint_eq] at ht
      exact deriv_gibbsRelativePotential_metriplectic_nonpos H_eq σ hσ hcomm_σ
        H (hSA t) (hderiv_open t ht)
  have hstrict :
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        normalizedExponential (H t) ≠ σ →
          deriv (fun s => gibbsRelativePotential σ (H s)) t < 0 := by
    intro t ht hne
    have hZ := tracedExponential_re_pos_of_isSelfAdjoint (H t) (hSA t)
    have hne_rho :
        (faithfulGibbsDensity (H t) (hSA t) hZ).rho ≠ σ := by
      rwa [faithfulGibbsDensity_rho_eq_normalizedExponential (H t) (hSA t) hZ]
    exact deriv_gibbsRelativePotential_metriplectic_neg_of_ne
      H_eq σ hσ hcomm_σ H (hSA t) (hderiv_open t ht) hne_rho
  exact ⟨ε, hε, H, hinit, hSA, hderiv_open, hanti, hstrict,
    fun t ht => hasDerivAt_normalizedExponential_gibbsMetriplecticFlow
      H_eq σ hH_eq hσ H (hSA t) (hderiv_open t ht)⟩

end UnconditionalSecondLaw

end InfoGeometry.Canonical.GibbsBKMMetriplecticPicardExistence
