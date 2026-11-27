/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Modular.ComplexMatrixTomitaDuality
import InfoGeometry.Canonical.TomitaModularAutomorphismFlow
import InfoGeometry.Modular.ConnesCocycle
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS

/-!
# Complex Matrix Modular Automorphism Flow & Gibbs Polar Realization (`F1a`)

This module constructs genuine Banach/C⋆ unitary modular automorphism flows on
`Matrix (Fin n) (Fin n) ℂ` from a Hermitian Hamiltonian `H : Matrix (Fin n) (Fin n) ℂ`,
connecting directly to the existing modular interfaces while preserving the generic
`matrixFunctionalTwisted` interface in `FilteredGNSMatrixAnalyticKMS` (whose
concrete finite-seed discharge lives in `FiniteSeedRepresentedAnalyticKMS.finiteSeedKMSState`):

1. **Unitary Exponential Group**:
   `uExp H t := NormedSpace.exp ((Complex.I * (t : ℂ)) • H)` is proved unitary
   (`(uExp H t)ᴴ = uExp H (-t)`) and homomorphic (`uExp H (s + t) = uExp H s * uExp H t`).
2. **Modular Flows & `ModularUnitaryGroup` on Hilbert–Schmidt `HSMatrix n`**:
   - Constructs `matrixModularFlow H hH : ConnesCocycle.ModularFlow ℂ (Matrix (Fin n) (Fin n) ℂ)`
     and `matrixOperatorFlow H hH : OperatorThermodynamics.OperatorFlow (Matrix (Fin n) (Fin n) ℂ)`.
   - Uses `HSMatrix n := EuclideanSpace ℂ (Fin n × Fin n)` with exact trace inner
     product identity `⟪hsOfMatrix n X, hsOfMatrix n Y⟫_ℂ = (Xᴴ * Y).trace` to
     inhabit `TomitaModularAutomorphismFlow.ModularUnitaryGroup (HSMatrix n)`.
3. **Constructive GNS Gibbs Vector State Invariance & KMS Cyclicity**:
   - Using the GNS cyclic-separating vector `Ω_H = exp((-1/2) • H)` (`hsGibbsVector`),
     proves `hsModularUnitaryIso H hH t Ω_H = Ω_H` and unconditional state invariance
     `⟪Ω_H, (U_t ∘ T ∘ U_{-t}) Ω_H⟫_ℂ = ⟪Ω_H, T Ω_H⟫_ℂ` for every bounded linear operator `T`,
     inhabiting `TomitaModularAutomorphismFlow.ModularInvariantState`.
   - Proves on `leftMulCLM A`: `⟪Ω_H, leftMulCLM A Ω_H⟫_ℂ = Tr(exp(-H) * A)` and exact
     KMS cyclicity `gibbsReadout H (A * (gibbsDensity H * B * gibbsDensityInv H)) = gibbsReadout H (B * A)`.
4. **OpenGauss T16 Witness**:
   - Explicit noncommuting `Matrix (Fin 2) (Fin 2) ℂ` witness.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar

open Matrix Complex
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

open InfoGeometry.Modular.ComplexMatrixTomitaDuality
open InfoGeometry.Modular.ConnesCocycle
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics
open InfoGeometry.Canonical.TomitaModularAutomorphismFlow

/-! =========================================================================
    1. OpenGauss T16 Noncommutativity Witness & Scalar Helpers
    ========================================================================= -/

/-- Closed T16 noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  InfoGeometry.Modular.ComplexMatrixTomitaDuality.mat2_complex_noncomm_witness

private lemma scalar_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  nlinarith [ha, hb, h]

private lemma scalar_neg_add_swap (s t : ℝ) : -(s + t) = -t + -s := by
  ring

private lemma scalar_neg_add_cancel_rev (t : ℝ) : -t + t = 0 := by
  ring

private lemma scalar_neg_half_add : (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) = (-1 : ℝ) := by
  norm_num

/-! =========================================================================
    2. Unitary One-Parameter Exponential Group uExp H t
    ========================================================================= -/

section UnitaryFlow

variable {n : ℕ}

/-- Unitary exponential `U(t) = exp(i t H)` on `M_n(ℂ)`. -/
def uExp (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • H)

/-- Gibbs unnormalized density `exp(-H)`, its square root `exp((-1/2)•H)`, and inverse `exp(H)`. -/
def gibbsDensity (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (-H)

def gibbsDensitySqrt (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((-(1 / 2 : ℝ)) • H)

def gibbsDensityInv (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp H

theorem uExp_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    uExp H 0 = 1 := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold uExp
  simp only [Complex.ofReal_zero, mul_zero, zero_smul, NormedSpace.exp_zero]

theorem uExp_add (H : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    uExp H (s + t) = uExp H s * uExp H t := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold uExp
  have hs : (Complex.I * ((s + t : ℝ) : ℂ)) • H =
      (Complex.I * (s : ℂ)) • H + (Complex.I * (t : ℝ)) • H := by
    rw [Complex.ofReal_add, mul_add, add_smul]
  rw [hs]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl H).smul_left (Complex.I * (s : ℂ))).smul_right (Complex.I * (t : ℂ)))

theorem uExp_conjTranspose (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (uExp H t)ᴴ = uExp H (-t) := by
  unfold uExp
  have hstar : star H = H := hH.eq
  have hexp : star (NormedSpace.exp ((Complex.I * (t : ℂ)) • H)) =
      NormedSpace.exp (star ((Complex.I * (t : ℂ)) • H)) :=
    NormedSpace.star_exp ((Complex.I * (t : ℂ)) • H)
  calc
    (NormedSpace.exp ((Complex.I * (t : ℂ)) • H))ᴴ
        = NormedSpace.exp (star ((Complex.I * (t : ℂ)) • H)) := hexp
    _ = NormedSpace.exp ((Complex.I * ((-t : ℝ) : ℂ)) • H) := by
      rw [star_smul, hstar, star_mul', Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, Complex.ofReal_neg, mul_neg, neg_mul]

theorem uExp_mul_conjTranspose (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    uExp H t * (uExp H t)ᴴ = 1 := by
  rw [uExp_conjTranspose H hH t, ← uExp_add, add_neg_cancel, uExp_zero]

theorem uExp_conjTranspose_mul (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (uExp H t)ᴴ * uExp H t = 1 := by
  rw [uExp_conjTranspose H hH t, ← uExp_add, neg_add_cancel, uExp_zero]

theorem gibbsDensitySqrt_herm (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    (gibbsDensitySqrt H)ᴴ = gibbsDensitySqrt H := by
  unfold gibbsDensitySqrt
  have hstar : star H = H := hH.eq
  have hexp : star (NormedSpace.exp ((-(1 / 2 : ℝ)) • H)) =
      NormedSpace.exp (star ((-(1 / 2 : ℝ)) • H)) :=
    NormedSpace.star_exp ((-(1 / 2 : ℝ)) • H)
  refine hexp.trans (congrArg NormedSpace.exp ?_)
  rw [star_smul, hstar, star_trivial]

theorem gibbsDensitySqrt_mul_self (H : Matrix (Fin n) (Fin n) ℂ) :
    gibbsDensitySqrt H * gibbsDensitySqrt H = gibbsDensity H := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold gibbsDensitySqrt gibbsDensity
  have hc : Commute ((-(1 / 2 : ℝ)) • H) ((-(1 / 2 : ℝ)) • H) :=
    ((Commute.refl H).smul_left _).smul_right _
  rw [← NormedSpace.exp_add_of_commute hc, ← add_smul, scalar_neg_half_add, neg_one_smul]

theorem gibbsDensitySqrt_commute_uExp (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Commute (gibbsDensitySqrt H) (uExp H t) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold gibbsDensitySqrt uExp Commute SemiconjBy
  have hreal : (-(1 / 2 : ℝ)) • H = ((-(1 / 2 : ℝ) : ℂ)) • H := by
    ext i j
    simp
  rw [hreal]
  have hc : Commute (((-(1 / 2 : ℝ) : ℂ)) • H) ((Complex.I * (t : ℂ)) • H) :=
    ((Commute.refl H).smul_left _).smul_right _
  rw [← NormedSpace.exp_add_of_commute hc, add_comm, ← NormedSpace.exp_add_of_commute hc.symm]

theorem gibbsDensity_mul_inv (H : Matrix (Fin n) (Fin n) ℂ) :
    gibbsDensity H * gibbsDensityInv H = 1 := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold gibbsDensity gibbsDensityInv
  rw [← NormedSpace.exp_add_of_commute (Commute.refl H).neg_left, neg_add_cancel,
    NormedSpace.exp_zero]

theorem gibbsDensityInv_mul (H : Matrix (Fin n) (Fin n) ℂ) :
    gibbsDensityInv H * gibbsDensity H = 1 := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold gibbsDensity gibbsDensityInv
  rw [← NormedSpace.exp_add_of_commute (Commute.refl H).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

theorem gibbsDensity_commute_uExp (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Commute (gibbsDensity H) (uExp H t) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold gibbsDensity uExp Commute SemiconjBy
  have hc : Commute (-H) ((Complex.I * (t : ℂ)) • H) :=
    ((Commute.refl H).neg_left).smul_right (Complex.I * (t : ℂ))
  rw [← NormedSpace.exp_add_of_commute hc, add_comm, ← NormedSpace.exp_add_of_commute hc.symm]

/-! =========================================================================
    3. Modular *-Automorphism Flow and OperatorFlow
    ========================================================================= -/

/-- Unitary-conjugation `*-automorphism` `σ_t^H(X) = U(t) X U(-t)` as a `StarAlgEquiv`. -/
def matrixModularStarAut (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := fun X => uExp H t * X * uExp H (-t)
  invFun := fun X => uExp H (-t) * X * uExp H t
  left_inv := fun X => by
    calc
      uExp H (-t) * (uExp H t * X * uExp H (-t)) * uExp H t
          = (uExp H (-t) * uExp H t) * X * (uExp H (-t) * uExp H t) := by
        simp only [Matrix.mul_assoc]
      _ = X := by
        rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.one_mul, Matrix.mul_one]
  right_inv := fun X => by
    calc
      uExp H t * (uExp H (-t) * X * uExp H t) * uExp H (-t)
          = (uExp H t * uExp H (-t)) * X * (uExp H t * uExp H (-t)) := by
        simp only [Matrix.mul_assoc]
      _ = X := by
        rw [← uExp_add, add_neg_cancel, uExp_zero, Matrix.one_mul, Matrix.mul_one]
  map_mul' := fun X Y => by
    calc
      uExp H t * (X * Y) * uExp H (-t)
          = uExp H t * X * 1 * Y * uExp H (-t) := by
        simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = uExp H t * X * (uExp H (-t) * uExp H t) * Y * uExp H (-t) := by
        rw [← uExp_add, neg_add_cancel, uExp_zero]
      _ = (uExp H t * X * uExp H (-t)) * (uExp H t * Y * uExp H (-t)) := by
        simp only [Matrix.mul_assoc]
  map_add' := fun X Y => by
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun c X => by
    change uExp H t * (c • X) * uExp H (-t) = c • (uExp H t * X * uExp H (-t))
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  map_star' := fun X => by
    change uExp H t * star X * uExp H (-t) = star (uExp H t * X * uExp H (-t))
    rw [star_mul, star_mul]
    change uExp H t * Xᴴ * uExp H (-t) = (uExp H (-t))ᴴ * (Xᴴ * (uExp H t)ᴴ)
    rw [uExp_conjTranspose H hH t, uExp_conjTranspose H hH (-t), neg_neg, Matrix.mul_assoc]

@[simp]
theorem matrixModularStarAut_apply (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModularStarAut H hH t X = uExp H t * X * uExp H (-t) := rfl

/-- Constructive `ConnesCocycle.ModularFlow` on `M_n(ℂ)` for any Hermitian `H`. -/
def matrixModularFlow (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ModularFlow ℂ (Matrix (Fin n) (Fin n) ℂ) where
  toFun := fun t => (matrixModularStarAut H hH t).toStarAlgHom
  map_zero := by
    ext X
    simp [uExp_zero]
  map_add := fun s t X => by
    change uExp H (s + t) * X * uExp H (-(s + t)) =
      uExp H s * (uExp H t * X * uExp H (-t)) * uExp H (-s)
    rw [uExp_add, scalar_neg_add_swap s t, uExp_add]
    simp only [Matrix.mul_assoc]

@[simp]
theorem matrixModularFlow_apply (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModularFlow H hH t X = uExp H t * X * uExp H (-t) := rfl

/-- Constructive `OperatorThermodynamics.OperatorFlow` on `M_n(ℂ)` for any Hermitian `H`. -/
def matrixOperatorFlow (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    OperatorFlow (Matrix (Fin n) (Fin n) ℂ) where
  flow := fun t => (matrixModularStarAut H hH t).toMulEquiv
  flow_zero := fun X => by
    change uExp H 0 * X * uExp H (-0) = X
    simp [uExp_zero]
  flow_add := fun s t X => (matrixModularFlow H hH).map_add s t X

@[simp]
theorem matrixOperatorFlow_apply (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (matrixOperatorFlow H hH).flow t X = uExp H t * X * uExp H (-t) := rfl

/-! =========================================================================
    4. Hilbert–Schmidt Inner-Product Carrier, ModularUnitaryGroup & Gibbs Invariance
    ========================================================================= -/

variable (n)

/-- Complex Hilbert–Schmidt inner-product space on `M_n(ℂ)` realized over
`EuclideanSpace ℂ (Fin n × Fin n)`. -/
abbrev HSMatrix : Type := EuclideanSpace ℂ (Fin n × Fin n)

/-- Canonical `ℂ`-linear isomorphism from `M_n(ℂ)` to `HSMatrix n`. -/
def hsOfMatrix : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] HSMatrix n where
  toFun := fun X => WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun := fun v => Matrix.of (fun i j => v (i, j))
  left_inv := fun X => by ext i j; rfl
  right_inv := fun v => by ext ⟨i, j⟩; rfl
  map_add' := fun X Y => by ext ⟨i, j⟩; rfl
  map_smul' := fun c X => by ext ⟨i, j⟩; rfl

/-- Exact complex Hilbert–Schmidt inner product identity
`⟪hsOfMatrix n X, hsOfMatrix n Y⟫_ℂ = Tr(Xᴴ * Y)`. -/
theorem hsOfMatrix_inner (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℂ (hsOfMatrix n X) (hsOfMatrix n Y) = hsInner n X Y := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  unfold hsInner Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change inner ℂ (X i j) (Y i j) = Xᴴ j i * Y i j
  rw [RCLike.inner_apply', Matrix.conjTranspose_apply]
  rfl

variable {n}

/-- Unitary operator `U(t) : HSMatrix n ≃ₗᵢ[ℂ] HSMatrix n` implementing `X ↦ uExp t * X * uExp (-t)`. -/
def hsModularUnitaryIso (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    HSMatrix n ≃ₗᵢ[ℂ] HSMatrix n :=
  { (hsOfMatrix n).symm.trans
      ((matrixModularStarAut H hH t).toAlgEquiv.toLinearEquiv.trans (hsOfMatrix n)) with
    norm_map' := fun v => by
      let X : Matrix (Fin n) (Fin n) ℂ := (hsOfMatrix n).symm v
      have hv : v = hsOfMatrix n X := ((hsOfMatrix n).apply_symm_apply v).symm
      have hmap :
          ((hsOfMatrix n).symm.trans
            ((matrixModularStarAut H hH t).toAlgEquiv.toLinearEquiv.trans (hsOfMatrix n))) v =
            hsOfMatrix n (uExp H t * X * uExp H (-t)) := rfl
      rw [hmap]
      have hinner :
          inner ℂ (hsOfMatrix n (uExp H t * X * uExp H (-t)))
            (hsOfMatrix n (uExp H t * X * uExp H (-t))) =
            inner ℂ v v := by
        rw [hv, hsOfMatrix_inner, hsOfMatrix_inner]
        unfold hsInner
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, uExp_conjTranspose H hH t,
          uExp_conjTranspose H hH (-t), neg_neg]
        calc
          (uExp H t * (Xᴴ * uExp H (-t)) * (uExp H t * X * uExp H (-t))).trace
              = (uExp H t * Xᴴ * (uExp H (-t) * uExp H t) * X * uExp H (-t)).trace := by
            simp only [Matrix.mul_assoc]
          _ = (uExp H t * (Xᴴ * X) * uExp H (-t)).trace := by
            rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
          _ = (uExp H (-t) * (uExp H t * (Xᴴ * X))).trace := Matrix.trace_mul_comm _ _
          _ = (Xᴴ * X).trace := by
            rw [← Matrix.mul_assoc, ← uExp_add, neg_add_cancel, uExp_zero, Matrix.one_mul]
      have hn : ‖hsOfMatrix n (uExp H t * X * uExp H (-t))‖ ^ 2 = ‖v‖ ^ 2 := by
        have hre : RCLike.re (inner ℂ (hsOfMatrix n (uExp H t * X * uExp H (-t)))
            (hsOfMatrix n (uExp H t * X * uExp H (-t)))) = RCLike.re (inner ℂ v v) :=
          congrArg Complex.re hinner
        rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at hre
      exact scalar_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) hn }

theorem hsModularUnitaryIso_hsOfMatrix (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    hsModularUnitaryIso H hH t (hsOfMatrix n X) = hsOfMatrix n (uExp H t * X * uExp H (-t)) := by
  ext ⟨i, j⟩
  rfl

/-- Genuine inhabitant of `TomitaModularAutomorphismFlow.ModularUnitaryGroup (HSMatrix n)`. -/
def matrixModularUnitaryGroup (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ModularUnitaryGroup (HSMatrix n) where
  U := hsModularUnitaryIso H hH
  map_zero := by
    ext v ⟨i, j⟩
    have hv : ((hsModularUnitaryIso H hH 0) v).ofLp (i, j) =
        (uExp H 0 * (hsOfMatrix n).symm v * uExp H (-0)) i j := rfl
    rw [hv, neg_zero, uExp_zero, Matrix.one_mul, Matrix.mul_one]
    rfl
  map_add := fun t1 t2 => by
    ext v ⟨i, j⟩
    have hL : ((hsModularUnitaryIso H hH (t1 + t2)) v).ofLp (i, j) =
        (uExp H (t1 + t2) * (hsOfMatrix n).symm v * uExp H (-(t1 + t2))) i j := rfl
    have hR : (((hsModularUnitaryIso H hH t2).trans (hsModularUnitaryIso H hH t1)) v).ofLp (i, j) =
        (uExp H t1 * (uExp H t2 * (hsOfMatrix n).symm v * uExp H (-t2)) * uExp H (-t1)) i j :=
      rfl
    rw [hL, hR, uExp_add, scalar_neg_add_swap t1 t2, uExp_add]
    simp only [Matrix.mul_assoc]
  inv_cancel := fun t v => by
    obtain ⟨X, rfl⟩ := (hsOfMatrix n).surjective v
    rw [hsModularUnitaryIso_hsOfMatrix, hsModularUnitaryIso_hsOfMatrix, neg_neg]
    congr 1
    calc
      uExp H (-t) * (uExp H t * X * uExp H (-t)) * uExp H t
          = (uExp H (-t) * uExp H t) * X * (uExp H (-t) * uExp H t) := by
        simp only [Matrix.mul_assoc]
      _ = X := by
        rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.one_mul, Matrix.mul_one]

/-- Unnormalized Gibbs functional `ω_H(A) = Tr(exp(-H) * A)` on `M_n(ℂ)`. -/
def gibbsReadout (H : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (gibbsDensity H * A).trace

/-- GNS cyclic-separating Gibbs vector `Ω_H = exp((-1/2) • H)` inside `HSMatrix n`. -/
def hsGibbsVector (H : Matrix (Fin n) (Fin n) ℂ) : HSMatrix n :=
  hsOfMatrix n (gibbsDensitySqrt H)

/-- The modular unitary flow fixes the GNS Gibbs vector: `U(t)(Ω_H) = Ω_H`. -/
theorem hsModularUnitaryIso_gibbsVector (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    hsModularUnitaryIso H hH t (hsGibbsVector H) = hsGibbsVector H := by
  unfold hsGibbsVector
  rw [hsModularUnitaryIso_hsOfMatrix, ← (gibbsDensitySqrt_commute_uExp H t).eq,
    Matrix.mul_assoc, ← uExp_add, add_neg_cancel, uExp_zero, Matrix.mul_one]

/-- Left regular multiplication as a bounded operator on `HSMatrix n`. -/
def leftMulCLM (A : Matrix (Fin n) (Fin n) ℂ) : HSMatrix n →L[ℂ] HSMatrix n :=
  ((hsOfMatrix n).toLinearMap.comp
    (({ toFun := fun X => A * X
        map_add' := fun X Y => Matrix.mul_add A X Y
        map_smul' := fun c X => Algebra.mul_smul_comm c A X } :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ).comp
      (hsOfMatrix n).symm.toLinearMap)).toContinuousLinearMap

/-- GNS vector expectation `ω_{Ω_H}(T) = ⟪Ω_H, T Ω_H⟫_ℂ` on `HSMatrix n →L[ℂ] HSMatrix n`. -/
def hsGibbsOpReadout (H : Matrix (Fin n) (Fin n) ℂ) (T : HSMatrix n →L[ℂ] HSMatrix n) : ℂ :=
  inner ℂ (hsGibbsVector H) (T (hsGibbsVector H))

/-- On left-regular operators `leftMulCLM A`, the GNS vector readout equals `Tr(exp(-H) * A)`. -/
theorem hsGibbsOpReadout_leftMulCLM (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    hsGibbsOpReadout H (leftMulCLM A) = gibbsReadout H A := by
  unfold hsGibbsOpReadout hsGibbsVector leftMulCLM gibbsReadout
  change inner ℂ (hsOfMatrix n (gibbsDensitySqrt H))
    (hsOfMatrix n (A * gibbsDensitySqrt H)) = (gibbsDensity H * A).trace
  rw [hsOfMatrix_inner]
  unfold hsInner
  rw [gibbsDensitySqrt_herm H hH, Matrix.trace_mul_comm, Matrix.mul_assoc,
    gibbsDensitySqrt_mul_self, Matrix.trace_mul_comm]

theorem hsModularUnitaryIso_adjoint_apply (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) (u v : HSMatrix n) :
    inner ℂ u (hsModularUnitaryIso H hH t v) =
      inner ℂ (hsModularUnitaryIso H hH (-t) u) v := by
  let U : Matrix (Fin n) (Fin n) ℂ := (hsOfMatrix n).symm u
  let V : Matrix (Fin n) (Fin n) ℂ := (hsOfMatrix n).symm v
  have hu : u = hsOfMatrix n U := ((hsOfMatrix n).apply_symm_apply u).symm
  have hv : v = hsOfMatrix n V := ((hsOfMatrix n).apply_symm_apply v).symm
  have h1 : hsModularUnitaryIso H hH t (hsOfMatrix n V) =
      hsOfMatrix n (uExp H t * V * uExp H (-t)) :=
    hsModularUnitaryIso_hsOfMatrix H hH t V
  have h2 : hsModularUnitaryIso H hH (-t) (hsOfMatrix n U) =
      hsOfMatrix n (uExp H (-t) * U * uExp H t) := by
    rw [hsModularUnitaryIso_hsOfMatrix, neg_neg]
  rw [hu, hv, h1, h2, hsOfMatrix_inner, hsOfMatrix_inner]
  unfold hsInner
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, uExp_conjTranspose H hH (-t),
    uExp_conjTranspose H hH t, neg_neg]
  calc
    (Uᴴ * (uExp H t * V * uExp H (-t))).trace
        = ((Uᴴ * uExp H t * V) * uExp H (-t)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (uExp H (-t) * (Uᴴ * uExp H t * V)).trace := Matrix.trace_mul_comm _ _
    _ = ((uExp H (-t) * (Uᴴ * uExp H t)) * V).trace := by
      simp only [Matrix.mul_assoc]

/-- Unconditional GNS invariance of `hsGibbsOpReadout` for every `T : HSMatrix n →L[ℂ] HSMatrix n`. -/
theorem hsGibbsOpReadout_modularFlow_invariant (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) (T : HSMatrix n →L[ℂ] HSMatrix n) :
    hsGibbsOpReadout H (modularFlow (matrixModularUnitaryGroup H hH) t T) =
      hsGibbsOpReadout H T := by
  unfold hsGibbsOpReadout modularFlow
  change inner ℂ (hsGibbsVector H)
    (hsModularUnitaryIso H hH t (T (hsModularUnitaryIso H hH (-t) (hsGibbsVector H)))) =
      inner ℂ (hsGibbsVector H) (T (hsGibbsVector H))
  rw [hsModularUnitaryIso_gibbsVector H hH (-t),
    hsModularUnitaryIso_adjoint_apply H hH t,
    hsModularUnitaryIso_gibbsVector H hH (-t)]

theorem gibbsReadout_modularFlow_invariant (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    gibbsReadout H (matrixModularFlow H hH t A) = gibbsReadout H A := by
  unfold gibbsReadout
  rw [matrixModularFlow_apply]
  calc
    (gibbsDensity H * (uExp H t * A * uExp H (-t))).trace
        = ((gibbsDensity H * uExp H t * A) * uExp H (-t)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (uExp H (-t) * (gibbsDensity H * uExp H t * A)).trace := Matrix.trace_mul_comm _ _
    _ = (uExp H (-t) * (uExp H t * gibbsDensity H * A)).trace := by
      rw [(gibbsDensity_commute_uExp H t).eq]
    _ = ((uExp H (-t) * uExp H t) * gibbsDensity H * A).trace := by
      simp only [Matrix.mul_assoc]
    _ = (gibbsDensity H * A).trace := by
      rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.one_mul]

/-- Exact algebraic KMS identity for `gibbsReadout`:
`ω_H(A · (exp(-H) B exp(H))) = ω_H(B · A)`. -/
theorem gibbsReadout_kms_identity (H : Matrix (Fin n) (Fin n) ℂ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    gibbsReadout H (A * (gibbsDensity H * B * gibbsDensityInv H)) =
      gibbsReadout H (B * A) := by
  unfold gibbsReadout
  calc
    (gibbsDensity H * (A * (gibbsDensity H * B * gibbsDensityInv H))).trace
        = ((gibbsDensity H * A * gibbsDensity H * B) * gibbsDensityInv H).trace := by
      simp only [Matrix.mul_assoc]
    _ = (gibbsDensityInv H * (gibbsDensity H * A * gibbsDensity H * B)).trace :=
      Matrix.trace_mul_comm _ _
    _ = ((gibbsDensityInv H * gibbsDensity H) * A * gibbsDensity H * B).trace := by
      simp only [Matrix.mul_assoc]
    _ = (A * (gibbsDensity H * B)).trace := by
      rw [gibbsDensityInv_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = (gibbsDensity H * (B * A)).trace := by
      rw [Matrix.trace_mul_comm A (gibbsDensity H * B), Matrix.mul_assoc]

/-- Genuine inhabitant of `TomitaModularAutomorphismFlow.ModularInvariantState` on `HSMatrix n`. -/
def matrixGibbsModularInvariantState (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) :
    ModularInvariantState (matrixModularUnitaryGroup H hH) where
  omega := hsGibbsOpReadout H
  invariant := hsGibbsOpReadout_modularFlow_invariant H hH

/-- Re-export pointer to the existing concrete finite-seed colimit analytic-KMS
specialization (`FiniteSeedRepresentedAnalyticKMS.finiteSeedKMSState`), which
discharges `FilteredGNSMatrixAnalyticKMS.matrixFunctionalTwisted` on the represented
UHF Gibbs carrier without altering any generic compatible-state-family hypotheses. -/
def concreteFiniteSeedKMSBridge {k : ℕ} (H : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (hH : H.IsHermitian) (β : ℝ) (hβ : 0 < β) (v : ℕ) :=
  InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS.finiteSeedKMSState H hH β hβ v

end UnitaryFlow

end InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar
