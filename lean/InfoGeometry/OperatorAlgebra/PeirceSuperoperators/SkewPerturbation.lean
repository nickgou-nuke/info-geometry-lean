/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.DoubleCommutator

/-!
# An imaginary Gram inner action preserves the double-commutator kernel

On the full complex matrix Hilbert–Schmidt space, the inner action of
`NNᴴ + NᴴN` is self-adjoint. Its imaginary multiple contributes zero real
energy. Adding this term to the negative paired double commutator preserves
the joint commutant kernel, without a nilpotence assumption.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open Matrix
open scoped ComplexOrder

attribute [local instance] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance : InnerProductSpace ℂ (Matrix n n ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local notation "adM" => LieAlgebra.ad ℂ (Matrix n n ℂ)

/-- The inner action of the two-sided matrix Gram sum is self-adjoint. -/
theorem hs_adjoint_ad_gram (N : Matrix n n ℂ) :
    (adM (N * Nᴴ + Nᴴ * N)).adjoint = adM (N * Nᴴ + Nᴴ * N) := by
  rw [hs_adjoint_ad]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- Multiplication by the imaginary unit makes the Gram inner action have zero real energy. -/
theorem imaginary_gram_ad_energy_eq_zero (N X : Matrix n n ℂ) :
    RCLike.re (inner ℂ X ((Complex.I • adM (N * Nᴴ + Nᴴ * N)) X)) = 0 := by
  have hs : (adM (N * Nᴴ + Nᴴ * N)).IsSymmetric :=
    (LinearMap.eq_adjoint_iff _ _).mp (hs_adjoint_ad_gram N).symm
  have him : (inner ℂ X (adM (N * Nᴴ + Nᴴ * N) X)).im = 0 :=
    hs.im_inner_self_apply X
  rw [LinearMap.smul_apply, inner_smul_right]
  change (Complex.I * inner ℂ X (adM (N * Nᴴ + Nᴴ * N) X)).re = 0
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, him]
  simp only [zero_mul, mul_zero, sub_zero]

/-- The imaginary Gram perturbation preserves the exact double-commutator energy. -/
theorem skewPerturbation_energy (N X : Matrix n n ℂ) :
    RCLike.re (inner ℂ X
      ((Complex.I • adM (N * Nᴴ + Nᴴ * N) -
        (adM N * adM Nᴴ + adM Nᴴ * adM N)) X)) =
          -(‖⁅N, X⁆‖ ^ 2 + ‖⁅Nᴴ, X⁆‖ ^ 2) := by
  rw [sub_eq_add_neg, LinearMap.add_apply, inner_add_right, map_add,
    imaginary_gram_ad_energy_eq_zero, zero_add, doubleCommutator_energy]

/-- The perturbed and unperturbed actions have the same zero vectors. -/
theorem skewPerturbation_apply_eq_zero_iff (N X : Matrix n n ℂ) :
    (Complex.I • adM (N * Nᴴ + Nᴴ * N) -
      (adM N * adM Nᴴ + adM Nᴴ * adM N)) X = 0 ↔
        (-(adM N * adM Nᴴ + adM Nᴴ * adM N)) X = 0 := by
  constructor
  · intro hX
    have hE := skewPerturbation_energy N X
    rw [hX, inner_zero_right, map_zero] at hE
    have hN : 0 ≤ ‖⁅N, X⁆‖ ^ 2 := sq_nonneg _
    have hNH : 0 ≤ ‖⁅Nᴴ, X⁆‖ ^ 2 := sq_nonneg _
    have hzN : ‖⁅N, X⁆‖ ^ 2 = 0 := by linarith only [hE, hN, hNH]
    have hzNH : ‖⁅Nᴴ, X⁆‖ ^ 2 = 0 := by linarith only [hE, hN, hNH]
    apply (doubleCommutator_apply_eq_zero_iff N X).mpr
    simpa only [sq_eq_zero_iff, norm_eq_zero] using And.intro hzN hzNH
  · intro hD
    obtain ⟨hN, hNH⟩ := (doubleCommutator_apply_eq_zero_iff N X).mp hD
    have hNX : Commute N X := by
      change N * X - X * N = 0 at hN
      exact sub_eq_zero.mp hN
    have hNHX : Commute Nᴴ X := by
      change Nᴴ * X - X * Nᴴ = 0 at hNH
      exact sub_eq_zero.mp hNH
    have hHX : Commute (N * Nᴴ + Nᴴ * N) X :=
      (hNX.mul_left hNHX).add_left (hNHX.mul_left hNX)
    have hH : adM (N * Nᴴ + Nᴴ * N) X = 0 := by
      change (N * Nᴴ + Nᴴ * N) * X - X * (N * Nᴴ + Nᴴ * N) = 0
      exact sub_eq_zero.mpr hHX.eq
    rw [sub_eq_add_neg, LinearMap.add_apply, LinearMap.smul_apply, hH, smul_zero, hD,
      zero_add]

/-- Kernel preservation as an equality of native complex submodules. -/
theorem skewPerturbation_ker_eq_doubleCommutator (N : Matrix n n ℂ) :
    (Complex.I • adM (N * Nᴴ + Nᴴ * N) -
      (adM N * adM Nᴴ + adM Nᴴ * adM N)).ker =
        (-(adM N * adM Nᴴ + adM Nᴴ * adM N)).ker := by
  apply Submodule.ext
  intro X
  simpa only [LinearMap.mem_ker] using skewPerturbation_apply_eq_zero_iff N X

/-- The skew perturbation has precisely the simultaneous inner-action kernel. -/
theorem skewPerturbation_ker (N : Matrix n n ℂ) :
    (Complex.I • adM (N * Nᴴ + Nᴴ * N) -
      (adM N * adM Nᴴ + adM Nᴴ * adM N)).ker =
        (adM N).ker ⊓ (adM Nᴴ).ker := by
  rw [skewPerturbation_ker_eq_doubleCommutator, doubleCommutator_ker]

/-- The corrected perturbed action has the same native joint centralizer. -/
theorem skewPerturbation_ker_eq_centralizer (N : Matrix n n ℂ) :
    (Complex.I • adM (N * Nᴴ + Nᴴ * N) -
      (adM N * adM Nᴴ + adM Nᴴ * adM N)).ker =
        (Subalgebra.centralizer ℂ ({N, Nᴴ} : Set (Matrix n n ℂ))).toSubmodule := by
  rw [skewPerturbation_ker_eq_doubleCommutator, doubleCommutator_ker_eq_centralizer]

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
