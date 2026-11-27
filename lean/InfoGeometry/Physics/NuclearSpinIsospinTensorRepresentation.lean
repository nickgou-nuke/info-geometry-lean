/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralTensorRecoupling
import InfoGeometry.External.Auto.WeakIsospinSU2
import InfoGeometry.Physics.NuclearSymmetrySectors

/-!
# Tensor-product spin/isospin representation

The two physical degree-zero sectors act on separate tensor factors.  This is
the concrete finite representation layer; the abstract five-grading remains a
separate transition algebra.
-/

namespace InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation

open Algebra.TensorProduct
open TensorProduct
open ChiralTensorRecoupling
open InfoGeometry.Physics.ChiralCausalCone
open WeakIsospinSU2
open InfoGeometry.Physics.NuclearSymmetrySectors

noncomputable section

def spinAction (A : M2C) : SpinPair := A ⊗ₜ[ℂ] (1 : M2C)

def isospinAction (B : M2C) : SpinPair := (1 : M2C) ⊗ₜ[ℂ] B

/-! ## Isoscalar/isovector operator coordinates

For a proton/neutron-labelled pair of operators `(p, n)`, these are the
canonical half-sum and half-difference coordinates.  The reconstruction
lemmas below are purely identities in the finite `SpinPair` carrier; they do
not identify this algebraic decomposition with an empirical nuclear model.
-/

def isoscalarComponent (p n : SpinPair) : SpinPair :=
  (1 / 2 : ℂ) • (p + n)

def isovectorComponent (p n : SpinPair) : SpinPair :=
  (1 / 2 : ℂ) • (p - n)

theorem isoscalar_add_isovector (p n : SpinPair) :
    isoscalarComponent p n + isovectorComponent p n = p := by
  unfold isoscalarComponent isovectorComponent
  module

theorem isoscalar_sub_isovector (p n : SpinPair) :
    isoscalarComponent p n - isovectorComponent p n = n := by
  unfold isoscalarComponent isovectorComponent
  module

theorem isoscalarComponent_swap (p n : SpinPair) :
    isoscalarComponent n p = isoscalarComponent p n := by
  unfold isoscalarComponent
  congr 1
  abel

theorem isovectorComponent_swap (p n : SpinPair) :
    isovectorComponent n p = -isovectorComponent p n := by
  unfold isovectorComponent
  module

/-- The noncommutative obstruction in isoscalar/isovector coordinates.
The half-sum/half-difference commutator is exactly minus one half of the
proton/neutron commutator. -/
theorem isoscalar_isovector_commutator (p n : SpinPair) :
    isoscalarComponent p n * isovectorComponent p n -
        isovectorComponent p n * isoscalarComponent p n =
      (-1 / 2 : ℂ) • (p * n - n * p) := by
  unfold isoscalarComponent isovectorComponent
  rw [smul_mul_smul, smul_mul_smul]
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  module

/-- The isoscalar and isovector components commute exactly when the original
proton/neutron operators commute. -/
theorem isoscalar_isovector_commute_iff (p n : SpinPair) :
    isoscalarComponent p n * isovectorComponent p n =
        isovectorComponent p n * isoscalarComponent p n ↔
      p * n = n * p := by
  constructor
  · intro h
    have hzero : isoscalarComponent p n * isovectorComponent p n -
        isovectorComponent p n * isoscalarComponent p n = 0 :=
      sub_eq_zero.mpr h
    rw [isoscalar_isovector_commutator] at hzero
    have hsub : p * n - n * p = 0 := by
      exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact sub_eq_zero.mp hsub
  · intro h
    apply sub_eq_zero.mp
    rw [isoscalar_isovector_commutator, sub_eq_zero.mpr h, smul_zero]

/-! The two physical Cartan/chirality readouts.  They are kept distinct from
the generic circular involution API: no circular axis is selected here. -/

def spinChirality : SpinPair := spinAction σ3c

def isospinChirality : SpinPair := isospinAction σ3c

theorem spinChirality_sq :
    spinChirality * spinChirality = (1 : SpinPair) := by
  unfold spinChirality spinAction
  rw [tmul_mul_tmul, σ3c_sq]
  simp [Algebra.TensorProduct.one_def]

theorem isospinChirality_sq :
    isospinChirality * isospinChirality = (1 : SpinPair) := by
  unfold isospinChirality isospinAction
  rw [tmul_mul_tmul, σ3c_sq]
  simp [Algebra.TensorProduct.one_def]

theorem spinChirality_isospinChirality_commute :
    spinChirality * isospinChirality =
      isospinChirality * spinChirality := by
  unfold spinChirality isospinChirality spinAction isospinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  simp

/-! Independent `ℤ₂` twists for the two physical tensor factors. -/

def spinTwist (x : SpinPair) : SpinPair :=
  spinChirality * x * spinChirality

def isospinTwist (x : SpinPair) : SpinPair :=
  isospinChirality * x * isospinChirality

theorem spinTwist_involutive (x : SpinPair) :
    spinTwist (spinTwist x) = x := by
  unfold spinTwist
  calc
    spinChirality * (spinChirality * x * spinChirality) * spinChirality =
        (spinChirality * spinChirality) * x *
          (spinChirality * spinChirality) := by noncomm_ring
    _ = x := by rw [spinChirality_sq]; simp

theorem isospinTwist_involutive (x : SpinPair) :
    isospinTwist (isospinTwist x) = x := by
  unfold isospinTwist
  calc
    isospinChirality * (isospinChirality * x * isospinChirality) *
        isospinChirality =
      (isospinChirality * isospinChirality) * x *
        (isospinChirality * isospinChirality) := by noncomm_ring
    _ = x := by rw [isospinChirality_sq]; simp

theorem spinTwist_isospinTwist_commute (x : SpinPair) :
    spinTwist (isospinTwist x) =
      isospinTwist (spinTwist x) := by
  unfold spinTwist isospinTwist
  have hcomm := spinChirality_isospinChirality_commute
  calc
    spinChirality * (isospinChirality * x * isospinChirality) *
        spinChirality =
      (spinChirality * isospinChirality) * x *
        (isospinChirality * spinChirality) := by noncomm_ring
    _ = (isospinChirality * spinChirality) * x *
        (spinChirality * isospinChirality) := by rw [hcomm]
    _ = isospinChirality * (spinChirality * x * spinChirality) *
        isospinChirality := by noncomm_ring

theorem spin_isospin_actions_commute (A B : M2C) :
    spinAction A * isospinAction B =
      isospinAction B * spinAction A := by
  unfold spinAction isospinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  simp

theorem spin_action_preserves_commutator (A B : M2C) :
    spinAction A * spinAction B - spinAction B * spinAction A =
      (A * B - B * A) ⊗ₜ[ℂ] (1 : M2C) := by
  unfold spinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  rw [← TensorProduct.sub_tmul]
  simp

theorem isospin_action_preserves_commutator (A B : M2C) :
    isospinAction A * isospinAction B - isospinAction B * isospinAction A =
      (1 : M2C) ⊗ₜ[ℂ] (A * B - B * A) := by
  unfold isospinAction
  rw [tmul_mul_tmul, tmul_mul_tmul]
  rw [← TensorProduct.tmul_sub]
  simp

theorem spin_action_preserves_square (A : M2C) (hA : A * A = 1) :
    spinAction A * spinAction A = (1 : SpinPair) := by
  unfold spinAction
  rw [tmul_mul_tmul, hA]
  simp [Algebra.TensorProduct.one_def]

theorem isospin_action_preserves_square (A : M2C) (hA : A * A = 1) :
    isospinAction A * isospinAction A = (1 : SpinPair) := by
  unfold isospinAction
  rw [tmul_mul_tmul, hA]
  simp [Algebra.TensorProduct.one_def]

theorem pauli_spin_squares :
    spinAction I₁ * spinAction I₁ = (1 : SpinPair) ∧
      spinAction I₂ * spinAction I₂ = (1 : SpinPair) ∧
      spinAction I₃ * spinAction I₃ = (1 : SpinPair) := by
  exact ⟨spin_action_preserves_square I₁ I₁_sq,
    spin_action_preserves_square I₂ I₂_sq,
    spin_action_preserves_square I₃ I₃_sq⟩

theorem pauli_isospin_squares :
    isospinAction I₁ * isospinAction I₁ = (1 : SpinPair) ∧
      isospinAction I₂ * isospinAction I₂ = (1 : SpinPair) ∧
      isospinAction I₃ * isospinAction I₃ = (1 : SpinPair) := by
  exact ⟨isospin_action_preserves_square I₁ I₁_sq,
    isospin_action_preserves_square I₂ I₂_sq,
    isospin_action_preserves_square I₃ I₃_sq⟩

theorem pauli_spin_comm_I₁_I₂ :
    spinAction I₁ * spinAction I₂ - spinAction I₂ * spinAction I₁ =
      (2 * Complex.I) • spinAction I₃ := by
  rw [spin_action_preserves_commutator, I₁_comm_I₂]
  simp [spinAction, TensorProduct.smul_tmul]

theorem pauli_isospin_comm_I₁_I₂ :
    isospinAction I₁ * isospinAction I₂ -
        isospinAction I₂ * isospinAction I₁ =
      (2 * Complex.I) • isospinAction I₃ := by
  rw [isospin_action_preserves_commutator, I₁_comm_I₂]
  simp [isospinAction]

theorem pauli_spin_comm_I₂_I₃ :
    spinAction I₂ * spinAction I₃ - spinAction I₃ * spinAction I₂ =
      (2 * Complex.I) • spinAction I₁ := by
  rw [spin_action_preserves_commutator, I₂_comm_I₃]
  simp [spinAction, TensorProduct.smul_tmul]

theorem pauli_spin_comm_I₃_I₁ :
    spinAction I₃ * spinAction I₁ - spinAction I₁ * spinAction I₃ =
      (2 * Complex.I) • spinAction I₂ := by
  rw [spin_action_preserves_commutator, I₃_comm_I₁]
  simp [spinAction, TensorProduct.smul_tmul]

theorem pauli_isospin_comm_I₂_I₃ :
    isospinAction I₂ * isospinAction I₃ -
        isospinAction I₃ * isospinAction I₂ =
      (2 * Complex.I) • isospinAction I₁ := by
  rw [isospin_action_preserves_commutator, I₂_comm_I₃]
  simp [isospinAction]

theorem pauli_isospin_comm_I₃_I₁ :
    isospinAction I₃ * isospinAction I₁ -
        isospinAction I₁ * isospinAction I₃ =
      (2 * Complex.I) • isospinAction I₂ := by
  rw [isospin_action_preserves_commutator, I₃_comm_I₁]
  simp [isospinAction]

/-- Spin/isospin generators with the same `σ/2` normalization used by
`NuclearWignerSupermultipletSymmetry.isospin_casimir`. -/
def spinGen1 : SpinPair := (1 / 2 : ℂ) • spinAction I₁
def spinGen2 : SpinPair := (1 / 2 : ℂ) • spinAction I₂
def spinGen3 : SpinPair := (1 / 2 : ℂ) • spinAction I₃

def isospinGen1 : SpinPair := (1 / 2 : ℂ) • isospinAction I₁
def isospinGen2 : SpinPair := (1 / 2 : ℂ) • isospinAction I₂
def isospinGen3 : SpinPair := (1 / 2 : ℂ) • isospinAction I₃

theorem spinGen1_sq : spinGen1 * spinGen1 = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold spinGen1
  rw [smul_mul_smul, spin_action_preserves_square I₁ I₁_sq]
  norm_num

theorem spinGen2_sq : spinGen2 * spinGen2 = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold spinGen2
  rw [smul_mul_smul, spin_action_preserves_square I₂ I₂_sq]
  norm_num

theorem spinGen3_sq : spinGen3 * spinGen3 = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold spinGen3
  rw [smul_mul_smul, spin_action_preserves_square I₃ I₃_sq]
  norm_num

theorem isospinGen1_sq : isospinGen1 * isospinGen1 = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold isospinGen1
  rw [smul_mul_smul, isospin_action_preserves_square I₁ I₁_sq]
  norm_num

theorem isospinGen2_sq : isospinGen2 * isospinGen2 = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold isospinGen2
  rw [smul_mul_smul, isospin_action_preserves_square I₂ I₂_sq]
  norm_num

theorem isospinGen3_sq : isospinGen3 * isospinGen3 = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold isospinGen3
  rw [smul_mul_smul, isospin_action_preserves_square I₃ I₃_sq]
  norm_num

/-- The spin factor Casimir is `3/4`, the same value as the isospin factor. -/
theorem spin_factor_casimir :
    spinGen1 * spinGen1 + spinGen2 * spinGen2 + spinGen3 * spinGen3 =
      (3 / 4 : ℂ) • (1 : SpinPair) := by
  rw [spinGen1_sq, spinGen2_sq, spinGen3_sq]
  module

theorem isospin_factor_casimir :
    isospinGen1 * isospinGen1 + isospinGen2 * isospinGen2 +
        isospinGen3 * isospinGen3 =
      (3 / 4 : ℂ) • (1 : SpinPair) := by
  rw [isospinGen1_sq, isospinGen2_sq, isospinGen3_sq]
  module

/-- Scaled spin and isospin actions commute. -/
theorem scaled_spin_isospin_commute (A B : M2C) :
    ((1 / 2 : ℂ) • spinAction A) * ((1 / 2 : ℂ) • isospinAction B) =
      ((1 / 2 : ℂ) • isospinAction B) * ((1 / 2 : ℂ) • spinAction A) := by
  rw [smul_mul_smul, smul_mul_smul, spin_isospin_actions_commute]

/-- Square of a commuting product of two scalar-square operators. -/
theorem product_sq_of_scalar_squares {s t : SpinPair} {c d : ℂ}
    (hs : s * s = c • (1 : SpinPair)) (ht : t * t = d • (1 : SpinPair))
    (hcomm : s * t = t * s) :
    (s * t) * (s * t) = (c * d) • (1 : SpinPair) := by
  calc
    (s * t) * (s * t) = s * (t * s) * t := by simp [mul_assoc]
    _ = s * (s * t) * t := by rw [hcomm]
    _ = (s * s) * (t * t) := by simp [mul_assoc]
    _ = (c * d) • (1 : SpinPair) := by
      rw [hs, ht, smul_mul_assoc, mul_smul_comm]
      simp [smul_smul]

/-- The nine Gamow--Teller squares are each `1/16` of the identity. -/
theorem gamow_teller_sq_sum :
    (spinGen1 * isospinGen1) * (spinGen1 * isospinGen1) +
    (spinGen1 * isospinGen2) * (spinGen1 * isospinGen2) +
    (spinGen1 * isospinGen3) * (spinGen1 * isospinGen3) +
    (spinGen2 * isospinGen1) * (spinGen2 * isospinGen1) +
    (spinGen2 * isospinGen2) * (spinGen2 * isospinGen2) +
    (spinGen2 * isospinGen3) * (spinGen2 * isospinGen3) +
    (spinGen3 * isospinGen1) * (spinGen3 * isospinGen1) +
    (spinGen3 * isospinGen2) * (spinGen3 * isospinGen2) +
    (spinGen3 * isospinGen3) * (spinGen3 * isospinGen3) =
      (9 / 16 : ℂ) • (1 : SpinPair) := by
  have hcomm (A B : M2C) :
      ((1 / 2 : ℂ) • spinAction A) * ((1 / 2 : ℂ) • isospinAction B) =
        ((1 / 2 : ℂ) • isospinAction B) * ((1 / 2 : ℂ) • spinAction A) :=
    scaled_spin_isospin_commute A B
  have hs1 : spinGen1 * spinGen1 = (1 / 4 : ℂ) • (1 : SpinPair) := spinGen1_sq
  have hs2 : spinGen2 * spinGen2 = (1 / 4 : ℂ) • (1 : SpinPair) := spinGen2_sq
  have hs3 : spinGen3 * spinGen3 = (1 / 4 : ℂ) • (1 : SpinPair) := spinGen3_sq
  have ht1 : isospinGen1 * isospinGen1 = (1 / 4 : ℂ) • (1 : SpinPair) := isospinGen1_sq
  have ht2 : isospinGen2 * isospinGen2 = (1 / 4 : ℂ) • (1 : SpinPair) := isospinGen2_sq
  have ht3 : isospinGen3 * isospinGen3 = (1 / 4 : ℂ) • (1 : SpinPair) := isospinGen3_sq
  have h11 := product_sq_of_scalar_squares hs1 ht1 (by simpa [spinGen1, isospinGen1] using hcomm I₁ I₁)
  have h12 := product_sq_of_scalar_squares hs1 ht2 (by simpa [spinGen1, isospinGen2] using hcomm I₁ I₂)
  have h13 := product_sq_of_scalar_squares hs1 ht3 (by simpa [spinGen1, isospinGen3] using hcomm I₁ I₃)
  have h21 := product_sq_of_scalar_squares hs2 ht1 (by simpa [spinGen2, isospinGen1] using hcomm I₂ I₁)
  have h22 := product_sq_of_scalar_squares hs2 ht2 (by simpa [spinGen2, isospinGen2] using hcomm I₂ I₂)
  have h23 := product_sq_of_scalar_squares hs2 ht3 (by simpa [spinGen2, isospinGen3] using hcomm I₂ I₃)
  have h31 := product_sq_of_scalar_squares hs3 ht1 (by simpa [spinGen3, isospinGen1] using hcomm I₃ I₁)
  have h32 := product_sq_of_scalar_squares hs3 ht2 (by simpa [spinGen3, isospinGen2] using hcomm I₃ I₂)
  have h33 := product_sq_of_scalar_squares hs3 ht3 (by simpa [spinGen3, isospinGen3] using hcomm I₃ I₃)
  rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  norm_num
  module

/-- With the repository's `σ/2` normalization, the 3+3+9 tensor-factor
generators give Casimir `33/16`, not the docstring's `15/4`. -/
theorem su4_tensor_casimir_value :
    (spinGen1 * spinGen1 + spinGen2 * spinGen2 + spinGen3 * spinGen3) +
    (isospinGen1 * isospinGen1 + isospinGen2 * isospinGen2 +
      isospinGen3 * isospinGen3) +
    ((spinGen1 * isospinGen1) * (spinGen1 * isospinGen1) +
    (spinGen1 * isospinGen2) * (spinGen1 * isospinGen2) +
    (spinGen1 * isospinGen3) * (spinGen1 * isospinGen3) +
    (spinGen2 * isospinGen1) * (spinGen2 * isospinGen1) +
    (spinGen2 * isospinGen2) * (spinGen2 * isospinGen2) +
    (spinGen2 * isospinGen3) * (spinGen2 * isospinGen3) +
    (spinGen3 * isospinGen1) * (spinGen3 * isospinGen1) +
    (spinGen3 * isospinGen2) * (spinGen3 * isospinGen2) +
    (spinGen3 * isospinGen3) * (spinGen3 * isospinGen3)) =
      (33 / 16 : ℂ) • (1 : SpinPair) := by
  rw [spin_factor_casimir, isospin_factor_casimir, gamow_teller_sq_sum]
  module

theorem su4_tensor_casimir_not_docstring_value :
    (33 / 16 : ℂ) ≠ 15 / 4 := by norm_num

/-- The `Tr(T_A T_B) = δ_AB / 2` normalization requires `1/√2` on the two
`SU(2)` factors and `√2 = 2/√2` on the nine tensor products. -/
def su4NormC : ℂ := ((Real.sqrt 2)⁻¹ : ℂ)

theorem su4NormC_sq : su4NormC * su4NormC = (1 / 2 : ℂ) := by
  unfold su4NormC
  rw [← mul_inv_rev]
  have hsqrt : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul]
    norm_num [Real.sq_sqrt]
  rw [hsqrt]
  norm_num

theorem su4NormC_twice_sq : (2 * su4NormC) * (2 * su4NormC) = (2 : ℂ) := by
  have h := su4NormC_sq
  calc
    (2 * su4NormC) * (2 * su4NormC) = 4 * (su4NormC * su4NormC) := by ring
    _ = 4 * (1 / 2 : ℂ) := by rw [h]
    _ = 2 := by norm_num

def su4Spin1 : SpinPair := su4NormC • spinGen1
def su4Spin2 : SpinPair := su4NormC • spinGen2
def su4Spin3 : SpinPair := su4NormC • spinGen3
def su4Iso1 : SpinPair := su4NormC • isospinGen1
def su4Iso2 : SpinPair := su4NormC • isospinGen2
def su4Iso3 : SpinPair := su4NormC • isospinGen3
def su4GT11 : SpinPair := (2 * su4NormC) • (spinGen1 * isospinGen1)
def su4GT12 : SpinPair := (2 * su4NormC) • (spinGen1 * isospinGen2)
def su4GT13 : SpinPair := (2 * su4NormC) • (spinGen1 * isospinGen3)
def su4GT21 : SpinPair := (2 * su4NormC) • (spinGen2 * isospinGen1)
def su4GT22 : SpinPair := (2 * su4NormC) • (spinGen2 * isospinGen2)
def su4GT23 : SpinPair := (2 * su4NormC) • (spinGen2 * isospinGen3)
def su4GT31 : SpinPair := (2 * su4NormC) • (spinGen3 * isospinGen1)
def su4GT32 : SpinPair := (2 * su4NormC) • (spinGen3 * isospinGen2)
def su4GT33 : SpinPair := (2 * su4NormC) • (spinGen3 * isospinGen3)

theorem su4Spin1_sq : su4Spin1 * su4Spin1 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4Spin1
  rw [smul_mul_smul, spinGen1_sq, su4NormC_sq, smul_smul]
  norm_num

theorem su4Spin2_sq : su4Spin2 * su4Spin2 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4Spin2
  rw [smul_mul_smul, spinGen2_sq, su4NormC_sq, smul_smul]
  norm_num

theorem su4Spin3_sq : su4Spin3 * su4Spin3 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4Spin3
  rw [smul_mul_smul, spinGen3_sq, su4NormC_sq, smul_smul]
  norm_num

theorem su4Iso1_sq : su4Iso1 * su4Iso1 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4Iso1
  rw [smul_mul_smul, isospinGen1_sq, su4NormC_sq, smul_smul]
  norm_num

theorem su4Iso2_sq : su4Iso2 * su4Iso2 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4Iso2
  rw [smul_mul_smul, isospinGen2_sq, su4NormC_sq, smul_smul]
  norm_num

theorem su4Iso3_sq : su4Iso3 * su4Iso3 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4Iso3
  rw [smul_mul_smul, isospinGen3_sq, su4NormC_sq, smul_smul]
  norm_num

theorem su4GT11_sq : su4GT11 * su4GT11 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT11
  rw [smul_mul_smul]
  have hcomm : spinGen1 * isospinGen1 = isospinGen1 * spinGen1 := by
    simpa [spinGen1, isospinGen1] using scaled_spin_isospin_commute I₁ I₁
  have hsq := product_sq_of_scalar_squares spinGen1_sq isospinGen1_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT12_sq : su4GT12 * su4GT12 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT12
  rw [smul_mul_smul]
  have hcomm : spinGen1 * isospinGen2 = isospinGen2 * spinGen1 := by
    simpa [spinGen1, isospinGen2] using scaled_spin_isospin_commute I₁ I₂
  have hsq := product_sq_of_scalar_squares spinGen1_sq isospinGen2_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT13_sq : su4GT13 * su4GT13 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT13
  rw [smul_mul_smul]
  have hcomm : spinGen1 * isospinGen3 = isospinGen3 * spinGen1 := by
    simpa [spinGen1, isospinGen3] using scaled_spin_isospin_commute I₁ I₃
  have hsq := product_sq_of_scalar_squares spinGen1_sq isospinGen3_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT21_sq : su4GT21 * su4GT21 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT21
  rw [smul_mul_smul]
  have hcomm : spinGen2 * isospinGen1 = isospinGen1 * spinGen2 := by
    simpa [spinGen2, isospinGen1] using scaled_spin_isospin_commute I₂ I₁
  have hsq := product_sq_of_scalar_squares spinGen2_sq isospinGen1_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT22_sq : su4GT22 * su4GT22 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT22
  rw [smul_mul_smul]
  have hcomm : spinGen2 * isospinGen2 = isospinGen2 * spinGen2 := by
    simpa [spinGen2, isospinGen2] using scaled_spin_isospin_commute I₂ I₂
  have hsq := product_sq_of_scalar_squares spinGen2_sq isospinGen2_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT23_sq : su4GT23 * su4GT23 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT23
  rw [smul_mul_smul]
  have hcomm : spinGen2 * isospinGen3 = isospinGen3 * spinGen2 := by
    simpa [spinGen2, isospinGen3] using scaled_spin_isospin_commute I₂ I₃
  have hsq := product_sq_of_scalar_squares spinGen2_sq isospinGen3_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT31_sq : su4GT31 * su4GT31 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT31
  rw [smul_mul_smul]
  have hcomm : spinGen3 * isospinGen1 = isospinGen1 * spinGen3 := by
    simpa [spinGen3, isospinGen1] using scaled_spin_isospin_commute I₃ I₁
  have hsq := product_sq_of_scalar_squares spinGen3_sq isospinGen1_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT32_sq : su4GT32 * su4GT32 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT32
  rw [smul_mul_smul]
  have hcomm : spinGen3 * isospinGen2 = isospinGen2 * spinGen3 := by
    simpa [spinGen3, isospinGen2] using scaled_spin_isospin_commute I₃ I₂
  have hsq := product_sq_of_scalar_squares spinGen3_sq isospinGen2_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4GT33_sq : su4GT33 * su4GT33 = (1 / 8 : ℂ) • (1 : SpinPair) := by
  unfold su4GT33
  rw [smul_mul_smul]
  have hcomm : spinGen3 * isospinGen3 = isospinGen3 * spinGen3 := by
    simpa [spinGen3, isospinGen3] using scaled_spin_isospin_commute I₃ I₃
  have hsq := product_sq_of_scalar_squares spinGen3_sq isospinGen3_sq hcomm
  rw [hsq, su4NormC_twice_sq, smul_smul]
  norm_num

theorem su4_normalized_casimir :
    (su4Spin1 * su4Spin1 + su4Spin2 * su4Spin2 + su4Spin3 * su4Spin3) +
    (su4Iso1 * su4Iso1 + su4Iso2 * su4Iso2 + su4Iso3 * su4Iso3) +
    (su4GT11 * su4GT11 + su4GT12 * su4GT12 + su4GT13 * su4GT13 +
     su4GT21 * su4GT21 + su4GT22 * su4GT22 + su4GT23 * su4GT23 +
     su4GT31 * su4GT31 + su4GT32 * su4GT32 + su4GT33 * su4GT33) =
      (15 / 8 : ℂ) • (1 : SpinPair) := by
  rw [su4Spin1_sq, su4Spin2_sq, su4Spin3_sq,
    su4Iso1_sq, su4Iso2_sq, su4Iso3_sq,
    su4GT11_sq, su4GT12_sq, su4GT13_sq,
    su4GT21_sq, su4GT22_sq, su4GT23_sq,
    su4GT31_sq, su4GT32_sq, su4GT33_sq]
  module

theorem su4_normalized_casimir_ne_docstring_value :
    (15 / 8 : ℂ) ≠ 15 / 4 := by norm_num

/-! ## Generalized Pauli-triple `(S, T)` pairing & 15-generator `su(4)` Lie closure -/

/-- Three-index Levi--Civita symbol `ε_{ijk}` over any commutative ring `K`. -/
def leviCivita (K : Type*) [Ring K] (i j k : Fin 3) : K :=
  match i, j, k with
  | 0, 1, 2 | 1, 2, 0 | 2, 0, 1 => 1
  | 0, 2, 1 | 2, 1, 0 | 1, 0, 2 => -1
  | _, _, _ => 0

/-- Generalized Pauli triple `(σ₁, σ₂, σ₃)` in an associative `K`-algebra `A`,
with an imaginary unit `iUnit : K` (`iUnit² = -1`). -/
structure PauliTriple (K A : Type*) [CommRing K] [Ring A] [Algebra K A] where
  iUnit : K
  iUnit_sq : iUnit * iUnit = -1
  gen : Fin 3 → A
  gen_sq : ∀ i : Fin 3, gen i * gen i = 1
  gen_anticomm : ∀ i j : Fin 3, i ≠ j → gen i * gen j + gen j * gen i = 0
  gen_comm : ∀ i j : Fin 3,
    gen i * gen j - gen j * gen i =
      ((2 : K) * iUnit) • ∑ k : Fin 3, leviCivita K i j k • gen k

section GeneralPauliSU4

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A] (P : PauliTriple K A)

/-- Associative commutator bracket on `A ⊗[K] A`. -/
def tensorBracket (X Y : A ⊗[K] A) : A ⊗[K] A := X * Y - Y * X

/-- Spin generator `Sᵢ = ½ (σᵢ ⊗ 1)` on `A ⊗[K] A`. -/
def su4SpinGen (i : Fin 3) : A ⊗[K] A := (1 / 2 : K) • (P.gen i ⊗ₜ[K] (1 : A))

/-- Isospin generator `Tⱼ = ½ (1 ⊗ τⱼ)` on `A ⊗[K] A`. -/
def su4IsospinGen (j : Fin 3) : A ⊗[K] A := (1 / 2 : K) • ((1 : A) ⊗ₜ[K] P.gen j)

/-- Gamow--Teller generator `Yᵢⱼ = ½ (σᵢ ⊗ τⱼ)` on `A ⊗[K] A`. -/
def su4GamowTellerGen (i j : Fin 3) : A ⊗[K] A := (1 / 2 : K) • (P.gen i ⊗ₜ[K] P.gen j)

theorem su4SpinGen_sq (i : Fin 3) :
    su4SpinGen P i * su4SpinGen P i = (1 / 4 : K) • (1 : A ⊗[K] A) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold su4SpinGen
  rw [smul_mul_smul, tmul_mul_tmul, P.gen_sq i, one_mul, Algebra.TensorProduct.one_def]
  congr 1; field_simp [h2]; ring

theorem su4IsospinGen_sq (j : Fin 3) :
    su4IsospinGen P j * su4IsospinGen P j = (1 / 4 : K) • (1 : A ⊗[K] A) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold su4IsospinGen
  rw [smul_mul_smul, tmul_mul_tmul, one_mul, P.gen_sq j, Algebra.TensorProduct.one_def]
  congr 1; field_simp [h2]; ring

theorem su4GamowTellerGen_sq (i j : Fin 3) :
    su4GamowTellerGen P i j * su4GamowTellerGen P i j = (1 / 4 : K) • (1 : A ⊗[K] A) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold su4GamowTellerGen
  rw [smul_mul_smul, tmul_mul_tmul, P.gen_sq i, P.gen_sq j, Algebra.TensorProduct.one_def]
  congr 1; field_simp [h2]; ring

theorem su4GamowTellerGen_eq_two_mul (i j : Fin 3) :
    su4GamowTellerGen P i j = (2 : K) • (su4SpinGen P i * su4IsospinGen P j) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold su4GamowTellerGen su4SpinGen su4IsospinGen
  rw [smul_mul_smul, tmul_mul_tmul, mul_one, one_mul, smul_smul]
  congr 1; field_simp [h2]

/-- Quadratic Casimir of the 15-generator `su(4)` algebra on `A ⊗[K] A`. -/
def su4CasimirOf : A ⊗[K] A :=
  (∑ i : Fin 3, su4SpinGen P i * su4SpinGen P i) +
  (∑ j : Fin 3, su4IsospinGen P j * su4IsospinGen P j) +
  (∑ i : Fin 3, ∑ j : Fin 3, su4GamowTellerGen P i j * su4GamowTellerGen P i j)

/-- Exact Wigner `su(4)` Casimir eigenvalue `15/4` for any `PauliTriple K A`. -/
theorem su4CasimirOf_eq_fifteen_fourths :
    su4CasimirOf P = (15 / 4 : K) • (1 : A ⊗[K] A) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold su4CasimirOf
  simp only [su4SpinGen_sq, su4IsospinGen_sq, su4GamowTellerGen_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← smul_assoc, ← add_smul]
  congr 1
  field_simp [h2]
  ring

omit [CharZero K] in
private theorem pauliTriple_anticomm_all (i j : Fin 3) :
    P.gen i * P.gen j + P.gen j * P.gen i =
      if i = j then (2 : K) • (1 : A) else 0 := by
  by_cases h : i = j
  · subst h
    simp [P.gen_sq i, two_smul]
  · simp [h, P.gen_anticomm i j h]

omit [CharZero K] in
private theorem tmul_comm_expand_of (a b c d : A) :
    (2 : K) • ((a ⊗ₜ[K] b) * (c ⊗ₜ[K] d) - (c ⊗ₜ[K] d) * (a ⊗ₜ[K] b)) =
      (a * c - c * a) ⊗ₜ[K] (b * d + d * b) +
      (a * c + c * a) ⊗ₜ[K] (b * d - d * b) := by
  rw [tmul_mul_tmul, tmul_mul_tmul]
  simp only [TensorProduct.sub_tmul, TensorProduct.tmul_add, TensorProduct.add_tmul,
    TensorProduct.tmul_sub, two_smul]
  abel

theorem su4SpinGen_comm (i j : Fin 3) :
    tensorBracket (su4SpinGen P i) (su4SpinGen P j) =
      P.iUnit • ∑ k : Fin 3, leviCivita K i j k • su4SpinGen P k := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold tensorBracket su4SpinGen
  rw [smul_mul_smul, smul_mul_smul, ← smul_sub, tmul_mul_tmul, tmul_mul_tmul, one_mul,
    ← TensorProduct.sub_tmul, P.gen_comm i j, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    TensorProduct.sum_tmul]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1; field_simp [h2]

theorem su4IsospinGen_comm (i j : Fin 3) :
    tensorBracket (su4IsospinGen P i) (su4IsospinGen P j) =
      P.iUnit • ∑ k : Fin 3, leviCivita K i j k • su4IsospinGen P k := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold tensorBracket su4IsospinGen
  rw [smul_mul_smul, smul_mul_smul, ← smul_sub, tmul_mul_tmul, tmul_mul_tmul, one_mul,
    ← TensorProduct.tmul_sub, P.gen_comm i j, TensorProduct.tmul_smul, TensorProduct.tmul_sum]
  simp only [TensorProduct.tmul_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1; field_simp [h2]

omit [CharZero K] in
theorem su4SpinGen_isospinGen_comm (i j : Fin 3) :
    tensorBracket (su4SpinGen P i) (su4IsospinGen P j) = 0 := by
  unfold tensorBracket su4SpinGen su4IsospinGen
  rw [smul_mul_smul, smul_mul_smul, tmul_mul_tmul, tmul_mul_tmul]
  simp only [mul_one, one_mul, sub_self]

theorem su4SpinGen_gamowTellerGen_comm (i j k : Fin 3) :
    tensorBracket (su4SpinGen P i) (su4GamowTellerGen P j k) =
      P.iUnit • ∑ l : Fin 3, leviCivita K i j l • su4GamowTellerGen P l k := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold tensorBracket su4SpinGen su4GamowTellerGen
  rw [smul_mul_smul, smul_mul_smul, ← smul_sub, tmul_mul_tmul, tmul_mul_tmul, one_mul, mul_one,
    ← TensorProduct.sub_tmul, P.gen_comm i j, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    TensorProduct.sum_tmul]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1; field_simp [h2]

theorem su4IsospinGen_gamowTellerGen_comm (j i k : Fin 3) :
    tensorBracket (su4IsospinGen P j) (su4GamowTellerGen P i k) =
      P.iUnit • ∑ l : Fin 3, leviCivita K j k l • su4GamowTellerGen P i l := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold tensorBracket su4IsospinGen su4GamowTellerGen
  rw [smul_mul_smul, smul_mul_smul, ← smul_sub, tmul_mul_tmul, tmul_mul_tmul, one_mul, mul_one,
    ← TensorProduct.tmul_sub, P.gen_comm j k, TensorProduct.tmul_smul, TensorProduct.tmul_sum]
  simp only [TensorProduct.tmul_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1; field_simp [h2]

/-- Noncommutativity obstruction: the Gamow--Teller commutator `[Y_{ij}, Y_{kl}]` fails to vanish
and regenerates the spin (`S_m`) and isospin (`T_m`) sectors, forcing `su(2)_S ⊕ su(2)_T`
to enlarge to the 15-generator `su(4)` Lie algebra. -/
theorem su4GamowTellerGen_comm (i j k l : Fin 3) :
    tensorBracket (su4GamowTellerGen P i j) (su4GamowTellerGen P k l) =
      (if i = k then P.iUnit • ∑ m : Fin 3, leviCivita K j l m • su4IsospinGen P m else 0) +
      (if j = l then P.iUnit • ∑ m : Fin 3, leviCivita K i k m • su4SpinGen P m else 0) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold tensorBracket su4GamowTellerGen
  rw [smul_mul_smul, smul_mul_smul, ← smul_sub]
  have hexp := tmul_comm_expand_of (K := K) (P.gen i) (P.gen j) (P.gen k) (P.gen l)
  have hhalf :
      (P.gen i ⊗ₜ[K] P.gen j) * (P.gen k ⊗ₜ[K] P.gen l) -
        (P.gen k ⊗ₜ[K] P.gen l) * (P.gen i ⊗ₜ[K] P.gen j) =
      (1 / 2 : K) • ((P.gen i * P.gen k - P.gen k * P.gen i) ⊗ₜ[K]
          (P.gen j * P.gen l + P.gen l * P.gen j) +
        (P.gen i * P.gen k + P.gen k * P.gen i) ⊗ₜ[K]
          (P.gen j * P.gen l - P.gen l * P.gen j)) := by
    rw [← hexp, smul_smul]
    have hmul1 : (1 / 2 : K) * 2 = 1 := by field_simp [h2]
    rw [hmul1, one_smul]
  rw [hhalf, smul_smul, P.gen_comm i k, pauliTriple_anticomm_all P j l,
    pauliTriple_anticomm_all P i k, P.gen_comm j l]
  have hterm1 :
      ((1 / 2 : K) * (1 / 2 : K) * (1 / 2 : K)) •
        ((((2 : K) * P.iUnit) • ∑ m : Fin 3, leviCivita K i k m • P.gen m) ⊗ₜ[K]
          (if j = l then (2 : K) • (1 : A) else 0)) =
      if j = l then P.iUnit • ∑ m : Fin 3, leviCivita K i k m • su4SpinGen P m else 0 := by
    split_ifs
    · simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.sum_tmul,
        Finset.smul_sum, smul_smul, su4SpinGen]
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1; field_simp [h2]
    · simp
  have hterm2 :
      ((1 / 2 : K) * (1 / 2 : K) * (1 / 2 : K)) •
        ((if i = k then (2 : K) • (1 : A) else 0) ⊗ₜ[K]
          (((2 : K) * P.iUnit) • ∑ m : Fin 3, leviCivita K j l m • P.gen m)) =
      if i = k then P.iUnit • ∑ m : Fin 3, leviCivita K j l m • su4IsospinGen P m else 0 := by
    split_ifs
    · simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_sum,
        Finset.smul_sum, smul_smul, su4IsospinGen]
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1; field_simp [h2]
    · simp
  rw [smul_add, hterm1, hterm2, add_comm]

/-- Spin-singlet (`S = 0`) projector `¼(1⊗1 - ∑ᵢ σᵢ⊗σᵢ)` on `A ⊗[K] A` for any `PauliTriple K A`. -/
def singletProjectorOf : A ⊗[K] A :=
  (1 / 4 : K) • ((1 : A) ⊗ₜ[K] (1 : A) - ∑ i : Fin 3, P.gen i ⊗ₜ[K] P.gen i)

/-- Spin-triplet (`S = 1`) projector `1 - P_{S=0}` on `A ⊗[K] A`. -/
def tripletProjectorOf : A ⊗[K] A :=
  (1 : A ⊗[K] A) - singletProjectorOf P

/-- Exchange swap operator `P_σ = ½(1⊗1 + ∑ᵢ σᵢ⊗σᵢ)` on `A ⊗[K] A`. -/
def swapOf : A ⊗[K] A :=
  (1 / 2 : K) • ((1 : A) ⊗ₜ[K] (1 : A) + ∑ i : Fin 3, P.gen i ⊗ₜ[K] P.gen i)

private theorem sum_gen_tmul_gen_sq :
    (∑ i : Fin 3, P.gen i ⊗ₜ[K] P.gen i) * (∑ j : Fin 3, P.gen j ⊗ₜ[K] P.gen j) =
      (3 : K) • ((1 : A) ⊗ₜ[K] (1 : A)) - (2 : K) • (∑ k : Fin 3, P.gen k ⊗ₜ[K] P.gen k) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hmul (i j : Fin 3) :
      (P.gen i ⊗ₜ[K] P.gen i) * (P.gen j ⊗ₜ[K] P.gen j) =
        (P.gen i * P.gen j) ⊗ₜ[K] (P.gen i * P.gen j) :=
    tmul_mul_tmul _ _ _ _
  have h01 : (P.gen 0 * P.gen 1) ⊗ₜ[K] (P.gen 0 * P.gen 1) +
      (P.gen 1 * P.gen 0) ⊗ₜ[K] (P.gen 1 * P.gen 0) = -(2 : K) • (P.gen 2 ⊗ₜ[K] P.gen 2) := by
    have hcomm01 : P.gen 0 * P.gen 1 - P.gen 1 * P.gen 0 = ((2 : K) * P.iUnit) • P.gen 2 := by
      simpa [leviCivita, Fin.sum_univ_three] using P.gen_comm 0 1
    have hanti01 : P.gen 1 * P.gen 0 = -(P.gen 0 * P.gen 1) :=
      eq_neg_of_add_eq_zero_right (P.gen_anticomm 0 1 (by decide))
    have hp01 : P.gen 0 * P.gen 1 = P.iUnit • P.gen 2 := by
      rw [hanti01, sub_neg_eq_add, ← two_smul K] at hcomm01
      have hsc := congrArg (fun x => (1 / 2 : K) • x) hcomm01
      simp only [smul_smul] at hsc
      have ha : (1 / 2 : K) * 2 = 1 := by field_simp [h2]
      have hb : (1 / 2 : K) * ((2 : K) * P.iUnit) = P.iUnit := by field_simp [h2]
      rw [ha, hb, one_smul] at hsc
      exact hsc
    rw [hanti01, hp01, neg_tmul, tmul_neg, neg_neg]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, P.iUnit_sq]
    module
  have h12 : (P.gen 1 * P.gen 2) ⊗ₜ[K] (P.gen 1 * P.gen 2) +
      (P.gen 2 * P.gen 1) ⊗ₜ[K] (P.gen 2 * P.gen 1) = -(2 : K) • (P.gen 0 ⊗ₜ[K] P.gen 0) := by
    have hcomm12 : P.gen 1 * P.gen 2 - P.gen 2 * P.gen 1 = ((2 : K) * P.iUnit) • P.gen 0 := by
      simpa [leviCivita, Fin.sum_univ_three] using P.gen_comm 1 2
    have hanti12 : P.gen 2 * P.gen 1 = -(P.gen 1 * P.gen 2) :=
      eq_neg_of_add_eq_zero_right (P.gen_anticomm 1 2 (by decide))
    have hp12 : P.gen 1 * P.gen 2 = P.iUnit • P.gen 0 := by
      rw [hanti12, sub_neg_eq_add, ← two_smul K] at hcomm12
      have hsc := congrArg (fun x => (1 / 2 : K) • x) hcomm12
      simp only [smul_smul] at hsc
      have ha : (1 / 2 : K) * 2 = 1 := by field_simp [h2]
      have hb : (1 / 2 : K) * ((2 : K) * P.iUnit) = P.iUnit := by field_simp [h2]
      rw [ha, hb, one_smul] at hsc
      exact hsc
    rw [hanti12, hp12, neg_tmul, tmul_neg, neg_neg]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, P.iUnit_sq]
    module
  have h20 : (P.gen 2 * P.gen 0) ⊗ₜ[K] (P.gen 2 * P.gen 0) +
      (P.gen 0 * P.gen 2) ⊗ₜ[K] (P.gen 0 * P.gen 2) = -(2 : K) • (P.gen 1 ⊗ₜ[K] P.gen 1) := by
    have hcomm20 : P.gen 2 * P.gen 0 - P.gen 0 * P.gen 2 = ((2 : K) * P.iUnit) • P.gen 1 := by
      simpa [leviCivita, Fin.sum_univ_three] using P.gen_comm 2 0
    have hanti20 : P.gen 0 * P.gen 2 = -(P.gen 2 * P.gen 0) :=
      eq_neg_of_add_eq_zero_right (P.gen_anticomm 2 0 (by decide))
    have hp20 : P.gen 2 * P.gen 0 = P.iUnit • P.gen 1 := by
      rw [hanti20, sub_neg_eq_add, ← two_smul K] at hcomm20
      have hsc := congrArg (fun x => (1 / 2 : K) • x) hcomm20
      simp only [smul_smul] at hsc
      have ha : (1 / 2 : K) * 2 = 1 := by field_simp [h2]
      have hb : (1 / 2 : K) * ((2 : K) * P.iUnit) = P.iUnit := by field_simp [h2]
      rw [ha, hb, one_smul] at hsc
      exact hsc
    rw [hanti20, hp20, neg_tmul, tmul_neg, neg_neg]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, P.iUnit_sq]
    module
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, hmul, Fin.sum_univ_three, P.gen_sq]
  have hsplit :
      (((1 : A) ⊗ₜ[K] (1 : A) + (P.gen 0 * P.gen 1) ⊗ₜ[K] (P.gen 0 * P.gen 1) +
        (P.gen 0 * P.gen 2) ⊗ₜ[K] (P.gen 0 * P.gen 2)) +
      ((P.gen 1 * P.gen 0) ⊗ₜ[K] (P.gen 1 * P.gen 0) + (1 : A) ⊗ₜ[K] (1 : A) +
        (P.gen 1 * P.gen 2) ⊗ₜ[K] (P.gen 1 * P.gen 2))) +
      ((P.gen 2 * P.gen 0) ⊗ₜ[K] (P.gen 2 * P.gen 0) +
        (P.gen 2 * P.gen 1) ⊗ₜ[K] (P.gen 2 * P.gen 1) + (1 : A) ⊗ₜ[K] (1 : A)) =
      (3 : K) • ((1 : A) ⊗ₜ[K] (1 : A)) +
        (((P.gen 0 * P.gen 1) ⊗ₜ[K] (P.gen 0 * P.gen 1) +
          (P.gen 1 * P.gen 0) ⊗ₜ[K] (P.gen 1 * P.gen 0)) +
         ((P.gen 1 * P.gen 2) ⊗ₜ[K] (P.gen 1 * P.gen 2) +
          (P.gen 2 * P.gen 1) ⊗ₜ[K] (P.gen 2 * P.gen 1)) +
         ((P.gen 2 * P.gen 0) ⊗ₜ[K] (P.gen 2 * P.gen 0) +
          (P.gen 0 * P.gen 2) ⊗ₜ[K] (P.gen 0 * P.gen 2))) := by
    rw [show (3 : K) • ((1 : A) ⊗ₜ[K] (1 : A)) =
        (1 : A) ⊗ₜ[K] (1 : A) + (1 : A) ⊗ₜ[K] (1 : A) + (1 : A) ⊗ₜ[K] (1 : A) by module]
    abel
  rw [hsplit, h01, h12, h20]
  module

theorem singletProjectorOf_idem :
    singletProjectorOf P * singletProjectorOf P = singletProjectorOf P := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold singletProjectorOf
  rw [smul_mul_smul, sub_mul, mul_sub, mul_sub, tmul_mul_tmul, one_mul, Finset.sum_mul,
    Finset.mul_sum]
  have hone (x : A ⊗[K] A) : ((1 : A) ⊗ₜ[K] (1 : A)) * x = x := by
    rw [← Algebra.TensorProduct.one_def, one_mul]
  have honer (x : A ⊗[K] A) : x * ((1 : A) ⊗ₜ[K] (1 : A)) = x := by
    rw [← Algebra.TensorProduct.one_def, mul_one]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hone, honer]
  rw [sum_gen_tmul_gen_sq P, show (1 / 4 : K) * (1 / 4 : K) = 1 / 16 by field_simp [h2]; ring]
  abel_nf; module

theorem tripletProjectorOf_idem :
    tripletProjectorOf P * tripletProjectorOf P = tripletProjectorOf P := by
  unfold tripletProjectorOf
  rw [sub_mul, mul_sub, one_mul, mul_sub, mul_one, singletProjectorOf_idem P]
  simp

theorem singletOf_mul_tripletOf :
    singletProjectorOf P * tripletProjectorOf P = 0 := by
  unfold tripletProjectorOf
  rw [mul_sub, mul_one, singletProjectorOf_idem P, sub_self]

theorem tripletOf_mul_singletOf :
    tripletProjectorOf P * singletProjectorOf P = 0 := by
  unfold tripletProjectorOf
  rw [sub_mul, one_mul, singletProjectorOf_idem P, sub_self]

omit [CharZero K] in
theorem singletOf_add_tripletOf :
    singletProjectorOf P + tripletProjectorOf P = (1 : A ⊗[K] A) := by
  unfold tripletProjectorOf
  abel

/-- Generalized total two-strand spin Casimir `S_tot²` on `A ⊗[K] A`. -/
def twoStrandSpinCasimirOf : A ⊗[K] A :=
  ∑ i : Fin 3,
    ((1 / 2 : K) • (P.gen i ⊗ₜ[K] (1 : A) + (1 : A) ⊗ₜ[K] P.gen i)) *
    ((1 / 2 : K) • (P.gen i ⊗ₜ[K] (1 : A) + (1 : A) ⊗ₜ[K] P.gen i))

/-- For any `PauliTriple K A`, `S_tot² = 2 • P_{S=1}` separates `S = 0` from `S = 1`. -/
theorem twoStrandSpinCasimirOf_eq_two_triplet :
    twoStrandSpinCasimirOf P = (2 : K) • tripletProjectorOf P := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  unfold twoStrandSpinCasimirOf
  have hterm (i : Fin 3) :
      ((1 / 2 : K) • (P.gen i ⊗ₜ[K] (1 : A) + (1 : A) ⊗ₜ[K] P.gen i)) *
      ((1 / 2 : K) • (P.gen i ⊗ₜ[K] (1 : A) + (1 : A) ⊗ₜ[K] P.gen i)) =
      (1 / 2 : K) • ((1 : A) ⊗ₜ[K] (1 : A) + P.gen i ⊗ₜ[K] P.gen i) := by
    rw [smul_mul_smul, add_mul, mul_add, mul_add, tmul_mul_tmul, tmul_mul_tmul, tmul_mul_tmul,
      tmul_mul_tmul, P.gen_sq i]
    simp only [one_mul, mul_one]
    rw [add_comm (P.gen i ⊗ₜ[K] P.gen i) ((1 : A) ⊗ₜ[K] (1 : A))]
    have hadd : ((1 : A) ⊗ₜ[K] (1 : A) + P.gen i ⊗ₜ[K] P.gen i) +
        ((1 : A) ⊗ₜ[K] (1 : A) + P.gen i ⊗ₜ[K] P.gen i) =
        (2 : K) • ((1 : A) ⊗ₜ[K] (1 : A) + P.gen i ⊗ₜ[K] P.gen i) := by
      rw [two_smul]
    rw [hadd, smul_smul]
    congr 1; field_simp [h2]
  simp_rw [hterm, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  have h3 : (3 : ℕ) • ((1 : A) ⊗ₜ[K] (1 : A)) = (3 : K) • ((1 : A) ⊗ₜ[K] (1 : A)) := by
    rw [← Nat.cast_smul_eq_nsmul K]; simp
  rw [h3]
  unfold tripletProjectorOf singletProjectorOf
  rw [Algebra.TensorProduct.one_def, smul_add]
  simp only [smul_sub, smul_smul]
  norm_num
  module

theorem swapOf_eq_triplet_sub_singlet :
    swapOf P = tripletProjectorOf P - singletProjectorOf P := by
  unfold swapOf tripletProjectorOf singletProjectorOf
  rw [Algebra.TensorProduct.one_def]
  module

theorem swapOf_mul_singlet :
    swapOf P * singletProjectorOf P = -singletProjectorOf P := by
  rw [swapOf_eq_triplet_sub_singlet P, sub_mul, tripletOf_mul_singletOf P,
    singletProjectorOf_idem P]
  abel

theorem swapOf_mul_triplet :
    swapOf P * tripletProjectorOf P = tripletProjectorOf P := by
  rw [swapOf_eq_triplet_sub_singlet P, sub_mul, tripletProjectorOf_idem P,
    singletOf_mul_tripletOf P, sub_zero]

/-- Generalized `(S, T)` pairing projectors on `(A ⊗[K] A) ⊗[K] (A ⊗[K] A)`. -/
def pairingChannel00Of : (A ⊗[K] A) ⊗[K] (A ⊗[K] A) :=
  singletProjectorOf P ⊗ₜ[K] singletProjectorOf P

def pairingChannel01Of : (A ⊗[K] A) ⊗[K] (A ⊗[K] A) :=
  singletProjectorOf P ⊗ₜ[K] tripletProjectorOf P

def pairingChannel10Of : (A ⊗[K] A) ⊗[K] (A ⊗[K] A) :=
  tripletProjectorOf P ⊗ₜ[K] singletProjectorOf P

def pairingChannel11Of : (A ⊗[K] A) ⊗[K] (A ⊗[K] A) :=
  tripletProjectorOf P ⊗ₜ[K] tripletProjectorOf P

def wignerPairing6AOf : (A ⊗[K] A) ⊗[K] (A ⊗[K] A) :=
  pairingChannel01Of P + pairingChannel10Of P

def wignerPairing10SOf : (A ⊗[K] A) ⊗[K] (A ⊗[K] A) :=
  pairingChannel00Of P + pairingChannel11Of P

def twoNucleonSU4CasimirOf : (A ⊗[K] A) ⊗[K] (A ⊗[K] A) :=
  (7 : K) • (1 : (A ⊗[K] A) ⊗[K] (A ⊗[K] A)) + (2 : K) • (swapOf P ⊗ₜ[K] swapOf P)

theorem twoNucleonSU4CasimirOf_mul_wignerPairing6AOf :
    twoNucleonSU4CasimirOf P * wignerPairing6AOf P = (5 : K) • wignerPairing6AOf P := by
  unfold twoNucleonSU4CasimirOf wignerPairing6AOf pairingChannel01Of pairingChannel10Of
  rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, mul_add, tmul_mul_tmul, tmul_mul_tmul,
    swapOf_mul_singlet P, swapOf_mul_triplet P, neg_tmul, tmul_neg]
  module

theorem twoNucleonSU4CasimirOf_mul_wignerPairing10SOf :
    twoNucleonSU4CasimirOf P * wignerPairing10SOf P = (9 : K) • wignerPairing10SOf P := by
  unfold twoNucleonSU4CasimirOf wignerPairing10SOf pairingChannel00Of pairingChannel11Of
  rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, mul_add, tmul_mul_tmul, tmul_mul_tmul,
    swapOf_mul_singlet P, swapOf_mul_triplet P, neg_tmul, tmul_neg, neg_neg]
  module

theorem wignerPairing6AOf_idem :
    wignerPairing6AOf P * wignerPairing6AOf P = wignerPairing6AOf P := by
  unfold wignerPairing6AOf pairingChannel01Of pairingChannel10Of
  simp only [add_mul, mul_add, tmul_mul_tmul,
    singletProjectorOf_idem P, tripletProjectorOf_idem P, singletOf_mul_tripletOf P,
    tripletOf_mul_singletOf P, tmul_zero, add_zero, zero_add]

theorem wignerPairing10SOf_idem :
    wignerPairing10SOf P * wignerPairing10SOf P = wignerPairing10SOf P := by
  unfold wignerPairing10SOf pairingChannel00Of pairingChannel11Of
  simp only [add_mul, mul_add, tmul_mul_tmul,
    singletProjectorOf_idem P, tripletProjectorOf_idem P, singletOf_mul_tripletOf P,
    tripletOf_mul_singletOf P, tmul_zero, add_zero, zero_add]

theorem wignerPairing6AOf_mul_10SOf :
    wignerPairing6AOf P * wignerPairing10SOf P = 0 := by
  unfold wignerPairing6AOf wignerPairing10SOf pairingChannel00Of pairingChannel01Of
    pairingChannel10Of pairingChannel11Of
  simp only [add_mul, mul_add, tmul_mul_tmul,
    singletOf_mul_tripletOf P, tripletOf_mul_singletOf P, tmul_zero, zero_tmul, add_zero]

omit [CharZero K] in
theorem wignerPairing6AOf_add_10SOf :
    wignerPairing6AOf P + wignerPairing10SOf P = (1 : (A ⊗[K] A) ⊗[K] (A ⊗[K] A)) := by
  unfold wignerPairing6AOf wignerPairing10SOf pairingChannel00Of pairingChannel01Of
    pairingChannel10Of pairingChannel11Of
  calc
    (singletProjectorOf P ⊗ₜ[K] tripletProjectorOf P +
        tripletProjectorOf P ⊗ₜ[K] singletProjectorOf P) +
      (singletProjectorOf P ⊗ₜ[K] singletProjectorOf P +
        tripletProjectorOf P ⊗ₜ[K] tripletProjectorOf P) =
      singletProjectorOf P ⊗ₜ[K] (singletProjectorOf P + tripletProjectorOf P) +
      tripletProjectorOf P ⊗ₜ[K] (singletProjectorOf P + tripletProjectorOf P) := by
      simp only [TensorProduct.tmul_add]; abel
    _ = (1 : (A ⊗[K] A) ⊗[K] (A ⊗[K] A)) := by
      rw [singletOf_add_tripletOf P, ← TensorProduct.add_tmul, singletOf_add_tripletOf P,
        ← Algebra.TensorProduct.one_def]

end GeneralPauliSU4

/-! ## Concrete `SpinPair = M₂(ℂ) ⊗ M₂(ℂ)` instantiation, linear independence & `(S, T)` pairing -/

/-- Indexed Pauli matrices `(σ₁, σ₂, σ₃)` in the `WeakIsospinSU2` basis. -/
def pauliBasis : Fin 3 → M2C
  | 0 => I₁
  | 1 => I₂
  | 2 => I₃

theorem pauliBasis_sq (i : Fin 3) :
    pauliBasis i * pauliBasis i = (1 : M2C) := by
  unfold pauliBasis
  fin_cases i
  · exact I₁_sq
  · exact I₂_sq
  · exact I₃_sq

/-- Pauli commutator: `[σᵢ, σⱼ] = 2i ∑ₖ εᵢⱼₖ σₖ`. -/
theorem pauliBasis_comm (i j : Fin 3) :
    pauliBasis i * pauliBasis j - pauliBasis j * pauliBasis i =
      (2 * Complex.I) • ∑ k : Fin 3, leviCivita ℂ i j k • pauliBasis k := by
  fin_cases i <;> fin_cases j
  · simp [leviCivita]
  · simp [pauliBasis, I₁_comm_I₂, leviCivita, Fin.sum_univ_three]
  · change pauliBasis 0 * pauliBasis 2 - pauliBasis 2 * pauliBasis 0 = _
    rw [show pauliBasis 0 * pauliBasis 2 - pauliBasis 2 * pauliBasis 0 =
        -(pauliBasis 2 * pauliBasis 0 - pauliBasis 0 * pauliBasis 2) by abel]
    simp [pauliBasis, I₃_comm_I₁, leviCivita, Fin.sum_univ_three]
  · change pauliBasis 1 * pauliBasis 0 - pauliBasis 0 * pauliBasis 1 = _
    rw [show pauliBasis 1 * pauliBasis 0 - pauliBasis 0 * pauliBasis 1 =
        -(pauliBasis 0 * pauliBasis 1 - pauliBasis 1 * pauliBasis 0) by abel]
    simp [pauliBasis, I₁_comm_I₂, leviCivita, Fin.sum_univ_three]
  · simp [leviCivita]
  · simp [pauliBasis, I₂_comm_I₃, leviCivita, Fin.sum_univ_three]
  · simp [pauliBasis, I₃_comm_I₁, leviCivita, Fin.sum_univ_three]
  · change pauliBasis 2 * pauliBasis 1 - pauliBasis 1 * pauliBasis 2 = _
    rw [show pauliBasis 2 * pauliBasis 1 - pauliBasis 1 * pauliBasis 2 =
        -(pauliBasis 1 * pauliBasis 2 - pauliBasis 2 * pauliBasis 1) by abel]
    simp [pauliBasis, I₂_comm_I₃, leviCivita, Fin.sum_univ_three]
  · simp [leviCivita]

/-- Pauli anticommutator: `{σᵢ, σⱼ} = 2 δᵢⱼ I`. -/
theorem pauliBasis_anticomm (i j : Fin 3) :
    pauliBasis i * pauliBasis j + pauliBasis j * pauliBasis i =
      if i = j then (2 : ℂ) • (1 : M2C) else 0 := by
  fin_cases i <;> fin_cases j <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    (simp [pauliBasis, I₁, I₂, I₃, σPlus, σMinus, σ3c, Complex.I_mul_I];
     try norm_num)

/-- Concrete `PauliTriple ℂ M2C` witness. -/
def pauliTripleM2C : PauliTriple ℂ M2C where
  iUnit := Complex.I
  iUnit_sq := Complex.I_mul_I
  gen := pauliBasis
  gen_sq := pauliBasis_sq
  gen_anticomm i j hij := by simpa [hij] using pauliBasis_anticomm i j
  gen_comm := pauliBasis_comm

/-- Indexed spin generator `Sᵢ = ½ (σᵢ ⊗ 1)`. -/
def spinGenVec (i : Fin 3) : SpinPair := su4SpinGen pauliTripleM2C i

/-- Indexed isospin generator `Tⱼ = ½ (1 ⊗ τⱼ)`. -/
def isospinGenVec (j : Fin 3) : SpinPair := su4IsospinGen pauliTripleM2C j

/-- Indexed Gamow--Teller generator `Yᵢⱼ = ½ (σᵢ ⊗ τⱼ) = 2 Sᵢ Tⱼ`. -/
def gamowTellerGen (i j : Fin 3) : SpinPair := su4GamowTellerGen pauliTripleM2C i j

/-- Associative commutator on `SpinPair`. -/
def pairBracket (A B : SpinPair) : SpinPair := tensorBracket A B

theorem gamowTellerGen_eq_tmul (i j : Fin 3) :
    gamowTellerGen i j = (1 / 2 : ℂ) • (pauliBasis i ⊗ₜ[ℂ] pauliBasis j) := by
  unfold gamowTellerGen su4GamowTellerGen pauliTripleM2C
  rfl

theorem gamowTellerGen_eq_two_mul (i j : Fin 3) :
    gamowTellerGen i j = (2 : ℂ) • (spinGenVec i * isospinGenVec j) := by
  unfold gamowTellerGen spinGenVec isospinGenVec
  exact su4GamowTellerGen_eq_two_mul pauliTripleM2C i j

theorem spinGenVec_sq (i : Fin 3) :
    spinGenVec i * spinGenVec i = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold spinGenVec
  exact su4SpinGen_sq pauliTripleM2C i

theorem isospinGenVec_sq (j : Fin 3) :
    isospinGenVec j * isospinGenVec j = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold isospinGenVec
  exact su4IsospinGen_sq pauliTripleM2C j

theorem gamowTellerGen_sq (i j : Fin 3) :
    gamowTellerGen i j * gamowTellerGen i j = (1 / 4 : ℂ) • (1 : SpinPair) := by
  unfold gamowTellerGen
  exact su4GamowTellerGen_sq pauliTripleM2C i j

/-- Quadratic Casimir of the 15-generator Wigner `su(4)` representation on `SpinPair`. -/
def su4Casimir : SpinPair := su4CasimirOf pauliTripleM2C

/-- Exact Wigner `su(4)` Casimir eigenvalue `15/4` in the fundamental 4D representation. -/
theorem su4Casimir_eq_fifteen_fourths :
    su4Casimir = (15 / 4 : ℂ) • (1 : SpinPair) := by
  unfold su4Casimir
  exact su4CasimirOf_eq_fifteen_fourths pauliTripleM2C

/-- Reconciles `su4Casimir` (`15/4`) with `su4_tensor_casimir_value` (`33/16`) and `su4_normalized_casimir` (`15/8`). -/
theorem su4Casimir_reconciles_normalizations :
    su4Casimir = (2 : ℂ) •
      ((su4Spin1 * su4Spin1 + su4Spin2 * su4Spin2 + su4Spin3 * su4Spin3) +
       (su4Iso1 * su4Iso1 + su4Iso2 * su4Iso2 + su4Iso3 * su4Iso3) +
       (su4GT11 * su4GT11 + su4GT12 * su4GT12 + su4GT13 * su4GT13 +
        su4GT21 * su4GT21 + su4GT22 * su4GT22 + su4GT23 * su4GT23 +
        su4GT31 * su4GT31 + su4GT32 * su4GT32 + su4GT33 * su4GT33)) ∧
    su4Casimir =
      (spinGen1 * spinGen1 + spinGen2 * spinGen2 + spinGen3 * spinGen3) +
      (isospinGen1 * isospinGen1 + isospinGen2 * isospinGen2 + isospinGen3 * isospinGen3) +
      (4 : ℂ) •
        ((spinGen1 * isospinGen1) * (spinGen1 * isospinGen1) +
         (spinGen1 * isospinGen2) * (spinGen1 * isospinGen2) +
         (spinGen1 * isospinGen3) * (spinGen1 * isospinGen3) +
         (spinGen2 * isospinGen1) * (spinGen2 * isospinGen1) +
         (spinGen2 * isospinGen2) * (spinGen2 * isospinGen2) +
         (spinGen2 * isospinGen3) * (spinGen2 * isospinGen3) +
         (spinGen3 * isospinGen1) * (spinGen3 * isospinGen1) +
         (spinGen3 * isospinGen2) * (spinGen3 * isospinGen2) +
         (spinGen3 * isospinGen3) * (spinGen3 * isospinGen3)) := by
  rw [su4Casimir_eq_fifteen_fourths, su4_normalized_casimir, spin_factor_casimir,
    isospin_factor_casimir, gamow_teller_sq_sum]
  constructor <;> module

theorem spinGenVec_comm (i j : Fin 3) :
    pairBracket (spinGenVec i) (spinGenVec j) =
      Complex.I • ∑ k : Fin 3, leviCivita ℂ i j k • spinGenVec k := by
  unfold pairBracket spinGenVec
  exact su4SpinGen_comm pauliTripleM2C i j

theorem isospinGenVec_comm (i j : Fin 3) :
    pairBracket (isospinGenVec i) (isospinGenVec j) =
      Complex.I • ∑ k : Fin 3, leviCivita ℂ i j k • isospinGenVec k := by
  unfold pairBracket isospinGenVec
  exact su4IsospinGen_comm pauliTripleM2C i j

theorem spinGenVec_isospinGenVec_comm (i j : Fin 3) :
    pairBracket (spinGenVec i) (isospinGenVec j) = 0 := by
  unfold pairBracket spinGenVec isospinGenVec
  exact su4SpinGen_isospinGen_comm pauliTripleM2C i j

theorem spinGenVec_gamowTellerGen_comm (i j k : Fin 3) :
    pairBracket (spinGenVec i) (gamowTellerGen j k) =
      Complex.I • ∑ l : Fin 3, leviCivita ℂ i j l • gamowTellerGen l k := by
  unfold pairBracket spinGenVec gamowTellerGen
  exact su4SpinGen_gamowTellerGen_comm pauliTripleM2C i j k

theorem isospinGenVec_gamowTellerGen_comm (j i k : Fin 3) :
    pairBracket (isospinGenVec j) (gamowTellerGen i k) =
      Complex.I • ∑ l : Fin 3, leviCivita ℂ j k l • gamowTellerGen i l := by
  unfold pairBracket isospinGenVec gamowTellerGen
  exact su4IsospinGen_gamowTellerGen_comm pauliTripleM2C j i k

theorem gamowTellerGen_comm (i j k l : Fin 3) :
    pairBracket (gamowTellerGen i j) (gamowTellerGen k l) =
      (if i = k then Complex.I • ∑ m : Fin 3, leviCivita ℂ j l m • isospinGenVec m else 0) +
      (if j = l then Complex.I • ∑ m : Fin 3, leviCivita ℂ i k m • spinGenVec m else 0) :=
  su4GamowTellerGen_comm pauliTripleM2C i j k l

/-- Canonical 15-element basis of `su(4)`: 3 spin, 3 isospin, and 9 Gamow--Teller generators. -/
def su4Generator (a : Fin 15) : SpinPair :=
  if ha : a.val < 3 then spinGenVec ⟨a.val, ha⟩
  else if ha6 : a.val < 6 then isospinGenVec ⟨a.val - 3, by omega⟩
  else gamowTellerGen ⟨(a.val - 6) / 3, by omega⟩ ⟨(a.val - 6) % 3, by omega⟩

private theorem su4Generator_spin (i : Fin 3) :
    su4Generator ⟨i.val, by omega⟩ = spinGenVec i := by
  have hi : i.val < 3 := i.isLt
  simp [su4Generator, hi]

private theorem su4Generator_isospin (j : Fin 3) :
    su4Generator ⟨j.val + 3, by omega⟩ = isospinGenVec j := by
  have h1 : ¬ (j.val + 3 < 3) := by omega
  have h2 : j.val + 3 < 6 := by omega
  simp [su4Generator, h1, h2]

private theorem su4Generator_gt (i j : Fin 3) :
    su4Generator ⟨6 + 3 * i.val + j.val, by omega⟩ = gamowTellerGen i j := by
  have h1 : ¬ (6 + 3 * i.val + j.val < 3) := by omega
  have h2 : ¬ (6 + 3 * i.val + j.val < 6) := by omega
  have hdiv : (6 + 3 * i.val + j.val - 6) / 3 = i.val := by omega
  have hmod : (6 + 3 * i.val + j.val - 6) % 3 = j.val := by omega
  simp [su4Generator, h1, h2, hdiv, hmod]

private lemma su4Generator_cases (a : Fin 15) :
    (∃ i : Fin 3, a = ⟨i.val, by omega⟩ ∧ su4Generator a = spinGenVec i) ∨
    (∃ j : Fin 3, a = ⟨j.val + 3, by omega⟩ ∧ su4Generator a = isospinGenVec j) ∨
    (∃ i j : Fin 3, a = ⟨6 + 3 * i.val + j.val, by omega⟩ ∧
      su4Generator a = gamowTellerGen i j) := by
  by_cases ha3 : a.val < 3
  · left; exact ⟨⟨a.val, ha3⟩, Fin.ext rfl, su4Generator_spin ⟨a.val, ha3⟩⟩
  · by_cases ha6 : a.val < 6
    · right; left
      have heq : (⟨a.val - 3 + 3, by omega⟩ : Fin 15) = a := Fin.ext (by dsimp; omega)
      have hsub := su4Generator_isospin ⟨a.val - 3, by omega⟩
      rw [heq] at hsub
      exact ⟨⟨a.val - 3, by omega⟩, heq.symm, hsub⟩
    · right; right
      have heq : (⟨6 + 3 * ((a.val - 6) / 3) + (a.val - 6) % 3, by omega⟩ : Fin 15) = a :=
        Fin.ext (by dsimp; omega)
      have hsub := su4Generator_gt ⟨(a.val - 6) / 3, by omega⟩ ⟨(a.val - 6) % 3, by omega⟩
      rw [heq] at hsub
      exact ⟨⟨(a.val - 6) / 3, by omega⟩, ⟨(a.val - 6) % 3, by omega⟩, heq.symm, hsub⟩

/-- The 15-generator family `su4Generator` is closed under the Lie bracket. -/
theorem su4Generator_lie_closed (a b : Fin 15) :
    ∃ c : Fin 15 → ℂ, pairBracket (su4Generator a) (su4Generator b) =
      ∑ k : Fin 15, c k • su4Generator k := by
  have hsum15 (g : Fin 15 → SpinPair) : (∑ m : Fin 15, g m) =
      g 0 + (g 1 + (g 2 + (g 3 + (g 4 + (g 5 + (g 6 + (g 7 + (g 8 + (g 9 + (g 10 +
        (g 11 + (g 12 + (g 13 + g 14))))))))))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  have ofSpinSum (f : Fin 3 → ℂ) :
      ∃ c : Fin 15 → ℂ, (∑ k : Fin 3, f k • spinGenVec k) = ∑ m : Fin 15, c m • su4Generator m := by
    refine ⟨fun m => if hm : m.val < 3 then f ⟨m.val, hm⟩ else 0, ?_⟩
    symm
    rw [hsum15, Fin.sum_univ_three]
    have hs0 : su4Generator 0 = spinGenVec 0 := su4Generator_spin 0
    have hs1 : su4Generator 1 = spinGenVec 1 := su4Generator_spin 1
    have hs2 : su4Generator 2 = spinGenVec 2 := su4Generator_spin 2
    simp only [show (0 : Fin 15).val < 3 by decide, show (1 : Fin 15).val < 3 by decide,
      show (2 : Fin 15).val < 3 by decide, show ¬(3 : Fin 15).val < 3 by decide,
      show ¬(4 : Fin 15).val < 3 by decide, show ¬(5 : Fin 15).val < 3 by decide,
      show ¬(6 : Fin 15).val < 3 by decide, show ¬(7 : Fin 15).val < 3 by decide,
      show ¬(8 : Fin 15).val < 3 by decide, show ¬(9 : Fin 15).val < 3 by decide,
      show ¬(10 : Fin 15).val < 3 by decide, show ¬(11 : Fin 15).val < 3 by decide,
      show ¬(12 : Fin 15).val < 3 by decide, show ¬(13 : Fin 15).val < 3 by decide,
      show ¬(14 : Fin 15).val < 3 by decide, dite_true, dite_false, zero_smul, add_zero,
      hs0, hs1, hs2]
    rfl
  have ofIsospinSum (f : Fin 3 → ℂ) :
      ∃ c : Fin 15 → ℂ, (∑ k : Fin 3, f k • isospinGenVec k) =
        ∑ m : Fin 15, c m • su4Generator m := by
    refine ⟨fun m => if hm : 3 ≤ m.val ∧ m.val < 6 then f ⟨m.val - 3, by omega⟩ else 0, ?_⟩
    symm
    rw [hsum15, Fin.sum_univ_three]
    have ht0 : su4Generator 3 = isospinGenVec 0 := su4Generator_isospin 0
    have ht1 : su4Generator 4 = isospinGenVec 1 := su4Generator_isospin 1
    have ht2 : su4Generator 5 = isospinGenVec 2 := su4Generator_isospin 2
    simp only [show ¬(3 ≤ (0 : Fin 15).val ∧ (0 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (1 : Fin 15).val ∧ (1 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (2 : Fin 15).val ∧ (2 : Fin 15).val < 6) by decide,
      show (3 ≤ (3 : Fin 15).val ∧ (3 : Fin 15).val < 6) by decide,
      show (3 ≤ (4 : Fin 15).val ∧ (4 : Fin 15).val < 6) by decide,
      show (3 ≤ (5 : Fin 15).val ∧ (5 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (6 : Fin 15).val ∧ (6 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (7 : Fin 15).val ∧ (7 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (8 : Fin 15).val ∧ (8 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (9 : Fin 15).val ∧ (9 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (10 : Fin 15).val ∧ (10 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (11 : Fin 15).val ∧ (11 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (12 : Fin 15).val ∧ (12 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (13 : Fin 15).val ∧ (13 : Fin 15).val < 6) by decide,
      show ¬(3 ≤ (14 : Fin 15).val ∧ (14 : Fin 15).val < 6) by decide,
      dite_false, zero_smul, zero_add, add_zero, ht0, ht1, ht2]
    rfl
  have ofGTSum (f : Fin 3 → Fin 3 → ℂ) :
      ∃ c : Fin 15 → ℂ, (∑ i : Fin 3, ∑ j : Fin 3, f i j • gamowTellerGen i j) =
        ∑ m : Fin 15, c m • su4Generator m := by
    refine ⟨fun m => if hm : 6 ≤ m.val then f ⟨(m.val - 6) / 3, by omega⟩
        ⟨(m.val - 6) % 3, by omega⟩ else 0, ?_⟩
    symm
    rw [hsum15]
    have hg00 : su4Generator 6 = gamowTellerGen 0 0 := su4Generator_gt 0 0
    have hg01 : su4Generator 7 = gamowTellerGen 0 1 := su4Generator_gt 0 1
    have hg02 : su4Generator 8 = gamowTellerGen 0 2 := su4Generator_gt 0 2
    have hg10 : su4Generator 9 = gamowTellerGen 1 0 := su4Generator_gt 1 0
    have hg11 : su4Generator 10 = gamowTellerGen 1 1 := su4Generator_gt 1 1
    have hg12 : su4Generator 11 = gamowTellerGen 1 2 := su4Generator_gt 1 2
    have hg20 : su4Generator 12 = gamowTellerGen 2 0 := su4Generator_gt 2 0
    have hg21 : su4Generator 13 = gamowTellerGen 2 1 := su4Generator_gt 2 1
    have hg22 : su4Generator 14 = gamowTellerGen 2 2 := su4Generator_gt 2 2
    simp only [show ¬(6 ≤ (0 : Fin 15).val) by decide, show ¬(6 ≤ (1 : Fin 15).val) by decide,
      show ¬(6 ≤ (2 : Fin 15).val) by decide, show ¬(6 ≤ (3 : Fin 15).val) by decide,
      show ¬(6 ≤ (4 : Fin 15).val) by decide, show ¬(6 ≤ (5 : Fin 15).val) by decide,
      show (6 ≤ (6 : Fin 15).val) by decide, show (6 ≤ (7 : Fin 15).val) by decide,
      show (6 ≤ (8 : Fin 15).val) by decide, show (6 ≤ (9 : Fin 15).val) by decide,
      show (6 ≤ (10 : Fin 15).val) by decide, show (6 ≤ (11 : Fin 15).val) by decide,
      show (6 ≤ (12 : Fin 15).val) by decide, show (6 ≤ (13 : Fin 15).val) by decide,
      show (6 ≤ (14 : Fin 15).val) by decide, dite_false, dite_true, zero_smul, zero_add,
      hg00, hg01, hg02, hg10, hg11, hg12, hg20, hg21, hg22]
    simp only [Fin.sum_univ_three]
    abel
  rcases su4Generator_cases a with ⟨i, _, ha⟩ | ⟨j, _, ha⟩ | ⟨i, j, _, ha⟩ <;>
    rcases su4Generator_cases b with ⟨i', _, hb⟩ | ⟨j', _, hb⟩ | ⟨k, l, _, hb⟩ <;>
    rw [ha, hb]
  · rw [spinGenVec_comm, Finset.smul_sum]
    simpa [smul_smul] using ofSpinSum (fun m => Complex.I * leviCivita ℂ i i' m)
  · rw [spinGenVec_isospinGenVec_comm]
    exact ⟨0, by simp⟩
  · rw [spinGenVec_gamowTellerGen_comm, Finset.smul_sum]
    simpa [smul_smul] using ofGTSum (fun p q => if q = l then Complex.I * leviCivita ℂ i k p else 0)
  · rw [show pairBracket (isospinGenVec j) (spinGenVec i') =
        -pairBracket (spinGenVec i') (isospinGenVec j) by unfold pairBracket tensorBracket; abel,
      spinGenVec_isospinGenVec_comm, neg_zero]
    exact ⟨0, by simp⟩
  · rw [isospinGenVec_comm, Finset.smul_sum]
    simpa [smul_smul] using ofIsospinSum (fun m => Complex.I * leviCivita ℂ j j' m)
  · rw [isospinGenVec_gamowTellerGen_comm, Finset.smul_sum]
    simpa [smul_smul] using ofGTSum (fun p q => if p = k then Complex.I * leviCivita ℂ j l q else 0)
  · rw [show pairBracket (gamowTellerGen i j) (spinGenVec i') =
        -pairBracket (spinGenVec i') (gamowTellerGen i j) by unfold pairBracket tensorBracket; abel,
      spinGenVec_gamowTellerGen_comm, Finset.smul_sum]
    have hex := ofGTSum (fun p q => if q = j then -(Complex.I * leviCivita ℂ i' i p) else 0)
    rcases hex with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single j (fun q _ hq => by simp [hq])
      (fun hj => False.elim (hj (Finset.mem_univ j)))]
    simp only [ite_true, smul_smul]
    exact (neg_smul (Complex.I * leviCivita ℂ i' i p) (gamowTellerGen p j)).symm
  · rw [show pairBracket (gamowTellerGen i j) (isospinGenVec j') =
        -pairBracket (isospinGenVec j') (gamowTellerGen i j) by unfold pairBracket tensorBracket; abel,
      isospinGenVec_gamowTellerGen_comm, Finset.smul_sum]
    have hex := ofGTSum (fun p q => if p = i then -(Complex.I * leviCivita ℂ j' j q) else 0)
    rcases hex with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, ← Finset.sum_neg_distrib]
    conv_rhs =>
      rw [Finset.sum_eq_single i (fun p _ hp => by simp [hp])
        (fun hi => False.elim (hi (Finset.mem_univ i)))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ite_true, smul_smul]
    exact (neg_smul (Complex.I * leviCivita ℂ j' j q) (gamowTellerGen i q)).symm
  · rw [gamowTellerGen_comm]
    rcases ofIsospinSum (fun m => if i = k then Complex.I * leviCivita ℂ j l m else 0) with ⟨c₁, hc₁⟩
    rcases ofSpinSum (fun m => if j = l then Complex.I * leviCivita ℂ i k m else 0) with ⟨c₂, hc₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← hc₁, ← hc₂]
    congr 1 <;> split_ifs <;> simp [Finset.smul_sum, smul_smul]

/-- The `su(4)` Casimir commutes with every generator. -/
theorem su4Casimir_comm_su4Generator (a : Fin 15) :
    pairBracket su4Casimir (su4Generator a) = 0 := by
  unfold pairBracket tensorBracket
  rw [su4Casimir_eq_fifteen_fourths, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sub_self]

/-- Non-commutativity witness for the `su(4)` tensor representation. -/
theorem su4_noncommutative_witness :
    spinGenVec 0 * gamowTellerGen 1 0 ≠ gamowTellerGen 1 0 * spinGenVec 0 := by
  intro h
  have h0 : pairBracket (spinGenVec 0) (gamowTellerGen 1 0) = 0 := sub_eq_zero.mpr h
  rw [spinGenVec_gamowTellerGen_comm] at h0
  simp only [Fin.sum_univ_three, leviCivita, zero_smul, one_smul, add_zero, zero_add] at h0
  have h1 : gamowTellerGen 2 0 = 0 := by
    have := congrArg (fun x => (-Complex.I) • x) h0
    simpa [smul_smul, Complex.I_mul_I] using this
  have h2 : gamowTellerGen 2 0 * gamowTellerGen 2 0 = 0 := by rw [h1, zero_mul]
  rw [gamowTellerGen_sq] at h2
  have hcoeff : (1 / 4 : ℂ) = 0 := by
    have hnot : (1 : SpinPair) ≠ 0 := one_ne_zero
    exact (smul_eq_zero.mp h2).resolve_right hnot
  norm_num at hcoeff

/-- Normalized trace functional on `SpinPair = M₂(ℂ) ⊗ M₂(ℂ)`: `pairTrace (A ⊗ₜ B) = ¼ Tr(A) Tr(B)`. -/
def pairTrace : SpinPair →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun := fun A =>
        { toFun := fun B => (1 / 4 : ℂ) * Matrix.trace A * Matrix.trace B
          map_add' := fun B₁ B₂ => by simp [Matrix.trace_add]; ring
          map_smul' := fun c B => by simp [Matrix.trace_smul]; ring }
      map_add' := fun A₁ A₂ => by
        ext B; simp [Matrix.trace_add]; ring
      map_smul' := fun c A => by
        ext B; simp [Matrix.trace_smul]; ring }

@[simp] theorem pairTrace_tmul (A B : M2C) :
    pairTrace (A ⊗ₜ[ℂ] B) = (1 / 4 : ℂ) * Matrix.trace A * Matrix.trace B := by
  simp [pairTrace]

private theorem pauliBasis_trace (i : Fin 3) : Matrix.trace (pauliBasis i) = 0 := by
  fin_cases i <;>
    simp [pauliBasis, I₁, I₂, I₃, σPlus, σMinus, σ3c, Matrix.trace, Fin.sum_univ_two]

private theorem pauliBasis_mul (i j : Fin 3) :
    pauliBasis i * pauliBasis j =
      if i = j then (1 : M2C)
      else Complex.I • ∑ k : Fin 3, leviCivita ℂ i j k • pauliBasis k := by
  fin_cases i <;> fin_cases j <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [pauliBasis, I₁, I₂, I₃, σPlus, σMinus, σ3c, leviCivita,
      Fin.sum_univ_three, Complex.I_mul_I]

private theorem trace_pauliBasis_mul (i j : Fin 3) :
    Matrix.trace (pauliBasis i * pauliBasis j) = if i = j then 2 else 0 := by
  rw [pauliBasis_mul]
  split_ifs with h
  · simp [Matrix.trace]
  · simp [Matrix.trace_smul, Matrix.trace_sum, pauliBasis_trace]

private theorem pairTrace_su4Generator_mul (a b : Fin 15) :
    pairTrace (su4Generator a * su4Generator b) = if a = b then (1 / 4 : ℂ) else 0 := by
  have h1 : Matrix.trace (1 : M2C) = 2 := by simp [Matrix.trace]
  rcases su4Generator_cases a with ⟨i, ha_eq, ha⟩ | ⟨j, ha_eq, ha⟩ | ⟨i, j, ha_eq, ha⟩ <;>
    rcases su4Generator_cases b with ⟨i', hb_eq, hb⟩ | ⟨j', hb_eq, hb⟩ | ⟨k, l, hb_eq, hb⟩
  · rw [ha, hb]
    unfold spinGenVec su4SpinGen pauliTripleM2C
    rw [smul_mul_smul, tmul_mul_tmul, mul_one, map_smul, pairTrace_tmul,
      trace_pauliBasis_mul, h1]
    have hab : (a = b) ↔ (i = i') := by rw [ha_eq, hb_eq]; simp [Fin.ext_iff]
    split_ifs <;> (simp_all; try norm_num)
  · rw [ha, hb]
    unfold spinGenVec isospinGenVec su4SpinGen su4IsospinGen pauliTripleM2C
    rw [smul_mul_smul, tmul_mul_tmul, mul_one, one_mul, map_smul, pairTrace_tmul,
      pauliBasis_trace, pauliBasis_trace]
    have hne : a ≠ b := by rw [ha_eq, hb_eq]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hne]
  · rw [ha, hb]
    unfold spinGenVec su4SpinGen pauliTripleM2C
    rw [gamowTellerGen_eq_tmul, smul_mul_smul, tmul_mul_tmul, one_mul, map_smul, pairTrace_tmul,
      pauliBasis_trace]
    have hne : a ≠ b := by rw [ha_eq, hb_eq]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hne]
  · rw [ha, hb]
    unfold isospinGenVec spinGenVec su4IsospinGen su4SpinGen pauliTripleM2C
    rw [smul_mul_smul, tmul_mul_tmul, one_mul, mul_one, map_smul, pairTrace_tmul,
      pauliBasis_trace, pauliBasis_trace]
    have hne : a ≠ b := by rw [ha_eq, hb_eq]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hne]
  · rw [ha, hb]
    unfold isospinGenVec su4IsospinGen pauliTripleM2C
    rw [smul_mul_smul, tmul_mul_tmul, one_mul, map_smul, pairTrace_tmul,
      trace_pauliBasis_mul, h1]
    have hab : (a = b) ↔ (j = j') := by rw [ha_eq, hb_eq]; simp [Fin.ext_iff]
    split_ifs <;> (simp_all; try norm_num)
  · rw [ha, hb]
    unfold isospinGenVec su4IsospinGen pauliTripleM2C
    rw [gamowTellerGen_eq_tmul, smul_mul_smul, tmul_mul_tmul, one_mul, map_smul, pairTrace_tmul,
      pauliBasis_trace]
    have hne : a ≠ b := by rw [ha_eq, hb_eq]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hne]
  · rw [ha, hb]
    unfold spinGenVec su4SpinGen pauliTripleM2C
    rw [gamowTellerGen_eq_tmul, smul_mul_smul, tmul_mul_tmul, mul_one, map_smul, pairTrace_tmul,
      pauliBasis_trace]
    have hne : a ≠ b := by rw [ha_eq, hb_eq]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hne]
  · rw [ha, hb]
    unfold isospinGenVec su4IsospinGen pauliTripleM2C
    rw [gamowTellerGen_eq_tmul, smul_mul_smul, tmul_mul_tmul, mul_one, map_smul, pairTrace_tmul,
      pauliBasis_trace]
    have hne : a ≠ b := by rw [ha_eq, hb_eq]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hne]
  · rw [ha, hb]
    rw [gamowTellerGen_eq_tmul, gamowTellerGen_eq_tmul, smul_mul_smul, tmul_mul_tmul, map_smul,
      pairTrace_tmul, trace_pauliBasis_mul, trace_pauliBasis_mul]
    have hab : (a = b) ↔ (i = k ∧ j = l) := by
      rw [ha_eq, hb_eq]; simp [Fin.ext_iff]; omega
    split_ifs <;> (simp_all; try norm_num)

/-- The 15 `su(4)` generators are linearly independent over `ℂ`. -/
theorem su4Generator_linearIndependent : LinearIndependent ℂ su4Generator := by
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have htrace := congrArg (fun x => pairTrace (su4Generator b * x)) hc
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    pairTrace_su4Generator_mul] at htrace
  have hsum : (∑ a : Fin 15, c a * if b = a then (1 / 4 : ℂ) else 0) = c b * (1 / 4 : ℂ) := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro a _ hab; simp [Ne.symm hab]
    · intro hb; exact False.elim (hb (Finset.mem_univ b))
  have hcb : c b * (1 / 4 : ℂ) = 0 := by simpa [smul_eq_mul, hsum] using htrace
  exact (mul_eq_zero.mp hcb).resolve_right (by norm_num)

def singletProjector : SpinPair := singletProjectorOf pauliTripleM2C
def tripletProjector : SpinPair := tripletProjectorOf pauliTripleM2C
def swapSpinPair : SpinPair := swapOf pauliTripleM2C

/-- The spin-singlet projector equals `½ spinTwist e` where `e` is `ChiralTensorRecoupling.e`. -/
theorem singletProjector_eq_spinTwist_e :
    singletProjector = (1 / 2 : ℂ) • spinTwist ChiralTensorRecoupling.e := by
  have h_twist_X : spinTwist ChiralTensorRecoupling.X = -(σPlus ⊗ₜ[ℂ] σMinus) := by
    unfold spinTwist spinChirality spinAction ChiralTensorRecoupling.X
    rw [tmul_mul_tmul, tmul_mul_tmul, mul_one, one_mul, σ3c_mul_σPlus, σPlus_mul_σ3c,
      ← TensorProduct.neg_tmul]
  have h_twist_Y : spinTwist ChiralTensorRecoupling.Y = -(σMinus ⊗ₜ[ℂ] σPlus) := by
    unfold spinTwist spinChirality spinAction ChiralTensorRecoupling.Y
    rw [tmul_mul_tmul, tmul_mul_tmul, mul_one, one_mul, σ3c_mul_σMinus, neg_mul, σMinus_mul_σ3c,
      ← TensorProduct.neg_tmul]
  have h_twist_Z : spinTwist ChiralTensorRecoupling.Z = ChiralTensorRecoupling.Z := by
    unfold spinTwist spinChirality spinAction ChiralTensorRecoupling.Z
    rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, tmul_mul_tmul, tmul_mul_tmul,
      tmul_mul_tmul, tmul_mul_tmul]
    simp only [mul_one, one_mul, σ3c_sq]
  have h_twist_e :
      spinTwist ChiralTensorRecoupling.e =
        -(ChiralTensorRecoupling.X + ChiralTensorRecoupling.Y) + ChiralTensorRecoupling.Z := by
    unfold spinTwist
    rw [ChiralTensorRecoupling.e_eq_X_add_Y_add_Z, mul_add, mul_add, add_mul, add_mul]
    change spinTwist ChiralTensorRecoupling.X + spinTwist ChiralTensorRecoupling.Y +
        spinTwist ChiralTensorRecoupling.Z = _
    rw [h_twist_X, h_twist_Y, h_twist_Z]
    unfold ChiralTensorRecoupling.X ChiralTensorRecoupling.Y
    abel
  have h_p12 :
      pauliBasis 0 ⊗ₜ[ℂ] pauliBasis 0 + pauliBasis 1 ⊗ₜ[ℂ] pauliBasis 1 =
        (2 : ℂ) • (ChiralTensorRecoupling.X + ChiralTensorRecoupling.Y) := by
    unfold pauliBasis I₁ I₂ ChiralTensorRecoupling.X ChiralTensorRecoupling.Y
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
      smul_add, smul_sub, smul_smul, neg_smul, one_smul, Complex.I_mul_I]
    rw [two_smul ℂ, two_smul ℂ]
    abel
  rw [h_twist_e]
  unfold singletProjector singletProjectorOf pauliTripleM2C
  dsimp only
  rw [Fin.sum_univ_three, h_p12]
  unfold ChiralTensorRecoupling.Z pauliBasis I₃
  simp only [smul_add, smul_sub, smul_smul]
  module

theorem singletProjector_idem : singletProjector * singletProjector = singletProjector := by
  unfold singletProjector
  exact singletProjectorOf_idem pauliTripleM2C

theorem tripletProjector_idem : tripletProjector * tripletProjector = tripletProjector := by
  unfold tripletProjector
  exact tripletProjectorOf_idem pauliTripleM2C

theorem singlet_mul_triplet : singletProjector * tripletProjector = 0 := by
  unfold singletProjector tripletProjector
  exact singletOf_mul_tripletOf pauliTripleM2C

theorem triplet_mul_singlet : tripletProjector * singletProjector = 0 := by
  unfold tripletProjector singletProjector
  exact tripletOf_mul_singletOf pauliTripleM2C

theorem singlet_add_triplet : singletProjector + tripletProjector = (1 : SpinPair) := by
  unfold singletProjector tripletProjector
  exact singletOf_add_tripletOf pauliTripleM2C

/-- Total two-strand spin Casimir on `SpinPair`, separating `S = 0` from `S = 1`. -/
def twoStrandSpinCasimir : SpinPair := twoStrandSpinCasimirOf pauliTripleM2C

theorem twoStrandSpinCasimir_eq_two_triplet :
    twoStrandSpinCasimir = (2 : ℂ) • tripletProjector := by
  unfold twoStrandSpinCasimir tripletProjector
  exact twoStrandSpinCasimirOf_eq_two_triplet pauliTripleM2C

abbrev TwoNucleonSpinIsospin := SpinPair ⊗[ℂ] SpinPair

def pairingChannel00 : TwoNucleonSpinIsospin := pairingChannel00Of pauliTripleM2C
def pairingChannel01 : TwoNucleonSpinIsospin := pairingChannel01Of pauliTripleM2C
def pairingChannel10 : TwoNucleonSpinIsospin := pairingChannel10Of pauliTripleM2C
def pairingChannel11 : TwoNucleonSpinIsospin := pairingChannel11Of pauliTripleM2C
def wignerPairing6A : TwoNucleonSpinIsospin := wignerPairing6AOf pauliTripleM2C
def wignerPairing10S : TwoNucleonSpinIsospin := wignerPairing10SOf pauliTripleM2C
def twoNucleonSU4Casimir : TwoNucleonSpinIsospin := twoNucleonSU4CasimirOf pauliTripleM2C

theorem twoNucleonSU4Casimir_mul_wignerPairing6A :
    twoNucleonSU4Casimir * wignerPairing6A = (5 : ℂ) • wignerPairing6A := by
  unfold twoNucleonSU4Casimir wignerPairing6A
  exact twoNucleonSU4CasimirOf_mul_wignerPairing6AOf pauliTripleM2C

theorem twoNucleonSU4Casimir_mul_wignerPairing10S :
    twoNucleonSU4Casimir * wignerPairing10S = (9 : ℂ) • wignerPairing10S := by
  unfold twoNucleonSU4Casimir wignerPairing10S
  exact twoNucleonSU4CasimirOf_mul_wignerPairing10SOf pauliTripleM2C

theorem wignerPairing6A_idem : wignerPairing6A * wignerPairing6A = wignerPairing6A := by
  unfold wignerPairing6A
  exact wignerPairing6AOf_idem pauliTripleM2C

theorem wignerPairing10S_idem : wignerPairing10S * wignerPairing10S = wignerPairing10S := by
  unfold wignerPairing10S
  exact wignerPairing10SOf_idem pauliTripleM2C

theorem wignerPairing6A_mul_10S : wignerPairing6A * wignerPairing10S = 0 := by
  unfold wignerPairing6A wignerPairing10S
  exact wignerPairing6AOf_mul_10SOf pauliTripleM2C

theorem wignerPairing6A_add_10S :
    wignerPairing6A + wignerPairing10S = (1 : TwoNucleonSpinIsospin) := by
  unfold wignerPairing6A wignerPairing10S
  exact wignerPairing6AOf_add_10SOf pauliTripleM2C

def twoNucleonGen1 (a : Fin 15) : TwoNucleonSpinIsospin :=
  if ha : a.val < 3 then spinGenVec ⟨a.val, ha⟩ ⊗ₜ[ℂ] (1 : SpinPair)
  else if ha6 : a.val < 6 then (1 : SpinPair) ⊗ₜ[ℂ] spinGenVec ⟨a.val - 3, by omega⟩
  else (1 / 2 : ℂ) • (spinAction (pauliBasis ⟨(a.val - 6) / 3, by omega⟩) ⊗ₜ[ℂ]
    spinAction (pauliBasis ⟨(a.val - 6) % 3, by omega⟩))

def twoNucleonGen2 (a : Fin 15) : TwoNucleonSpinIsospin :=
  if ha : a.val < 3 then isospinGenVec ⟨a.val, ha⟩ ⊗ₜ[ℂ] (1 : SpinPair)
  else if ha6 : a.val < 6 then (1 : SpinPair) ⊗ₜ[ℂ] isospinGenVec ⟨a.val - 3, by omega⟩
  else (1 / 2 : ℂ) • (isospinAction (pauliBasis ⟨(a.val - 6) / 3, by omega⟩) ⊗ₜ[ℂ]
    isospinAction (pauliBasis ⟨(a.val - 6) % 3, by omega⟩))

def totalTwoNucleonGen (a : Fin 15) : TwoNucleonSpinIsospin :=
  twoNucleonGen1 a + twoNucleonGen2 a

private theorem swapSpinPair_comm_sym (A : M2C) :
    swapSpinPair * (spinAction A + isospinAction A) =
      (spinAction A + isospinAction A) * swapSpinPair := by
  have hexp : A = ((1 / 2 : ℂ) * Matrix.trace A) • (1 : M2C) +
      ∑ k : Fin 3, ((1 / 2 : ℂ) * Matrix.trace (A * pauliBasis k)) • pauliBasis k := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      (simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
        pauliBasis, I₁, I₂, I₃, σPlus, σMinus, σ3c];
       ring_nf;
       try rw [Complex.I_sq]
       try ring)
  have h1 : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (spinAction A + isospinAction A) =
      (spinAction A + isospinAction A) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) := by
    rw [← Algebra.TensorProduct.one_def, one_mul, mul_one]
  let S : SpinPair := ∑ i : Fin 3, pauliBasis i ⊗ₜ[ℂ] pauliBasis i
  have hbasis : ∀ k : Fin 3,
      S * (spinAction (pauliBasis k) + isospinAction (pauliBasis k)) -
      (spinAction (pauliBasis k) + isospinAction (pauliBasis k)) * S = 0 := by
    intro k
    dsimp [S]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hterm (i : Fin 3) :
        (pauliBasis i ⊗ₜ[ℂ] pauliBasis i) *
          (spinAction (pauliBasis k) + isospinAction (pauliBasis k)) -
        (spinAction (pauliBasis k) + isospinAction (pauliBasis k)) *
          (pauliBasis i ⊗ₜ[ℂ] pauliBasis i) =
        (pauliBasis i * pauliBasis k - pauliBasis k * pauliBasis i) ⊗ₜ[ℂ] pauliBasis i +
        pauliBasis i ⊗ₜ[ℂ] (pauliBasis i * pauliBasis k - pauliBasis k * pauliBasis i) := by
      unfold spinAction isospinAction
      rw [mul_add, add_mul, tmul_mul_tmul, tmul_mul_tmul, tmul_mul_tmul, tmul_mul_tmul,
        mul_one, one_mul]
      simp only [sub_tmul, tmul_sub]
      abel
    simp_rw [hterm, pauliBasis_comm]
    fin_cases k <;>
      simp [leviCivita, Fin.sum_univ_three, neg_one_zsmul,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul,
        TensorProduct.neg_tmul, TensorProduct.tmul_neg]
  have hcomm_one :
      S * (spinAction (1 : M2C) + isospinAction (1 : M2C)) -
      (spinAction (1 : M2C) + isospinAction (1 : M2C)) * S = 0 := by
    unfold spinAction isospinAction
    dsimp [S]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [mul_add, add_mul, tmul_mul_tmul, mul_one, one_mul, sub_self]
  have h1_comm : S * (spinAction (1 : M2C) + isospinAction (1 : M2C)) =
      (spinAction (1 : M2C) + isospinAction (1 : M2C)) * S := sub_eq_zero.mp hcomm_one
  have hk_comm (k : Fin 3) : S * (spinAction (pauliBasis k) + isospinAction (pauliBasis k)) =
      (spinAction (pauliBasis k) + isospinAction (pauliBasis k)) * S := sub_eq_zero.mp (hbasis k)
  have hswap :
      S * (spinAction A + isospinAction A) =
      (spinAction A + isospinAction A) * S := by
    rw [hexp]
    have hsp : spinAction (((1 / 2 : ℂ) * Matrix.trace A) • (1 : M2C) +
        ∑ k : Fin 3, ((1 / 2 : ℂ) * Matrix.trace (A * pauliBasis k)) • pauliBasis k) +
      isospinAction (((1 / 2 : ℂ) * Matrix.trace A) • (1 : M2C) +
        ∑ k : Fin 3, ((1 / 2 : ℂ) * Matrix.trace (A * pauliBasis k)) • pauliBasis k) =
      ((1 / 2 : ℂ) * Matrix.trace A) • (spinAction (1 : M2C) + isospinAction (1 : M2C)) +
      ∑ k : Fin 3, ((1 / 2 : ℂ) * Matrix.trace (A * pauliBasis k)) •
        (spinAction (pauliBasis k) + isospinAction (pauliBasis k)) := by
      unfold spinAction isospinAction
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
        Finset.sum_add_distrib, smul_add]
      abel_nf
    rw [hsp, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h1_comm,
      Finset.mul_sum Finset.univ _ S, Finset.sum_mul Finset.univ _ S]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hk_comm]
  unfold swapSpinPair swapOf pauliTripleM2C
  dsimp only
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  have h1s : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (spinAction A + isospinAction A) =
      (spinAction A + isospinAction A) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) := h1
  have htotal :
      ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) + S) * (spinAction A + isospinAction A) =
        (spinAction A + isospinAction A) *
          ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) + S) := by
    calc
      ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) + S) * (spinAction A + isospinAction A) =
          ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (spinAction A + isospinAction A) +
            S * (spinAction A + isospinAction A) := by rw [add_mul]
      _ = (spinAction A + isospinAction A) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) +
            (spinAction A + isospinAction A) * S := by rw [h1s, hswap]
      _ = (spinAction A + isospinAction A) *
          ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) + S) := by rw [mul_add]
  simpa [S, add_mul, mul_add] using htotal

private theorem swapSpinPair_anticomm_antisym (i : Fin 3) :
    swapSpinPair * (spinAction (pauliBasis i) - isospinAction (pauliBasis i)) =
      -((spinAction (pauliBasis i) - isospinAction (pauliBasis i)) * swapSpinPair) := by
  have hm01 : pauliBasis 0 * pauliBasis 1 = Complex.I • pauliBasis 2 := by
    simp [pauliBasis_mul, leviCivita, Fin.sum_univ_three]
  have hm10 : pauliBasis 1 * pauliBasis 0 = -(Complex.I • pauliBasis 2) := by
    simp [pauliBasis_mul, leviCivita, Fin.sum_univ_three]
  have hm02 : pauliBasis 0 * pauliBasis 2 = -(Complex.I • pauliBasis 1) := by
    simp [pauliBasis_mul, leviCivita, Fin.sum_univ_three]
  have hm20 : pauliBasis 2 * pauliBasis 0 = Complex.I • pauliBasis 1 := by
    simp [pauliBasis_mul, leviCivita, Fin.sum_univ_three]
  have hm12 : pauliBasis 1 * pauliBasis 2 = Complex.I • pauliBasis 0 := by
    simp [pauliBasis_mul, leviCivita, Fin.sum_univ_three]
  have hm21 : pauliBasis 2 * pauliBasis 1 = -(Complex.I • pauliBasis 0) := by
    simp [pauliBasis_mul, leviCivita, Fin.sum_univ_three]
  rcases (by fin_cases i <;> simp : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  all_goals
    apply eq_neg_of_add_eq_zero_left
    unfold swapSpinPair swapOf pauliTripleM2C spinAction isospinAction
    dsimp only
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add]
    apply smul_eq_zero_of_right
    simp [Fin.sum_univ_three, add_mul, mul_add, sub_mul, mul_sub, tmul_mul_tmul,
      one_mul, mul_one, pauliBasis_sq, neg_one_zsmul,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg,
      hm01, hm10, hm02, hm20, hm12, hm21]
    abel

private theorem tensor_split_comm_swap {R : Type*} [Ring R] [Algebra ℂ R]
    (si ti sj tj s : R)
    (hc_i : (si + ti) * s = s * (si + ti))
    (hc_j : (sj + tj) * s = s * (sj + tj))
    (ha_i : (si - ti) * s = -(s * (si - ti)))
    (ha_j : (sj - tj) * s = -(s * (sj - tj))) :
    ((1 / 2 : ℂ) • (si ⊗ₜ[ℂ] sj) + (1 / 2 : ℂ) • (ti ⊗ₜ[ℂ] tj)) * (s ⊗ₜ[ℂ] s) =
      (s ⊗ₜ[ℂ] s) * ((1 / 2 : ℂ) • (si ⊗ₜ[ℂ] sj) + (1 / 2 : ℂ) • (ti ⊗ₜ[ℂ] tj)) := by
  have hsum_sq : (si + ti) ⊗ₜ[ℂ] (sj + tj) + (si - ti) ⊗ₜ[ℂ] (sj - tj) =
      (2 : ℂ) • (si ⊗ₜ[ℂ] sj + ti ⊗ₜ[ℂ] tj) := by
    simp only [add_tmul, tmul_add, sub_tmul, tmul_sub, two_smul]
    abel
  have hsplit : (1 / 2 : ℂ) • (si ⊗ₜ[ℂ] sj) + (1 / 2 : ℂ) • (ti ⊗ₜ[ℂ] tj) =
      (1 / 4 : ℂ) • ((si + ti) ⊗ₜ[ℂ] (sj + tj) + (si - ti) ⊗ₜ[ℂ] (sj - tj)) := by
    rw [hsum_sq, smul_smul, ← smul_add]
    congr 1
    norm_num
  rw [hsplit, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, tmul_mul_tmul, tmul_mul_tmul,
    tmul_mul_tmul, tmul_mul_tmul, hc_i, hc_j, ha_i, ha_j, neg_tmul, tmul_neg, neg_neg]

private theorem comm_one_sub_ring {R : Type*} [Ring R] [Algebra ℂ R]
    (c : ℂ) (x y : R) (h : x * y = y * x) :
    x * (c • (1 - y)) = (c • (1 - y)) * x := by
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, h]

/-- Every total two-nucleon `su(4)` generator commutes with the `6_A` supermultiplet projector,
while the Gamow--Teller generator mixes `(S=0, T=1) ↔ (S=1, T=0)` inside `6_A`. -/
theorem totalTwoNucleonGen_comm_wignerPairing6A (a : Fin 15) :
    totalTwoNucleonGen a * wignerPairing6A = wignerPairing6A * totalTwoNucleonGen a := by
  have hw6 : wignerPairing6A =
      (1 / 2 : ℂ) • ((1 : TwoNucleonSpinIsospin) - swapSpinPair ⊗ₜ[ℂ] swapSpinPair) := by
    unfold wignerPairing6A wignerPairing6AOf pairingChannel01Of pairingChannel10Of
    change (singletProjector ⊗ₜ[ℂ] tripletProjector + tripletProjector ⊗ₜ[ℂ] singletProjector) = _
    have hsw : swapSpinPair = tripletProjector - singletProjector :=
      swapOf_eq_triplet_sub_singlet pauliTripleM2C
    have h1 : (1 : SpinPair) = singletProjector + tripletProjector := singlet_add_triplet.symm
    have hdiff :
        (singletProjector + tripletProjector) ⊗ₜ[ℂ] (singletProjector + tripletProjector) -
          (tripletProjector - singletProjector) ⊗ₜ[ℂ] (tripletProjector - singletProjector) =
          (2 : ℂ) • (singletProjector ⊗ₜ[ℂ] tripletProjector +
            tripletProjector ⊗ₜ[ℂ] singletProjector) := by
      simp only [add_tmul, tmul_add, sub_tmul, tmul_sub, two_smul]
      abel
    rw [hsw, Algebra.TensorProduct.one_def, h1, hdiff, smul_smul]
    norm_num
  rw [hw6]
  refine comm_one_sub_ring (1 / 2 : ℂ) (totalTwoNucleonGen a)
    (swapSpinPair ⊗ₜ[ℂ] swapSpinPair) ?_
  have hcomm_spin (i : Fin 3) :
      (spinGenVec i + isospinGenVec i) * swapSpinPair =
        swapSpinPair * (spinGenVec i + isospinGenVec i) := by
    unfold spinGenVec isospinGenVec su4SpinGen su4IsospinGen pauliTripleM2C
    dsimp only
    change ((1 / 2 : ℂ) • spinAction (pauliBasis i) +
        (1 / 2 : ℂ) • isospinAction (pauliBasis i)) * swapSpinPair =
      swapSpinPair * ((1 / 2 : ℂ) • spinAction (pauliBasis i) +
        (1 / 2 : ℂ) • isospinAction (pauliBasis i))
    rw [← smul_add, smul_mul_assoc, mul_smul_comm, (swapSpinPair_comm_sym (pauliBasis i)).symm]
  unfold totalTwoNucleonGen twoNucleonGen1 twoNucleonGen2
  by_cases ha3 : a.val < 3
  · simp only [ha3, dite_true, ← TensorProduct.add_tmul, tmul_mul_tmul, one_mul, mul_one,
      hcomm_spin]
  · by_cases ha6 : a.val < 6
    · simp only [ha3, ha6, dite_false, dite_true, ← TensorProduct.tmul_add, tmul_mul_tmul,
        one_mul, mul_one, hcomm_spin]
    · simp only [ha3, ha6, dite_false]
      set i : Fin 3 := ⟨(a.val - 6) / 3, by omega⟩
      set j : Fin 3 := ⟨(a.val - 6) % 3, by omega⟩
      have hc_i : (spinAction (pauliBasis i) + isospinAction (pauliBasis i)) * swapSpinPair =
          swapSpinPair * (spinAction (pauliBasis i) + isospinAction (pauliBasis i)) :=
        (swapSpinPair_comm_sym (pauliBasis i)).symm
      have hc_j : (spinAction (pauliBasis j) + isospinAction (pauliBasis j)) * swapSpinPair =
          swapSpinPair * (spinAction (pauliBasis j) + isospinAction (pauliBasis j)) :=
        (swapSpinPair_comm_sym (pauliBasis j)).symm
      have ha_i : (spinAction (pauliBasis i) - isospinAction (pauliBasis i)) * swapSpinPair =
          -(swapSpinPair * (spinAction (pauliBasis i) - isospinAction (pauliBasis i))) := by
        have h := congrArg Neg.neg (swapSpinPair_anticomm_antisym i)
        simp only [neg_neg] at h
        exact h.symm
      have ha_j : (spinAction (pauliBasis j) - isospinAction (pauliBasis j)) * swapSpinPair =
          -(swapSpinPair * (spinAction (pauliBasis j) - isospinAction (pauliBasis j))) := by
        have h := congrArg Neg.neg (swapSpinPair_anticomm_antisym j)
        simp only [neg_neg] at h
        exact h.symm
      exact tensor_split_comm_swap (spinAction (pauliBasis i)) (isospinAction (pauliBasis i))
        (spinAction (pauliBasis j)) (isospinAction (pauliBasis j)) swapSpinPair
        hc_i hc_j ha_i ha_j

private theorem tensor_pair_sandwich {R : Type*} [Ring R] [Algebra ℂ R]
    (p1 q1 a b p2 q2 : R) :
    (p1 ⊗ₜ[ℂ] q1) * ((a ⊗ₜ[ℂ] a + b ⊗ₜ[ℂ] b) * (p2 ⊗ₜ[ℂ] q2)) =
      (p1 * a * p2) ⊗ₜ[ℂ] (q1 * a * q2) + (p1 * b * p2) ⊗ₜ[ℂ] (q1 * b * q2) := by
  rw [add_mul, mul_add, tmul_mul_tmul, tmul_mul_tmul, tmul_mul_tmul, tmul_mul_tmul]
  simp only [mul_assoc]

/-- Obstruction-driven mixing: the Gamow--Teller generator `totalTwoNucleonGen 6` (`Y_{00}`)
does NOT commute with the individual `(S=0, T=1)` pairing channel `pairingChannel01`,
instead mixing `(S=0, T=1) ↔ (S=1, T=0)` inside the `6_A` supermultiplet. -/
theorem gamowTeller_mixes_pairingChannel01_to_10 :
    pairingChannel10 * totalTwoNucleonGen 6 * pairingChannel01 ≠ 0 := by
  have h01 : pairingChannel01 = singletProjector ⊗ₜ[ℂ] tripletProjector := rfl
  have h10 : pairingChannel10 = tripletProjector ⊗ₜ[ℂ] singletProjector := rfl
  have hg6 : totalTwoNucleonGen 6 =
      (1 / 2 : ℂ) • (spinAction I₁ ⊗ₜ[ℂ] spinAction I₁ + isospinAction I₁ ⊗ₜ[ℂ] isospinAction I₁) := by
    unfold totalTwoNucleonGen twoNucleonGen1 twoNucleonGen2
    simp [pauliBasis, ← smul_add]
  have hswap : swapSpinPair = tripletProjector - singletProjector :=
    swapOf_eq_triplet_sub_singlet pauliTripleM2C
  have hs_swap : singletProjector = (1 / 2 : ℂ) • ((1 : SpinPair) - swapSpinPair) := by
    rw [hswap, ← singlet_add_triplet]
    module
  have ht_swap : tripletProjector = (1 / 2 : ℂ) • ((1 : SpinPair) + swapSpinPair) := by
    rw [hswap, ← singlet_add_triplet]
    module
  have h10_01 :
      tripletProjector * (spinAction I₁ - isospinAction I₁) * singletProjector =
        tripletProjector * (spinAction I₁ - isospinAction I₁) := by
    have hanti := swapSpinPair_anticomm_antisym 0
    calc
      tripletProjector * (spinAction I₁ - isospinAction I₁) * singletProjector =
          (1 / 2 : ℂ) • ((1 : SpinPair) + swapSpinPair) * (spinAction I₁ - isospinAction I₁) *
            ((1 / 2 : ℂ) • ((1 : SpinPair) - swapSpinPair)) := by rw [hs_swap, ht_swap]
      _ = (1 / 4 : ℂ) • (((1 : SpinPair) + swapSpinPair) *
            ((spinAction I₁ - isospinAction I₁) * ((1 : SpinPair) - swapSpinPair))) := by
            simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
            norm_num
      _ = (1 / 4 : ℂ) • (((1 : SpinPair) + swapSpinPair) *
            (((1 : SpinPair) + swapSpinPair) * (spinAction I₁ - isospinAction I₁))) := by
            congr 2
            simp only [mul_sub, add_mul, mul_one, one_mul]
            have hsw : (spinAction I₁ - isospinAction I₁) * swapSpinPair =
                -(swapSpinPair * (spinAction I₁ - isospinAction I₁)) := by
              have h := congrArg Neg.neg hanti
              rw [neg_neg] at h
              simpa [pauliBasis, I₁] using h.symm
            rw [hsw, mul_sub, sub_eq_add_neg]
            simp only [neg_sub]
            abel
      _ = tripletProjector * (spinAction I₁ - isospinAction I₁) := by
            rw [← mul_assoc]
            have hid : ((1 / 2 : ℂ) • ((1 : SpinPair) + swapSpinPair)) *
                ((1 / 2 : ℂ) • ((1 : SpinPair) + swapSpinPair)) =
                (1 / 2 : ℂ) • ((1 : SpinPair) + swapSpinPair) := by
              rw [← ht_swap]; exact tripletProjector_idem
            rw [smul_mul_smul, show (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 by norm_num] at hid
            rw [← smul_mul_assoc, hid, ← ht_swap]
  have hp_tr : pairTrace (tripletProjector * (spinAction I₁ - isospinAction I₁) *
      (spinAction I₁ - isospinAction I₁)) = 1 := by
    have hsq : (spinAction I₁ - isospinAction I₁) * (spinAction I₁ - isospinAction I₁) =
        (2 : ℂ) • ((1 : SpinPair) - I₁ ⊗ₜ[ℂ] I₁) := by
      rw [sub_mul, mul_sub, mul_sub, spin_action_preserves_square I₁ I₁_sq,
        isospin_action_preserves_square I₁ I₁_sq]
      have hsi : spinAction I₁ * isospinAction I₁ = I₁ ⊗ₜ[ℂ] I₁ := by
        unfold spinAction isospinAction; rw [tmul_mul_tmul, mul_one, one_mul]
      have his : isospinAction I₁ * spinAction I₁ = I₁ ⊗ₜ[ℂ] I₁ := by
        rw [← spin_isospin_actions_commute, hsi]
      rw [hsi, his]
      module
    rw [mul_assoc, hsq]
    unfold tripletProjector tripletProjectorOf singletProjectorOf pauliTripleM2C
    dsimp only
    rw [Algebra.TensorProduct.one_def, mul_smul_comm]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, Fin.sum_univ_three,
      add_mul, tmul_mul_tmul, pauliBasis, map_smul, map_sub, map_add, pairTrace_tmul]
    have htr1 : Matrix.trace (1 : M2C) = 2 := by simp [Matrix.trace]
    have htr0 : Matrix.trace I₁ = 0 := pauliBasis_trace 0
    have htr1' : Matrix.trace (I₁ * I₁) = 2 := by rw [I₁_sq]; exact htr1
    have htr21 : Matrix.trace (I₂ * I₁) = 0 := by simpa [pauliBasis] using trace_pauliBasis_mul 1 0
    have htr31 : Matrix.trace (I₃ * I₁) = 0 := by simpa [pauliBasis] using trace_pauliBasis_mul 2 0
    have htr2 : Matrix.trace I₂ = 0 := pauliBasis_trace 1
    have htr3 : Matrix.trace I₃ = 0 := pauliBasis_trace 2
    rw [htr1, htr0, htr1', htr21, htr31, htr2, htr3]
    norm_num
  have hs_01 :
      singletProjector * (spinAction I₁ - isospinAction I₁) * tripletProjector =
        singletProjector * (spinAction I₁ - isospinAction I₁) := by
    calc
      singletProjector * (spinAction I₁ - isospinAction I₁) * tripletProjector =
          (1 / 2 : ℂ) • ((1 : SpinPair) - swapSpinPair) * (spinAction I₁ - isospinAction I₁) *
            ((1 / 2 : ℂ) • ((1 : SpinPair) + swapSpinPair)) := by rw [hs_swap, ht_swap]
      _ = (1 / 4 : ℂ) • (((1 : SpinPair) - swapSpinPair) *
            ((spinAction I₁ - isospinAction I₁) * ((1 : SpinPair) + swapSpinPair))) := by
            simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
            norm_num
      _ = (1 / 4 : ℂ) • (((1 : SpinPair) - swapSpinPair) *
            (((1 : SpinPair) - swapSpinPair) * (spinAction I₁ - isospinAction I₁))) := by
            congr 2
            simp only [mul_add, mul_one, sub_mul, one_mul]
            have hsw : (spinAction I₁ - isospinAction I₁) * swapSpinPair =
                -(swapSpinPair * (spinAction I₁ - isospinAction I₁)) := by
              have h := congrArg Neg.neg (swapSpinPair_anticomm_antisym 0)
              simp only [neg_neg] at h
              simpa [pauliBasis, I₁] using h.symm
            have hcombine : spinAction I₁ * swapSpinPair - isospinAction I₁ * swapSpinPair =
                (spinAction I₁ - isospinAction I₁) * swapSpinPair := by
              rw [sub_mul]
            rw [hcombine, hsw]
            abel
      _ = singletProjector * (spinAction I₁ - isospinAction I₁) := by
            rw [← mul_assoc]
            have hid : ((1 / 2 : ℂ) • ((1 : SpinPair) - swapSpinPair)) *
                ((1 / 2 : ℂ) • ((1 : SpinPair) - swapSpinPair)) =
                (1 / 2 : ℂ) • ((1 : SpinPair) - swapSpinPair) := by
              rw [← hs_swap]; exact singletProjector_idem
            rw [smul_mul_smul, show (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 by norm_num] at hid
            rw [← smul_mul_assoc, hid, ← hs_swap]
  have hsym_kill_10 :
      tripletProjector * (spinAction I₁ + isospinAction I₁) * singletProjector = 0 := by
    have hcs := (swapSpinPair_comm_sym I₁).symm
    have hcomm_tp : tripletProjector * (spinAction I₁ + isospinAction I₁) =
        (spinAction I₁ + isospinAction I₁) * tripletProjector := by
      rw [ht_swap, smul_mul_assoc, mul_smul_comm]
      congr 1
      calc
        (1 + swapSpinPair) * (spinAction I₁ + isospinAction I₁) =
            spinAction I₁ + isospinAction I₁ +
              swapSpinPair * (spinAction I₁ + isospinAction I₁) := by
          rw [add_mul, one_mul]
        _ = (spinAction I₁ + isospinAction I₁) +
              (spinAction I₁ + isospinAction I₁) * swapSpinPair := by rw [hcs]
        _ = (spinAction I₁ + isospinAction I₁) * (1 + swapSpinPair) := by
          rw [mul_add, mul_one]
    rw [hcomm_tp, mul_assoc, triplet_mul_singlet, mul_zero]
  have hsplit1 :
      spinAction I₁ ⊗ₜ[ℂ] spinAction I₁ + isospinAction I₁ ⊗ₜ[ℂ] isospinAction I₁ =
        (1 / 2 : ℂ) • ((spinAction I₁ + isospinAction I₁) ⊗ₜ[ℂ] (spinAction I₁ + isospinAction I₁) +
          (spinAction I₁ - isospinAction I₁) ⊗ₜ[ℂ] (spinAction I₁ - isospinAction I₁)) := by
    have hsum_sq :
        (spinAction I₁ + isospinAction I₁) ⊗ₜ[ℂ] (spinAction I₁ + isospinAction I₁) +
          (spinAction I₁ - isospinAction I₁) ⊗ₜ[ℂ] (spinAction I₁ - isospinAction I₁) =
          (2 : ℂ) • (spinAction I₁ ⊗ₜ[ℂ] spinAction I₁ + isospinAction I₁ ⊗ₜ[ℂ] isospinAction I₁) := by
      simp only [add_tmul, tmul_add, sub_tmul, tmul_sub, two_smul]
      abel
    rw [hsum_sq, smul_smul]
    norm_num
  have hprod :
      pairingChannel10 * totalTwoNucleonGen 6 * pairingChannel01 =
        (1 / 4 : ℂ) • ((tripletProjector * (spinAction I₁ - isospinAction I₁)) ⊗ₜ[ℂ]
          (singletProjector * (spinAction I₁ - isospinAction I₁))) := by
    rw [h10, h01, hg6, hsplit1, smul_smul, show (1 / 2 : ℂ) * (1 / 2 : ℂ) = 1 / 4 by norm_num,
      mul_smul_comm, smul_mul_assoc, mul_assoc (tripletProjector ⊗ₜ[ℂ] singletProjector),
      tensor_pair_sandwich, hsym_kill_10, zero_tmul, zero_add, h10_01, hs_01]
  have hps_tr : pairTrace (singletProjector * (spinAction I₁ - isospinAction I₁) *
      (spinAction I₁ - isospinAction I₁)) = 1 := by
    have hsq : (spinAction I₁ - isospinAction I₁) * (spinAction I₁ - isospinAction I₁) =
        (2 : ℂ) • ((1 : SpinPair) - I₁ ⊗ₜ[ℂ] I₁) := by
      rw [sub_mul, mul_sub, mul_sub, spin_action_preserves_square I₁ I₁_sq,
        isospin_action_preserves_square I₁ I₁_sq]
      have hsi : spinAction I₁ * isospinAction I₁ = I₁ ⊗ₜ[ℂ] I₁ := by
        unfold spinAction isospinAction; rw [tmul_mul_tmul, mul_one, one_mul]
      have his : isospinAction I₁ * spinAction I₁ = I₁ ⊗ₜ[ℂ] I₁ := by
        rw [← spin_isospin_actions_commute, hsi]
      rw [hsi, his]
      module
    rw [mul_assoc, hsq]
    unfold singletProjector singletProjectorOf pauliTripleM2C
    dsimp only
    rw [Algebra.TensorProduct.one_def, mul_smul_comm]
    simp only [smul_mul_assoc, sub_mul, mul_sub, one_mul, mul_one, Fin.sum_univ_three,
      add_mul, tmul_mul_tmul, pauliBasis, map_smul, map_sub, map_add, pairTrace_tmul]
    have htr1 : Matrix.trace (1 : M2C) = 2 := by simp [Matrix.trace]
    have htr0 : Matrix.trace I₁ = 0 := pauliBasis_trace 0
    have htr1' : Matrix.trace (I₁ * I₁) = 2 := by rw [I₁_sq]; exact htr1
    have htr21 : Matrix.trace (I₂ * I₁) = 0 := by simpa [pauliBasis] using trace_pauliBasis_mul 1 0
    have htr31 : Matrix.trace (I₃ * I₁) = 0 := by simpa [pauliBasis] using trace_pauliBasis_mul 2 0
    have htr2 : Matrix.trace I₂ = 0 := pauliBasis_trace 1
    have htr3 : Matrix.trace I₃ = 0 := pauliBasis_trace 2
    rw [htr1, htr0, htr1', htr21, htr31, htr2, htr3]
    norm_num
  intro hzero
  let tr2 : TwoNucleonSpinIsospin →ₗ[ℂ] ℂ :=
    TensorProduct.lift
      { toFun := fun A =>
          { toFun := fun B => pairTrace A * pairTrace B
            map_add' := fun B₁ B₂ => by simp [map_add, mul_add]
            map_smul' := fun c B => by simp [map_smul]; ring }
        map_add' := fun A₁ A₂ => by ext B; simp [map_add, add_mul]
        map_smul' := fun c A => by ext B; simp [map_smul]; ring }
  have htr2_val : tr2 (pairingChannel10 * totalTwoNucleonGen 6 * pairingChannel01 *
      ((spinAction I₁ - isospinAction I₁) ⊗ₜ[ℂ] (spinAction I₁ - isospinAction I₁))) = 0 := by
    have hz := congrArg (fun x : TwoNucleonSpinIsospin =>
      tr2 (x * ((spinAction I₁ - isospinAction I₁) ⊗ₜ[ℂ]
        (spinAction I₁ - isospinAction I₁)))) hzero
    have hz0 : tr2 ((0 : TwoNucleonSpinIsospin) *
        ((spinAction I₁ - isospinAction I₁) ⊗ₜ[ℂ]
          (spinAction I₁ - isospinAction I₁))) = 0 := by
      rw [@MulZeroClass.zero_mul TwoNucleonSpinIsospin _]
      exact map_zero tr2
    exact hz.trans hz0
  rw [hprod, smul_mul_assoc, tmul_mul_tmul, map_smul,
    show tr2 ((tripletProjector * (spinAction I₁ - isospinAction I₁) *
      (spinAction I₁ - isospinAction I₁)) ⊗ₜ[ℂ]
      (singletProjector * (spinAction I₁ - isospinAction I₁) *
      (spinAction I₁ - isospinAction I₁))) =
      pairTrace (tripletProjector * (spinAction I₁ - isospinAction I₁) *
        (spinAction I₁ - isospinAction I₁)) *
      pairTrace (singletProjector * (spinAction I₁ - isospinAction I₁) *
        (spinAction I₁ - isospinAction I₁)) from rfl,
    hp_tr, hps_tr] at htr2_val
  norm_num at htr2_val

end

/-! ### K^π sectors and rotational selection rules

The intrinsic projection `K` and spatial parity are separately conserved labels.
The theorem below is a conservation law conditional on the usual spectral inputs
for the K and parity operators; it does not construct a rotor Hamiltonian.
-/

/-- Axial intrinsic-projection/spatial-parity label `K^π`; `twoK` stores `2K`. -/
structure KParitySector where
  twoK : ℤ
  parity : SpatialParity
  deriving DecidableEq, Repr

instance : Inhabited KParitySector := ⟨⟨0, .positive⟩⟩

/-- A Hamiltonian commuting with the intrinsic K operator cannot mix distinct
K sectors.  The `K` label is a supplied spectral observable, not derived from J. -/
theorem hamiltonian_no_K_mixing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Kop H Pi Pf : Module.End ℝ V) (ki kf : ℤ)
    (hi : Kop.comp Pi = (ki : ℝ) • Pi)
    (hf : Pf.comp Kop = (kf : ℝ) • Pf)
    (hcomm : Kop.comp H = H.comp Kop) (hne : kf ≠ ki) :
    Pf.comp (H.comp Pi) = 0 := by
  have hcast : (kf : ℝ) ≠ (ki : ℝ) := by exact_mod_cast hne
  exact InfoGeometry.Physics.NuclearSymmetrySectors.commuting_hamiltonian_block_zero
    Kop H Pi Pf _ _ hi hf hcomm hcast

/-- Combined K^π selection: if either the intrinsic projection or the spatial
parity differs, a Hamiltonian commuting with both operators has zero block
between the two sectors. -/
theorem hamiltonian_no_Kpi_mixing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Kop parity H Pi Pf : Module.End ℝ V) (i f : KParitySector)
    (hKi : Kop.comp Pi = (i.twoK : ℝ) • Pi)
    (hKf : Pf.comp Kop = (f.twoK : ℝ) • Pf)
    (hKcomm : Kop.comp H = H.comp Kop)
    (hpi : parity.comp Pi = i.parity.sign • Pi)
    (hpf : Pf.comp parity = f.parity.sign • Pf)
    (hparitycomm : parity.comp H = H.comp parity)
    (hdiff : f.twoK ≠ i.twoK ∨ f.parity ≠ i.parity) :
    Pf.comp (H.comp Pi) = 0 := by
  cases hdiff with
  | inl hk =>
      exact hamiltonian_no_K_mixing Kop H Pi Pf i.twoK f.twoK hKi hKf hKcomm hk
  | inr hp =>
      exact InfoGeometry.Physics.NuclearSymmetrySectors.hamiltonian_no_parity_mixing
        parity H Pi Pf i.parity f.parity hpi hpf hparitycomm hp

/-- The K label is independent of spatial parity: the same intrinsic projection
admits both parity sectors as distinct sectors. -/
theorem KParitySector_sameK_oppositeParity_distinct :
    (⟨1, SpatialParity.positive⟩ : KParitySector) ≠
      ⟨1, SpatialParity.negative⟩ := by
  decide

end InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
