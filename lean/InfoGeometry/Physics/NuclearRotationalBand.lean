/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearAngularMomentum
import InfoGeometry.Physics.NuclearSymmetrySectors
import InfoGeometry.Physics.NuclearShellModel
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation

noncomputable section

namespace InfoGeometry.Physics.NuclearRotationalBand

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦] [CharZero 𝒦]

def moment_of_inertia (hbar : 𝒦) (mass_radius_sq : 𝒦) (deformation_factor : 𝒦) : 𝒦 :=
  mass_radius_sq * (1 + deformation_factor * deformation_factor)

theorem moment_of_inertia_homogeneous (hbar : 𝒦) (mass_radius_sq : 𝒦) (deformation_factor : 𝒦) (lam : 𝒦) :
    moment_of_inertia hbar (lam * mass_radius_sq) deformation_factor = lam * moment_of_inertia hbar mass_radius_sq deformation_factor := by
  calc
    moment_of_inertia hbar (lam * mass_radius_sq) deformation_factor =
        (lam * mass_radius_sq) * (1 + deformation_factor * deformation_factor) := by rfl
    _ = lam * (mass_radius_sq * (1 + deformation_factor * deformation_factor)) := by ring
    _ = lam * moment_of_inertia hbar mass_radius_sq deformation_factor := by rfl

def rotational_energy (hbar : 𝒦) (𝓘 : 𝒦) (I : 𝒦) : 𝒦 :=
  (hbar * hbar : 𝒦) * I * (I + 1 : 𝒦) / (2 * 𝓘 : 𝒦)

theorem rotational_energy_spacing (hbar : 𝒦) (𝓘 : 𝒦) (I : 𝒦) :
    rotational_energy hbar 𝓘 (I + 1) - rotational_energy hbar 𝓘 I =
      (hbar * hbar : 𝒦) * (I + 1 : 𝒦) / 𝓘 := by
  have h₁ : rotational_energy hbar 𝓘 (I + 1) = (hbar * hbar : 𝒦) * (I + 1 : 𝒦) * ((I + 1 : 𝒦) + (1 : 𝒦)) / (2 * 𝓘 : 𝒦) := by
    rfl
  have h₂ : rotational_energy hbar 𝓘 I = (hbar * hbar : 𝒦) * I * (I + 1 : 𝒦) / (2 * 𝓘 : 𝒦) := by
    rfl
  rw [h₁, h₂]
  field_simp
  <;> ring
  <;> field_simp
  <;> ring

-- -----------------------------------------------------------------------------
-- SECTION 2: Finite-dimensional SU(2) representations on SpinSpace twoI
-- -----------------------------------------------------------------------------

section SU2SpinRepresentations

open InfoGeometry.Physics.NuclearAngularMomentum
open InfoGeometry.Physics.NuclearShellModel
open scoped BigOperators

/-- `(twoI + 1)`-dimensional complex spin representation space `Fin (twoI + 1) → ℂ`.
For integer spin `I`, take `twoI = 2 * I`; for spin-`1/2`, take `twoI = 1`. -/
abbrev SpinSpace (twoI : ℕ) := Fin (twoI + 1) → ℂ

/-- Standard magnetic basis ket `|I, M⟩` with `M = twoI / 2 - k`. -/
def spinKet (twoI : ℕ) (k : Fin (twoI + 1)) : SpinSpace twoI :=
  Pi.single k 1

/-- Magnetic quantum number `M = twoI / 2 - k` as a complex scalar. -/
def spinMValue (twoI : ℕ) (k : Fin (twoI + 1)) : ℂ :=
  (twoI : ℂ) / 2 - (k.val : ℂ)

@[simp] theorem spinKet_apply (twoI : ℕ) (k j : Fin (twoI + 1)) :
    spinKet twoI k j = if j = k then 1 else 0 := by
  simp [spinKet, Pi.single_apply]

theorem spinMValue_injective (twoI : ℕ) : Function.Injective (spinMValue twoI) := by
  intro a b hab
  unfold spinMValue at hab
  have h1 : (a.val : ℂ) = (b.val : ℂ) := by linear_combination -hab
  have h2 : a.val = b.val := by exact_mod_cast h1
  exact Fin.ext h2

theorem spinSpace_basis_expand {twoI : ℕ} (ψ : SpinSpace twoI) :
    ψ = ∑ k : Fin (twoI + 1), ψ k • spinKet twoI k := by
  ext j
  simp [spinKet, Pi.single_apply]

/-- Raising coefficient `√((k + 1)(twoI - k))`. -/
def spinPlusCoeff (twoI k : ℕ) : ℂ :=
  ((Real.sqrt (((k : ℝ) + 1) * ((twoI : ℝ) - k)) : ℝ) : ℂ)

/-- Lowering coefficient `√(k (twoI + 1 - k))`. -/
def spinMinusCoeff (twoI k : ℕ) : ℂ :=
  ((Real.sqrt ((k : ℝ) * ((twoI : ℝ) + 1 - k)) : ℝ) : ℂ)

theorem spinPlusCoeff_sq {twoI k : ℕ} (hk : k ≤ twoI) :
    spinPlusCoeff twoI k * spinPlusCoeff twoI k = ((k : ℂ) + 1) * ((twoI : ℂ) - k) := by
  unfold spinPlusCoeff
  have hnn : 0 ≤ ((k : ℝ) + 1) * ((twoI : ℝ) - k) := by
    have hk' : (k : ℝ) ≤ twoI := by exact_mod_cast hk
    nlinarith
  have hsq : Real.sqrt (((k : ℝ) + 1) * ((twoI : ℝ) - k)) *
      Real.sqrt (((k : ℝ) + 1) * ((twoI : ℝ) - k)) =
      ((k : ℝ) + 1) * ((twoI : ℝ) - k) := Real.mul_self_sqrt hnn
  exact_mod_cast hsq

theorem spinMinusCoeff_sq {twoI k : ℕ} (hk : k ≤ twoI) :
    spinMinusCoeff twoI k * spinMinusCoeff twoI k = (k : ℂ) * ((twoI : ℂ) + 1 - k) := by
  unfold spinMinusCoeff
  have hnn : 0 ≤ (k : ℝ) * ((twoI : ℝ) + 1 - k) := by
    have hk' : (k : ℝ) ≤ twoI := by exact_mod_cast hk
    nlinarith
  have hsq : Real.sqrt ((k : ℝ) * ((twoI : ℝ) + 1 - k)) *
      Real.sqrt ((k : ℝ) * ((twoI : ℝ) + 1 - k)) =
      (k : ℝ) * ((twoI : ℝ) + 1 - k) := Real.mul_self_sqrt hnn
  exact_mod_cast hsq

theorem spinPlusCoeff_eq_spinMinusCoeff_succ (twoI k : ℕ) :
    spinPlusCoeff twoI k = spinMinusCoeff twoI (k + 1) := by
  unfold spinPlusCoeff spinMinusCoeff
  congr 2
  push_cast
  ring

theorem spinPlusCoeff_ne_zero {twoI k : ℕ} (hk : k < twoI) :
    spinPlusCoeff twoI k ≠ 0 := by
  intro h
  have hsq := spinPlusCoeff_sq (Nat.le_of_lt hk)
  rw [h, zero_mul] at hsq
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hdiff : (twoI : ℂ) - k ≠ 0 := by
    intro hd
    have heq : (twoI : ℂ) = k := sub_eq_zero.mp hd
    have heq' : twoI = k := by exact_mod_cast heq
    omega
  exact mul_ne_zero hk1 hdiff hsq.symm

/-- Angular momentum `J_z` operator on `SpinSpace twoI`. -/
def spinZ (twoI : ℕ) : Module.End ℂ (SpinSpace twoI) where
  toFun ψ k := spinMValue twoI k * ψ k
  map_add' ψ φ := by ext k; simp [mul_add]
  map_smul' a ψ := by ext k; simp; ring

@[simp] theorem spinZ_apply (twoI : ℕ) (ψ : SpinSpace twoI) (k : Fin (twoI + 1)) :
    spinZ twoI ψ k = spinMValue twoI k * ψ k := rfl

/-- Angular momentum raising operator `J_+` on `SpinSpace twoI`. -/
def spinPlus (twoI : ℕ) : Module.End ℂ (SpinSpace twoI) where
  toFun ψ k := if h : k.val < twoI then
    spinPlusCoeff twoI k.val * ψ ⟨k.val + 1, by omega⟩ else 0
  map_add' ψ φ := by
    ext k
    change (if h : k.val < twoI then spinPlusCoeff twoI k.val * (ψ ⟨k.val + 1, by omega⟩ + φ ⟨k.val + 1, by omega⟩) else 0) =
      (if h : k.val < twoI then spinPlusCoeff twoI k.val * ψ ⟨k.val + 1, by omega⟩ else 0) +
      (if h : k.val < twoI then spinPlusCoeff twoI k.val * φ ⟨k.val + 1, by omega⟩ else 0)
    split_ifs <;> ring
  map_smul' a ψ := by
    ext k
    change (if h : k.val < twoI then spinPlusCoeff twoI k.val * (a * ψ ⟨k.val + 1, by omega⟩) else 0) =
      a * (if h : k.val < twoI then spinPlusCoeff twoI k.val * ψ ⟨k.val + 1, by omega⟩ else 0)
    split_ifs <;> ring

@[simp] theorem spinPlus_apply (twoI : ℕ) (ψ : SpinSpace twoI) (k : Fin (twoI + 1)) :
    spinPlus twoI ψ k = if h : k.val < twoI then
      spinPlusCoeff twoI k.val * ψ ⟨k.val + 1, by omega⟩ else 0 := rfl

/-- Angular momentum lowering operator `J_-` on `SpinSpace twoI`. -/
def spinMinus (twoI : ℕ) : Module.End ℂ (SpinSpace twoI) where
  toFun ψ k := if h : 0 < k.val then
    spinMinusCoeff twoI k.val * ψ ⟨k.val - 1, by omega⟩ else 0
  map_add' ψ φ := by
    ext k
    change (if h : 0 < k.val then spinMinusCoeff twoI k.val * (ψ ⟨k.val - 1, by omega⟩ + φ ⟨k.val - 1, by omega⟩) else 0) =
      (if h : 0 < k.val then spinMinusCoeff twoI k.val * ψ ⟨k.val - 1, by omega⟩ else 0) +
      (if h : 0 < k.val then spinMinusCoeff twoI k.val * φ ⟨k.val - 1, by omega⟩ else 0)
    split_ifs <;> ring
  map_smul' a ψ := by
    ext k
    change (if h : 0 < k.val then spinMinusCoeff twoI k.val * (a * ψ ⟨k.val - 1, by omega⟩) else 0) =
      a * (if h : 0 < k.val then spinMinusCoeff twoI k.val * ψ ⟨k.val - 1, by omega⟩ else 0)
    split_ifs <;> ring

@[simp] theorem spinMinus_apply (twoI : ℕ) (ψ : SpinSpace twoI) (k : Fin (twoI + 1)) :
    spinMinus twoI ψ k = if h : 0 < k.val then
      spinMinusCoeff twoI k.val * ψ ⟨k.val - 1, by omega⟩ else 0 := rfl

def spinX (twoI : ℕ) : Module.End ℂ (SpinSpace twoI) :=
  (1 / 2 : ℂ) • (spinPlus twoI + spinMinus twoI)

def spinY (twoI : ℕ) : Module.End ℂ (SpinSpace twoI) :=
  (-Complex.I / 2 : ℂ) • (spinPlus twoI - spinMinus twoI)

/-- Quadratic Casimir `J^2 = J_z^2 + (1/2)(J_+ J_- + J_- J_+)` on `SpinSpace twoI`. -/
def spinCasimirOp (twoI : ℕ) : Module.End ℂ (SpinSpace twoI) :=
  spinZ twoI * spinZ twoI + (1 / 2 : ℂ) • (spinPlus twoI * spinMinus twoI + spinMinus twoI * spinPlus twoI)

/-- Cartesian Casimir `J_x^2 + J_y^2 + J_z^2` on `SpinSpace twoI`. -/
def spinCartesianCasimirOp (twoI : ℕ) : Module.End ℂ (SpinSpace twoI) :=
  spinX twoI * spinX twoI + spinY twoI * spinY twoI + spinZ twoI * spinZ twoI

@[simp] theorem spinZ_ket (twoI : ℕ) (k : Fin (twoI + 1)) :
    spinZ twoI (spinKet twoI k) = spinMValue twoI k • spinKet twoI k := by
  ext j
  by_cases hj : j = k
  · subst hj; simp
  · simp [hj]

theorem spinPlus_ket_zero (twoI : ℕ) :
    spinPlus twoI (spinKet twoI ⟨0, Nat.succ_pos twoI⟩) = 0 := by
  ext j
  rw [spinPlus_apply]
  split_ifs with h
  · have hne : (⟨j.val + 1, by omega⟩ : Fin (twoI + 1)) ≠ ⟨0, Nat.succ_pos twoI⟩ := by
      intro heq; have : j.val + 1 = 0 := congrArg Fin.val heq; omega
    rw [spinKet_apply, if_neg hne, mul_zero]; rfl
  · rfl

theorem spinPlus_ket_succ (twoI k : ℕ) (hk : k < twoI) :
    spinPlus twoI (spinKet twoI ⟨k + 1, by omega⟩) =
      spinPlusCoeff twoI k • spinKet twoI ⟨k, by omega⟩ := by
  ext j
  rw [spinPlus_apply]
  split_ifs with h
  · by_cases hj : j.val = k
    · have hj1 : (⟨j.val + 1, by omega⟩ : Fin (twoI + 1)) = ⟨k + 1, by omega⟩ := by
        ext; dsimp; omega
      have hj2 : j = ⟨k, by omega⟩ := by ext; exact hj
      simp [hj2]
    · have hj1 : (⟨j.val + 1, by omega⟩ : Fin (twoI + 1)) ≠ ⟨k + 1, by omega⟩ := by
        intro heq; apply hj; have : j.val + 1 = k + 1 := congrArg Fin.val heq; omega
      have hj2 : j ≠ ⟨k, by omega⟩ := by
        intro heq; apply hj; exact congrArg Fin.val heq
      simp [hj1, hj2]
  · have hj : j ≠ ⟨k, by omega⟩ := by
      intro heq; apply h; have : j.val = k := congrArg Fin.val heq; omega
    simp [hj]

theorem spinMinus_ket_top (twoI : ℕ) :
    spinMinus twoI (spinKet twoI ⟨twoI, Nat.lt_succ_self twoI⟩) = 0 := by
  ext j
  rw [spinMinus_apply]
  split_ifs with h
  · have hne : (⟨j.val - 1, by omega⟩ : Fin (twoI + 1)) ≠ ⟨twoI, Nat.lt_succ_self twoI⟩ := by
      intro heq; have : j.val - 1 = twoI := congrArg Fin.val heq; omega
    rw [spinKet_apply, if_neg hne, mul_zero]; rfl
  · rfl

theorem spinMinus_ket_lt (twoI k : ℕ) (hk : k < twoI) :
    spinMinus twoI (spinKet twoI ⟨k, by omega⟩) =
      spinPlusCoeff twoI k • spinKet twoI ⟨k + 1, by omega⟩ := by
  ext j
  rw [spinMinus_apply]
  split_ifs with h
  · by_cases hj : j.val = k + 1
    · have hj1 : (⟨j.val - 1, by omega⟩ : Fin (twoI + 1)) = ⟨k, by omega⟩ := by
        ext; dsimp; omega
      have hj2 : j = ⟨k + 1, by omega⟩ := by ext; exact hj
      simp [hj2, spinPlusCoeff_eq_spinMinusCoeff_succ]
    · have hj1 : (⟨j.val - 1, by omega⟩ : Fin (twoI + 1)) ≠ ⟨k, by omega⟩ := by
        intro heq; apply hj; have : j.val - 1 = k := congrArg Fin.val heq; omega
      have hj2 : j ≠ ⟨k + 1, by omega⟩ := by
        intro heq; apply hj; exact congrArg Fin.val heq
      simp [hj1, hj2]
  · have hj : j ≠ ⟨k + 1, by omega⟩ := by
      intro heq; apply h; have : j.val = k + 1 := congrArg Fin.val heq; omega
    simp [hj]

theorem spinZ_comm_spinPlus (twoI : ℕ) :
    spinZ twoI * spinPlus twoI - spinPlus twoI * spinZ twoI = spinPlus twoI := by
  apply LinearMap.ext; intro ψ; ext k
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, spinZ_apply, spinPlus_apply]
  split_ifs with h
  · unfold spinMValue; push_cast; ring
  · ring

theorem spinZ_comm_spinMinus (twoI : ℕ) :
    spinZ twoI * spinMinus twoI - spinMinus twoI * spinZ twoI = -spinMinus twoI := by
  apply LinearMap.ext; intro ψ; ext k
  simp only [LinearMap.sub_apply, Pi.sub_apply, LinearMap.neg_apply, Pi.neg_apply,
    Module.End.mul_apply, spinZ_apply, spinMinus_apply]
  split_ifs with h
  · unfold spinMValue
    have hsub : ((k.val - 1 : ℕ) : ℂ) = (k.val : ℂ) - 1 := by rw [Nat.cast_sub h]; simp
    rw [hsub]; ring
  · ring

theorem spinPlus_mul_spinMinus_apply (twoI : ℕ) (ψ : SpinSpace twoI) (k : Fin (twoI + 1)) :
    spinPlus twoI (spinMinus twoI ψ) k =
      (((k.val : ℂ) + 1) * ((twoI : ℂ) - k.val)) * ψ k := by
  rw [spinPlus_apply]
  split_ifs with h
  · rw [spinMinus_apply]
    have hk0 : 0 < (⟨k.val + 1, by omega⟩ : Fin (twoI + 1)).val := Nat.succ_pos k.val
    rw [dite_eq_left hk0]
    have hidx : (⟨(⟨k.val + 1, by omega⟩ : Fin (twoI + 1)).val - 1, by omega⟩ :
        Fin (twoI + 1)) = k := by ext; dsimp
    rw [hidx]
    change spinPlusCoeff twoI k.val * (spinMinusCoeff twoI (k.val + 1) * ψ k) = _
    rw [← spinPlusCoeff_eq_spinMinusCoeff_succ, ← mul_assoc, spinPlusCoeff_sq (by omega)]
  · have hkeq : k.val = twoI := by omega
    simp [hkeq]

theorem spinMinus_mul_spinPlus_apply (twoI : ℕ) (ψ : SpinSpace twoI) (k : Fin (twoI + 1)) :
    spinMinus twoI (spinPlus twoI ψ) k =
      ((k.val : ℂ) * ((twoI : ℂ) + 1 - k.val)) * ψ k := by
  rw [spinMinus_apply]
  split_ifs with h
  · rw [spinPlus_apply]
    have hk1 : (⟨k.val - 1, by omega⟩ : Fin (twoI + 1)).val < twoI := by
      change k.val - 1 < twoI; omega
    rw [dite_eq_left hk1]
    have hidx : (⟨(⟨k.val - 1, by omega⟩ : Fin (twoI + 1)).val + 1, by omega⟩ :
        Fin (twoI + 1)) = k := by ext; dsimp; omega
    rw [hidx]
    have heqc : spinPlusCoeff twoI (⟨k.val - 1, by omega⟩ : Fin (twoI + 1)).val =
        spinMinusCoeff twoI k.val := by
      change spinPlusCoeff twoI (k.val - 1) = spinMinusCoeff twoI k.val
      rw [spinPlusCoeff_eq_spinMinusCoeff_succ]; congr 1; omega
    rw [heqc, ← mul_assoc, spinMinusCoeff_sq (by omega)]
  · have hk0 : k.val = 0 := by omega
    simp [hk0]

theorem spinPlus_comm_spinMinus (twoI : ℕ) :
    spinPlus twoI * spinMinus twoI - spinMinus twoI * spinPlus twoI = (2 : ℂ) • spinZ twoI := by
  apply LinearMap.ext; intro ψ; ext k
  change spinPlus twoI (spinMinus twoI ψ) k - spinMinus twoI (spinPlus twoI ψ) k =
    2 * (spinZ twoI ψ k)
  rw [spinPlus_mul_spinMinus_apply, spinMinus_mul_spinPlus_apply, spinZ_apply]
  unfold spinMValue
  ring

/-- Complete `SU(2)` representation structure on `SpinSpace twoI` for every `twoI : ℕ`. -/
def spinIrrep (twoI : ℕ) : SU2Rep ℂ (SpinSpace twoI) where
  J_zero := spinZ twoI
  J_plus := spinPlus twoI
  J_minus := spinMinus twoI
  comm_zero_plus := spinZ_comm_spinPlus twoI
  comm_zero_minus := spinZ_comm_spinMinus twoI
  comm_plus_minus := spinPlus_comm_spinMinus twoI

/-- For `twoI = 1`, `spinIrrep 1` coincides identically with `NuclearAngularMomentum.spinHalfSU2Rep`. -/
theorem spinIrrep_one_eq_spinHalfSU2Rep : spinIrrep 1 = spinHalfSU2Rep := by
  have hz : spinZ 1 = spinHalfSU2Rep.J_zero := by
    apply LinearMap.ext; intro ψ; ext k
    fin_cases k <;>
      (simp [spinZ, spinMValue, spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_zero,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; try ring)
  have hp : spinPlus 1 = spinHalfSU2Rep.J_plus := by
    apply LinearMap.ext; intro ψ; ext k
    fin_cases k <;>
      simp [spinPlus, spinPlusCoeff, spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_plus,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hm : spinMinus 1 = spinHalfSU2Rep.J_minus := by
    apply LinearMap.ext; intro ψ; ext k
    fin_cases k <;>
      simp [spinMinus, spinMinusCoeff, spinHalfSU2Rep, InfoGeometry.Algebra.FiniteSpin.J_minus,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  cases h : spinHalfSU2Rep
  dsimp [spinIrrep] at hz hp hm ⊢
  rw [h] at hz hp hm
  congr

theorem spinCartesianCasimirOp_eq_spinCasimirOp (twoI : ℕ) :
    spinCartesianCasimirOp twoI = spinCasimirOp twoI := by
  apply LinearMap.ext; intro ψ; ext k
  unfold spinCartesianCasimirOp spinCasimirOp spinX spinY
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.sub_apply, map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [show Complex.I ^ 2 = -1 from Complex.I_sq]
  ring

/-- **SU(2) Casimir Diagonalization**: `J^2 = (twoI / 2)(twoI / 2 + 1) • 1` on `SpinSpace twoI`. -/
theorem spinCasimirOp_eq_scalar (twoI : ℕ) :
    spinCasimirOp twoI =
      (((twoI : ℂ) / 2) * ((twoI : ℂ) / 2 + 1)) • (1 : Module.End ℂ (SpinSpace twoI)) := by
  apply LinearMap.ext; intro ψ; ext k
  simp only [spinCasimirOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Module.End.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [spinPlus_mul_spinMinus_apply, spinMinus_mul_spinPlus_apply]
  simp only [spinZ, LinearMap.coe_mk, AddHom.coe_mk, spinMValue]
  ring

theorem spinCasimirOp_integer_eq_scalar (I : ℕ) :
    spinCasimirOp (2 * I) =
      ((I : ℂ) * ((I : ℂ) + 1)) • (1 : Module.End ℂ (SpinSpace (2 * I))) := by
  rw [spinCasimirOp_eq_scalar]
  push_cast
  ring_nf

-- -----------------------------------------------------------------------------
-- SECTION 3: Explicit Unitary Clebsch--Gordan Recoupling j ⊗ 1/2 -> (j+1/2) ⊕ (j-1/2)
-- -----------------------------------------------------------------------------

/-- Tensor product space `(Fin (n + 2) × Fin 2) → ℂ` for coupling spin `j = (n + 1)/2` with `1/2`. -/
abbrev SpinTensorHalfSpace (n : ℕ) := Fin (n + 2) × Fin 2 → ℂ

/-- Coupled direct-sum space `SpinSpace (n + 2) × SpinSpace n` for `(j + 1/2) ⊕ (j - 1/2)`. -/
abbrev CoupledHalfSpace (n : ℕ) := SpinSpace (n + 2) × SpinSpace n

/-- Clebsch--Gordan cosine coefficient `√((n + 2 - p) / (n + 2))`. -/
def cgAlpha (n p : ℕ) : ℂ :=
  ((Real.sqrt (((n : ℝ) + 2 - p) / ((n : ℝ) + 2)) : ℝ) : ℂ)

/-- Clebsch--Gordan sine coefficient `√(p / (n + 2))`. -/
def cgBeta (n p : ℕ) : ℂ :=
  ((Real.sqrt ((p : ℝ) / ((n : ℝ) + 2)) : ℝ) : ℂ)

theorem cgAlpha_sq {n p : ℕ} (hp : p ≤ n + 2) :
    cgAlpha n p * cgAlpha n p = ((n : ℂ) + 2 - p) / ((n : ℂ) + 2) := by
  unfold cgAlpha
  have hp' : (p : ℝ) ≤ n + 2 := by exact_mod_cast hp
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hnn : 0 ≤ ((n : ℝ) + 2 - p) / ((n : ℝ) + 2) := div_nonneg (by linarith) (le_of_lt hden)
  have hsq := Real.mul_self_sqrt hnn
  rw [← Complex.ofReal_mul, hsq]
  push_cast
  rfl

theorem cgBeta_sq (n p : ℕ) :
    cgBeta n p * cgBeta n p = (p : ℂ) / ((n : ℂ) + 2) := by
  unfold cgBeta
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hnn : 0 ≤ (p : ℝ) / ((n : ℝ) + 2) := div_nonneg (Nat.cast_nonneg p) (le_of_lt hden)
  have hsq := Real.mul_self_sqrt hnn
  rw [← Complex.ofReal_mul, hsq]
  push_cast
  rfl

theorem cgAlpha_sq_add_cgBeta_sq {n p : ℕ} (hp : p ≤ n + 2) :
    cgAlpha n p * cgAlpha n p + cgBeta n p * cgBeta n p = 1 := by
  rw [cgAlpha_sq hp, cgBeta_sq]
  have hden : ((n : ℂ) + 2) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact_mod_cast ne_of_gt this
  field_simp [hden]
  ring

@[simp] theorem cgAlpha_zero (n : ℕ) : cgAlpha n 0 = 1 := by
  unfold cgAlpha
  have hden : ((n : ℝ) + 2) ≠ 0 := by positivity
  simp [div_self hden]

@[simp] theorem cgBeta_zero (n : ℕ) : cgBeta n 0 = 0 := by
  unfold cgBeta
  simp

@[simp] theorem cgAlpha_top (n : ℕ) : cgAlpha n (n + 2) = 0 := by
  unfold cgAlpha
  have hnum : (n : ℝ) + 2 - ((n + 2 : ℕ) : ℝ) = 0 := by push_cast; ring
  simp [hnum]

@[simp] theorem cgBeta_top (n : ℕ) : cgBeta n (n + 2) = 1 := by
  unfold cgBeta
  have hden : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hnum : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  simp [hnum, div_self hden]

theorem star_cgAlpha (n p : ℕ) : star (cgAlpha n p) = cgAlpha n p := by
  unfold cgAlpha; simp

theorem star_cgBeta (n p : ℕ) : star (cgBeta n p) = cgBeta n p := by
  unfold cgBeta; simp

/-- Unitary Clebsch--Gordan transformation from coupled `(j + 1/2) ⊕ (j - 1/2)` to uncoupled `j ⊗ 1/2`. -/
def cgCouplingBackward (n : ℕ) : CoupledHalfSpace n →ₗ[ℂ] SpinTensorHalfSpace n where
  toFun ψ := fun ks =>
    if ks.2 = 0 then
      cgAlpha n ks.1.val * ψ.1 ⟨ks.1.val, by omega⟩ -
        (if h : 0 < ks.1.val then cgBeta n ks.1.val * ψ.2 ⟨ks.1.val - 1, by omega⟩ else 0)
    else
      cgBeta n (ks.1.val + 1) * ψ.1 ⟨ks.1.val + 1, by omega⟩ +
        (if h : ks.1.val < n + 1 then cgAlpha n (ks.1.val + 1) * ψ.2 ⟨ks.1.val, by omega⟩ else 0)
  map_add' ψ φ := by
    ext ⟨k, s⟩
    fin_cases s
    · change cgAlpha n k.val * (ψ.1 ⟨k.val, by omega⟩ + φ.1 ⟨k.val, by omega⟩) -
          (if h : 0 < k.val then cgBeta n k.val * (ψ.2 ⟨k.val - 1, by omega⟩ + φ.2 ⟨k.val - 1, by omega⟩) else 0) =
        (cgAlpha n k.val * ψ.1 ⟨k.val, by omega⟩ -
          (if h : 0 < k.val then cgBeta n k.val * ψ.2 ⟨k.val - 1, by omega⟩ else 0)) +
        (cgAlpha n k.val * φ.1 ⟨k.val, by omega⟩ -
          (if h : 0 < k.val then cgBeta n k.val * φ.2 ⟨k.val - 1, by omega⟩ else 0))
      split_ifs <;> ring
    · change cgBeta n (k.val + 1) * (ψ.1 ⟨k.val + 1, by omega⟩ + φ.1 ⟨k.val + 1, by omega⟩) +
          (if h : k.val < n + 1 then cgAlpha n (k.val + 1) * (ψ.2 ⟨k.val, by omega⟩ + φ.2 ⟨k.val, by omega⟩) else 0) =
        (cgBeta n (k.val + 1) * ψ.1 ⟨k.val + 1, by omega⟩ +
          (if h : k.val < n + 1 then cgAlpha n (k.val + 1) * ψ.2 ⟨k.val, by omega⟩ else 0)) +
        (cgBeta n (k.val + 1) * φ.1 ⟨k.val + 1, by omega⟩ +
          (if h : k.val < n + 1 then cgAlpha n (k.val + 1) * φ.2 ⟨k.val, by omega⟩ else 0))
      split_ifs <;> ring
  map_smul' a ψ := by
    ext ⟨k, s⟩
    fin_cases s
    · change cgAlpha n k.val * (a * ψ.1 ⟨k.val, by omega⟩) -
          (if h : 0 < k.val then cgBeta n k.val * (a * ψ.2 ⟨k.val - 1, by omega⟩) else 0) =
        a * (cgAlpha n k.val * ψ.1 ⟨k.val, by omega⟩ -
          (if h : 0 < k.val then cgBeta n k.val * ψ.2 ⟨k.val - 1, by omega⟩ else 0))
      split_ifs <;> ring
    · change cgBeta n (k.val + 1) * (a * ψ.1 ⟨k.val + 1, by omega⟩) +
          (if h : k.val < n + 1 then cgAlpha n (k.val + 1) * (a * ψ.2 ⟨k.val, by omega⟩) else 0) =
        a * (cgBeta n (k.val + 1) * ψ.1 ⟨k.val + 1, by omega⟩ +
          (if h : k.val < n + 1 then cgAlpha n (k.val + 1) * ψ.2 ⟨k.val, by omega⟩ else 0))
      split_ifs <;> ring

/-- Inverse unitary Clebsch--Gordan transformation from uncoupled `j ⊗ 1/2` to `(j + 1/2) ⊕ (j - 1/2)`. -/
def cgCouplingForward (n : ℕ) : SpinTensorHalfSpace n →ₗ[ℂ] CoupledHalfSpace n where
  toFun ϕ :=
    ( fun p =>
        (if hp1 : p.val < n + 2 then cgAlpha n p.val * ϕ (⟨p.val, hp1⟩, 0) else 0) +
        (if hp2 : 0 < p.val then cgBeta n p.val * ϕ (⟨p.val - 1, by omega⟩, 1) else 0),
      fun q =>
        -cgBeta n (q.val + 1) * ϕ (⟨q.val + 1, by omega⟩, 0) +
        cgAlpha n (q.val + 1) * ϕ (⟨q.val, by omega⟩, 1) )
  map_add' ϕ₁ ϕ₂ := by
    ext p
    · change (if hp1 : p.val < n + 2 then cgAlpha n p.val * (ϕ₁ (⟨p.val, hp1⟩, 0) + ϕ₂ (⟨p.val, hp1⟩, 0)) else 0) +
          (if hp2 : 0 < p.val then cgBeta n p.val * (ϕ₁ (⟨p.val - 1, by omega⟩, 1) + ϕ₂ (⟨p.val - 1, by omega⟩, 1)) else 0) =
        ((if hp1 : p.val < n + 2 then cgAlpha n p.val * ϕ₁ (⟨p.val, hp1⟩, 0) else 0) +
          (if hp2 : 0 < p.val then cgBeta n p.val * ϕ₁ (⟨p.val - 1, by omega⟩, 1) else 0)) +
        ((if hp1 : p.val < n + 2 then cgAlpha n p.val * ϕ₂ (⟨p.val, hp1⟩, 0) else 0) +
          (if hp2 : 0 < p.val then cgBeta n p.val * ϕ₂ (⟨p.val - 1, by omega⟩, 1) else 0))
      split_ifs <;> ring
    · simp; ring
  map_smul' a ϕ := by
    ext p
    · change (if hp1 : p.val < n + 2 then cgAlpha n p.val * (a * ϕ (⟨p.val, hp1⟩, 0)) else 0) +
          (if hp2 : 0 < p.val then cgBeta n p.val * (a * ϕ (⟨p.val - 1, by omega⟩, 1)) else 0) =
        a * ((if hp1 : p.val < n + 2 then cgAlpha n p.val * ϕ (⟨p.val, hp1⟩, 0) else 0) +
          (if hp2 : 0 < p.val then cgBeta n p.val * ϕ (⟨p.val - 1, by omega⟩, 1) else 0))
      split_ifs <;> ring
    · simp; ring

theorem cgCouplingForward_backward (n : ℕ) (ψ : CoupledHalfSpace n) :
    cgCouplingForward n (cgCouplingBackward n ψ) = ψ := by
  ext p
  · dsimp [cgCouplingForward, cgCouplingBackward]
    by_cases hp1 : p.val < n + 2 <;> by_cases hp2 : 0 < p.val
    · have hp_le : p.val ≤ n + 2 := Nat.le_of_lt hp1
      have hid1 : (⟨p.val - 1 + 1, by omega⟩ : Fin (n + 3)) = p := by ext; dsimp; omega
      have hlt : p.val - 1 < n + 1 := by omega
      have hsucc : p.val - 1 + 1 = p.val := by omega
      simp only [hp1, hp2, hlt, ↓reduceDIte, hsucc, hid1]
      have hsq := cgAlpha_sq_add_cgBeta_sq hp_le
      linear_combination (ψ.1 p) * hsq
    · have hp0 : p.val = 0 := by omega
      have hpz : p = ⟨0, Nat.succ_pos (n + 2)⟩ := Fin.ext hp0
      simp [hpz]
    · have hpeq : p.val = n + 2 := by omega
      have hpt : p = ⟨n + 2, Nat.lt_succ_self (n + 2)⟩ := Fin.ext hpeq
      simp [hpt]
    · omega
  · dsimp [cgCouplingForward, cgCouplingBackward]
    have hq_le : p.val + 1 ≤ n + 2 := by omega
    have hlt : p.val < n + 1 := p.isLt
    simp only [hlt, ↓reduceIte]
    have hsq := cgAlpha_sq_add_cgBeta_sq hq_le
    linear_combination (ψ.2 p) * hsq

theorem cgCouplingBackward_forward (n : ℕ) (ϕ : SpinTensorHalfSpace n) :
    cgCouplingBackward n (cgCouplingForward n ϕ) = ϕ := by
  ext ⟨k, s⟩
  fin_cases s
  · dsimp [cgCouplingBackward, cgCouplingForward]
    by_cases hk0 : 0 < k.val
    · have hk1 : k.val < n + 2 := k.isLt
      have hk_le : k.val ≤ n + 2 := Nat.le_of_lt hk1
      have hidx1 : (⟨k.val - 1 + 1, by omega⟩ : Fin (n + 2)) = k := by ext; dsimp; omega
      simp only [hk0, hk1, ↓reduceDIte, ↓reduceIte, hidx1]
      have hsub : k.val - 1 + 1 = k.val := by omega
      rw [hsub]
      have hsq := cgAlpha_sq_add_cgBeta_sq hk_le
      linear_combination (ϕ (k, 0)) * hsq
    · have hk_eq : k.val = 0 := by omega
      have hkz : k = ⟨0, Nat.succ_pos (n + 1)⟩ := Fin.ext hk_eq
      simp [hkz]
  · dsimp [cgCouplingBackward, cgCouplingForward]
    by_cases hk1 : k.val < n + 1
    · have hk_le : k.val + 1 ≤ n + 2 := by omega
      have hklt2 : k.val + 1 < n + 2 := by omega
      simp only [hk1, hklt2, ↓reduceDIte]
      have hsq := cgAlpha_sq_add_cgBeta_sq hk_le
      linear_combination (ϕ (k, 1)) * hsq
    · have hkeq : k.val = n + 1 := by omega
      have hkt : k = ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := Fin.ext hkeq
      simp [hkt]

/-- Exact Clebsch--Gordan linear equivalence `j ⊗ 1/2 ≃ (j + 1/2) ⊕ (j - 1/2)`. -/
def cgCouplingEquiv (n : ℕ) : SpinTensorHalfSpace n ≃ₗ[ℂ] CoupledHalfSpace n where
  toFun := cgCouplingForward n
  invFun := cgCouplingBackward n
  left_inv := cgCouplingBackward_forward n
  right_inv := cgCouplingForward_backward n
  map_add' := (cgCouplingForward n).map_add
  map_smul' := (cgCouplingForward n).map_smul

/-- Standard Hermitian inner product on `SpinTensorHalfSpace n`. -/
def tensorInner (n : ℕ) (u v : SpinTensorHalfSpace n) : ℂ :=
  ∑ x : Fin (n + 2) × Fin 2, star (u x) * v x

/-- Standard Hermitian inner product on `CoupledHalfSpace n`. -/
def coupledInner (n : ℕ) (f g : CoupledHalfSpace n) : ℂ :=
  (∑ p : Fin (n + 3), star (f.1 p) * g.1 p) + (∑ q : Fin (n + 1), star (f.2 q) * g.2 q)

/-- Exact unitarity (isometry & orthogonality preservation) of `cgCouplingBackward n`. -/
theorem cgCouplingBackward_unitary (n : ℕ) (f g : CoupledHalfSpace n) :
    tensorInner n (cgCouplingBackward n f) (cgCouplingBackward n g) = coupledInner n f g := by
  unfold tensorInner coupledInner
  rw [Fintype.sum_prod_type]
  have hprod : ∀ x : Fin (n + 2),
      (star (cgCouplingBackward n f (x, 0)) * cgCouplingBackward n g (x, 0) +
        star (cgCouplingBackward n f (x, 1)) * cgCouplingBackward n g (x, 1)) =
      (star (f.1 ⟨x.val, by omega⟩) * g.1 ⟨x.val, by omega⟩ *
        (cgAlpha n x.val * cgAlpha n x.val) +
       star (f.1 ⟨x.val + 1, by omega⟩) * g.1 ⟨x.val + 1, by omega⟩ *
        (cgBeta n (x.val + 1) * cgBeta n (x.val + 1))) +
      (if h0 : 0 < x.val then
        star (f.2 ⟨x.val - 1, by omega⟩) * g.2 ⟨x.val - 1, by omega⟩ *
          (cgBeta n x.val * cgBeta n x.val) -
        (star (f.1 ⟨x.val, by omega⟩) * g.2 ⟨x.val - 1, by omega⟩ +
          star (f.2 ⟨x.val - 1, by omega⟩) * g.1 ⟨x.val, by omega⟩) *
          (cgAlpha n x.val * cgBeta n x.val)
       else 0) +
      (if h1 : x.val < n + 1 then
        star (f.2 ⟨x.val, by omega⟩) * g.2 ⟨x.val, by omega⟩ *
          (cgAlpha n (x.val + 1) * cgAlpha n (x.val + 1)) +
        (star (f.1 ⟨x.val + 1, by omega⟩) * g.2 ⟨x.val, by omega⟩ +
          star (f.2 ⟨x.val, by omega⟩) * g.1 ⟨x.val + 1, by omega⟩) *
          (cgAlpha n (x.val + 1) * cgBeta n (x.val + 1))
       else 0) := by
    intro x
    dsimp [cgCouplingBackward]
    have hsa : ∀ m, (starRingEnd ℂ) (cgAlpha n m) = cgAlpha n m := star_cgAlpha n
    have hsb : ∀ m, (starRingEnd ℂ) (cgBeta n m) = cgBeta n m := star_cgBeta n
    by_cases h0 : 0 < x.val <;> by_cases h1 : x.val < n + 1 <;>
      simp [h0, h1, hsa, hsb] <;> ring
  have hsum_k : ∑ x : Fin (n + 2),
      (star (cgCouplingBackward n f (x, 0)) * cgCouplingBackward n g (x, 0) +
        star (cgCouplingBackward n f (x, 1)) * cgCouplingBackward n g (x, 1)) =
      (∑ x : Fin (n + 2),
        star (f.1 ⟨x.val, by omega⟩) * g.1 ⟨x.val, by omega⟩ *
          (cgAlpha n x.val * cgAlpha n x.val)) +
      (∑ x : Fin (n + 2),
        star (f.1 ⟨x.val + 1, by omega⟩) * g.1 ⟨x.val + 1, by omega⟩ *
          (cgBeta n (x.val + 1) * cgBeta n (x.val + 1))) +
      (∑ x : Fin (n + 2), if h0 : 0 < x.val then
        star (f.2 ⟨x.val - 1, by omega⟩) * g.2 ⟨x.val - 1, by omega⟩ *
          (cgBeta n x.val * cgBeta n x.val) -
        (star (f.1 ⟨x.val, by omega⟩) * g.2 ⟨x.val - 1, by omega⟩ +
          star (f.2 ⟨x.val - 1, by omega⟩) * g.1 ⟨x.val, by omega⟩) *
          (cgAlpha n x.val * cgBeta n x.val)
       else 0) +
      (∑ x : Fin (n + 2), if h1 : x.val < n + 1 then
        star (f.2 ⟨x.val, by omega⟩) * g.2 ⟨x.val, by omega⟩ *
          (cgAlpha n (x.val + 1) * cgAlpha n (x.val + 1)) +
        (star (f.1 ⟨x.val + 1, by omega⟩) * g.2 ⟨x.val, by omega⟩ +
          star (f.2 ⟨x.val, by omega⟩) * g.1 ⟨x.val + 1, by omega⟩) *
          (cgAlpha n (x.val + 1) * cgBeta n (x.val + 1))
       else 0) := by
    simp_rw [hprod, Finset.sum_add_distrib]
  have hsum_flip : (∑ x : Fin (n + 2),
      (star (cgCouplingBackward n f (x, 0)) * cgCouplingBackward n g (x, 0) +
       star (cgCouplingBackward n f (x, 1)) * cgCouplingBackward n g (x, 1))) =
      (∑ x : Fin (n + 2), ∑ y : Fin 2,
        star (cgCouplingBackward n f (x, y)) * cgCouplingBackward n g (x, y)) := by
    refine Finset.sum_congr rfl ?_
    intro x _; simp [Fin.sum_univ_two]
  rw [← hsum_flip, hsum_k]
  have hA : ∑ x : Fin (n + 2),
      star (f.1 ⟨x.val, by omega⟩) * g.1 ⟨x.val, by omega⟩ *
        (cgAlpha n x.val * cgAlpha n x.val) =
      ∑ p : Fin (n + 3),
        star (f.1 p) * g.1 p * (cgAlpha n p.val * cgAlpha n p.val) := by
    conv_rhs => rw [Fin.sum_univ_castSucc]
    have htop : star (f.1 (Fin.last (n + 2))) * g.1 (Fin.last (n + 2)) *
        (cgAlpha n (Fin.last (n + 2)).val * cgAlpha n (Fin.last (n + 2)).val) = 0 := by
      simp
    rw [htop, add_zero]
    refine Finset.sum_congr rfl ?_
    intro x _; rfl
  have hB : ∑ x : Fin (n + 2),
      star (f.1 ⟨x.val + 1, by omega⟩) * g.1 ⟨x.val + 1, by omega⟩ *
        (cgBeta n (x.val + 1) * cgBeta n (x.val + 1)) =
      ∑ p : Fin (n + 3),
        star (f.1 p) * g.1 p * (cgBeta n p.val * cgBeta n p.val) := by
    conv_rhs => rw [Fin.sum_univ_succ]
    have hbot : star (f.1 0) * g.1 0 * (cgBeta n (0 : Fin (n + 3)).val * cgBeta n (0 : Fin (n + 3)).val) = 0 := by
      simp
    rw [hbot, zero_add]
    refine Finset.sum_congr rfl ?_
    intro x _; rfl
  have hC : (∑ x : Fin (n + 2), if h0 : 0 < x.val then
        star (f.2 ⟨x.val - 1, by omega⟩) * g.2 ⟨x.val - 1, by omega⟩ *
          (cgBeta n x.val * cgBeta n x.val) -
        (star (f.1 ⟨x.val, by omega⟩) * g.2 ⟨x.val - 1, by omega⟩ +
          star (f.2 ⟨x.val - 1, by omega⟩) * g.1 ⟨x.val, by omega⟩) *
          (cgAlpha n x.val * cgBeta n x.val)
       else 0) =
      ∑ q : Fin (n + 1),
        (star (f.2 q) * g.2 q * (cgBeta n (q.val + 1) * cgBeta n (q.val + 1)) -
         (star (f.1 ⟨q.val + 1, by omega⟩) * g.2 q +
          star (f.2 q) * g.1 ⟨q.val + 1, by omega⟩) *
          (cgAlpha n (q.val + 1) * cgBeta n (q.val + 1))) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, lt_self_iff_false, ↓reduceDIte, zero_add, Fin.val_succ,
      Nat.succ_pos, Nat.add_sub_cancel, Fin.eta]
  have hD : (∑ x : Fin (n + 2), if h1 : x.val < n + 1 then
        star (f.2 ⟨x.val, by omega⟩) * g.2 ⟨x.val, by omega⟩ *
          (cgAlpha n (x.val + 1) * cgAlpha n (x.val + 1)) +
        (star (f.1 ⟨x.val + 1, by omega⟩) * g.2 ⟨x.val, by omega⟩ +
          star (f.2 ⟨x.val, by omega⟩) * g.1 ⟨x.val + 1, by omega⟩) *
          (cgAlpha n (x.val + 1) * cgBeta n (x.val + 1))
       else 0) =
      ∑ q : Fin (n + 1),
        (star (f.2 q) * g.2 q * (cgAlpha n (q.val + 1) * cgAlpha n (q.val + 1)) +
         (star (f.1 ⟨q.val + 1, by omega⟩) * g.2 q +
          star (f.2 q) * g.1 ⟨q.val + 1, by omega⟩) *
          (cgAlpha n (q.val + 1) * cgBeta n (q.val + 1))) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, add_zero, Fin.val_castSucc,
      Fin.isLt, Fin.eta]
  rw [hA, hB, hC, hD]
  have hP : ∑ p : Fin (n + 3), star (f.1 p) * g.1 p * (cgAlpha n p.val * cgAlpha n p.val) +
      ∑ p : Fin (n + 3), star (f.1 p) * g.1 p * (cgBeta n p.val * cgBeta n p.val) =
      ∑ p : Fin (n + 3), star (f.1 p) * g.1 p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    have hsq := cgAlpha_sq_add_cgBeta_sq (n := n) (p := p.val) (by omega)
    calc
      star (f.1 p) * g.1 p * (cgAlpha n p.val * cgAlpha n p.val) +
          star (f.1 p) * g.1 p * (cgBeta n p.val * cgBeta n p.val)
          = star (f.1 p) * g.1 p * (cgAlpha n p.val * cgAlpha n p.val +
              cgBeta n p.val * cgBeta n p.val) := by ring
      _ = star (f.1 p) * g.1 p := by rw [hsq, mul_one]
  have hQ : (∑ q : Fin (n + 1),
        (star (f.2 q) * g.2 q * (cgBeta n (q.val + 1) * cgBeta n (q.val + 1)) -
         (star (f.1 ⟨q.val + 1, by omega⟩) * g.2 q +
          star (f.2 q) * g.1 ⟨q.val + 1, by omega⟩) *
          (cgAlpha n (q.val + 1) * cgBeta n (q.val + 1)))) +
      (∑ q : Fin (n + 1),
        (star (f.2 q) * g.2 q * (cgAlpha n (q.val + 1) * cgAlpha n (q.val + 1)) +
         (star (f.1 ⟨q.val + 1, by omega⟩) * g.2 q +
          star (f.2 q) * g.1 ⟨q.val + 1, by omega⟩) *
          (cgAlpha n (q.val + 1) * cgBeta n (q.val + 1)))) =
      ∑ q : Fin (n + 1), star (f.2 q) * g.2 q := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro q _
    have hsq := cgAlpha_sq_add_cgBeta_sq (n := n) (p := q.val + 1) (by omega)
    calc
      (star (f.2 q) * g.2 q * (cgBeta n (q.val + 1) * cgBeta n (q.val + 1)) -
        (star (f.1 ⟨q.val + 1, by omega⟩) * g.2 q +
          star (f.2 q) * g.1 ⟨q.val + 1, by omega⟩) *
          (cgAlpha n (q.val + 1) * cgBeta n (q.val + 1))) +
      (star (f.2 q) * g.2 q * (cgAlpha n (q.val + 1) * cgAlpha n (q.val + 1)) +
        (star (f.1 ⟨q.val + 1, by omega⟩) * g.2 q +
          star (f.2 q) * g.1 ⟨q.val + 1, by omega⟩) *
          (cgAlpha n (q.val + 1) * cgBeta n (q.val + 1)))
          = star (f.2 q) * g.2 q *
              (cgAlpha n (q.val + 1) * cgAlpha n (q.val + 1) +
               cgBeta n (q.val + 1) * cgBeta n (q.val + 1)) := by ring
      _ = star (f.2 q) * g.2 q := by rw [hsq, mul_one]
  linear_combination hP + hQ

theorem cgCouplingForward_unitary (n : ℕ) (u v : SpinTensorHalfSpace n) :
    coupledInner n (cgCouplingForward n u) (cgCouplingForward n v) = tensorInner n u v := by
  have h := cgCouplingBackward_unitary n (cgCouplingForward n u) (cgCouplingForward n v)
  rw [cgCouplingBackward_forward, cgCouplingBackward_forward] at h
  exact h.symm

/-- Total angular momentum `J_z = J_{1z} ⊗ 1 + 1 ⊗ J_{2z}` on `SpinTensorHalfSpace n`. -/
def tensorHalfZ (n : ℕ) : Module.End ℂ (SpinTensorHalfSpace n) where
  toFun ϕ ks := (spinMValue (n + 1) ks.1 + spinMValue 1 ks.2) * ϕ ks
  map_add' ϕ₁ ϕ₂ := by ext ks; simp [mul_add]
  map_smul' a ϕ := by ext ks; simp; ring

/-- Total raising operator `J_+ = J_{1+} ⊗ 1 + 1 ⊗ J_{2+}` on `SpinTensorHalfSpace n`. -/
def tensorHalfPlus (n : ℕ) : Module.End ℂ (SpinTensorHalfSpace n) where
  toFun ϕ ks :=
    (spinPlus (n + 1) (fun k' => ϕ (k', ks.2))) ks.1 +
    (spinPlus 1 (fun s' => ϕ (ks.1, s'))) ks.2
  map_add' ϕ₁ ϕ₂ := by
    ext ⟨k, s⟩
    change (spinPlus (n + 1) (fun k' => ϕ₁ (k', s) + ϕ₂ (k', s))) k +
        (spinPlus 1 (fun s' => ϕ₁ (k, s') + ϕ₂ (k, s'))) s =
      ((spinPlus (n + 1) (fun k' => ϕ₁ (k', s))) k + (spinPlus 1 (fun s' => ϕ₁ (k, s'))) s) +
      ((spinPlus (n + 1) (fun k' => ϕ₂ (k', s))) k + (spinPlus 1 (fun s' => ϕ₂ (k, s'))) s)
    simp only [spinPlus_apply]
    fin_cases s <;> split_ifs <;> ring
  map_smul' a ϕ := by
    ext ⟨k, s⟩
    change (spinPlus (n + 1) (fun k' => a * ϕ (k', s))) k +
        (spinPlus 1 (fun s' => a * ϕ (k, s'))) s =
      a * ((spinPlus (n + 1) (fun k' => ϕ (k', s))) k + (spinPlus 1 (fun s' => ϕ (k, s'))) s)
    simp only [spinPlus_apply]
    fin_cases s <;> split_ifs <;> ring

/-- Total lowering operator `J_- = J_{1-} ⊗ 1 + 1 ⊗ J_{2-}` on `SpinTensorHalfSpace n`. -/
def tensorHalfMinus (n : ℕ) : Module.End ℂ (SpinTensorHalfSpace n) where
  toFun ϕ ks :=
    (spinMinus (n + 1) (fun k' => ϕ (k', ks.2))) ks.1 +
    (spinMinus 1 (fun s' => ϕ (ks.1, s'))) ks.2
  map_add' ϕ₁ ϕ₂ := by
    ext ⟨k, s⟩
    change (spinMinus (n + 1) (fun k' => ϕ₁ (k', s) + ϕ₂ (k', s))) k +
        (spinMinus 1 (fun s' => ϕ₁ (k, s') + ϕ₂ (k, s'))) s =
      ((spinMinus (n + 1) (fun k' => ϕ₁ (k', s))) k + (spinMinus 1 (fun s' => ϕ₁ (k, s'))) s) +
      ((spinMinus (n + 1) (fun k' => ϕ₂ (k', s))) k + (spinMinus 1 (fun s' => ϕ₂ (k, s'))) s)
    simp only [spinMinus_apply]
    fin_cases s <;> split_ifs <;> ring
  map_smul' a ϕ := by
    ext ⟨k, s⟩
    change (spinMinus (n + 1) (fun k' => a * ϕ (k', s))) k +
        (spinMinus 1 (fun s' => a * ϕ (k, s'))) s =
      a * ((spinMinus (n + 1) (fun k' => ϕ (k', s))) k + (spinMinus 1 (fun s' => ϕ (k, s'))) s)
    simp only [spinMinus_apply]
    fin_cases s <;> split_ifs <;> ring

/-- Total Casimir `J^2 = J_z^2 + (1/2)(J_+ J_- + J_- J_+)` on `SpinTensorHalfSpace n`. -/
def tensorHalfCasimir (n : ℕ) : Module.End ℂ (SpinTensorHalfSpace n) :=
  tensorHalfZ n * tensorHalfZ n +
    (1 / 2 : ℂ) • (tensorHalfPlus n * tensorHalfMinus n + tensorHalfMinus n * tensorHalfPlus n)

theorem cgCoupling_intertwines_J_zero (n : ℕ) (ψ : CoupledHalfSpace n) :
    tensorHalfZ n (cgCouplingBackward n ψ) =
      cgCouplingBackward n (spinZ (n + 2) ψ.1, spinZ n ψ.2) := by
  ext ⟨k, s⟩
  fin_cases s
  · by_cases h0 : 0 < k.val
    · simp only [tensorHalfZ, cgCouplingBackward, spinZ, spinMValue, LinearMap.coe_mk,
        AddHom.coe_mk, h0, ↓reduceDIte]
      have hsub : ((k.val - 1 : ℕ) : ℂ) = (k.val : ℂ) - 1 := by
        rw [Nat.cast_sub h0]; simp
      rw [hsub]
      push_cast
      ring
    · have hk0 : k.val = 0 := by omega
      obtain rfl : k = ⟨0, Nat.succ_pos (n + 1)⟩ := Fin.ext hk0
      simp only [tensorHalfZ, cgCouplingBackward, spinZ, spinMValue, LinearMap.coe_mk,
        AddHom.coe_mk, Fin.ext_iff, Fin.val_zero]
      split_ifs <;> (try first | contradiction | omega) <;> (push_cast; ring)
  · by_cases h1 : k.val < n + 1
    · simp only [tensorHalfZ, cgCouplingBackward, spinZ, spinMValue, LinearMap.coe_mk,
        AddHom.coe_mk, h1, ↓reduceDIte]
      push_cast
      ring
    · have hk_top : k.val = n + 1 := by omega
      obtain rfl : k = ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := Fin.ext hk_top
      simp only [tensorHalfZ, cgCouplingBackward, spinZ, spinMValue, LinearMap.coe_mk,
        AddHom.coe_mk, Fin.ext_iff, Fin.val_zero]
      split_ifs <;> (try first | contradiction | omega) <;> (push_cast; ring)

private theorem cg_plus_coeff_plus_0 (n k : ℕ) (hk : k < n + 1) :
    spinPlusCoeff (n + 1) k * cgAlpha n (k + 1) + cgBeta n (k + 1) =
      cgAlpha n k * spinPlusCoeff (n + 2) k := by
  unfold spinPlusCoeff cgAlpha cgBeta
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hk_le : (k : ℝ) ≤ n + 1 := by exact_mod_cast (Nat.le_of_lt hk)
  have lhs_eq :
      Real.sqrt (((k : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) - k)) *
          Real.sqrt (((n : ℝ) + 2 - ((k + 1 : ℕ) : ℝ)) / ((n : ℝ) + 2)) +
        Real.sqrt (((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)) =
      ((n : ℝ) + 2 - k) * Real.sqrt (((k + 1 : ℝ)) / ((n : ℝ) + 2)) := by
    rw [← Real.sqrt_mul (by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - k := by push_cast; linarith
      positivity)]
    have hre : (((k : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) - k)) *
        (((n : ℝ) + 2 - ((k + 1 : ℕ) : ℝ)) / ((n : ℝ) + 2)) =
        (((k : ℝ) + 1) / ((n : ℝ) + 2)) * ((n : ℝ) + 1 - k) ^ 2 := by
      push_cast; ring
    rw [hre, Real.sqrt_mul (div_nonneg (by positivity) (le_of_lt hden)),
      Real.sqrt_sq (by linarith)]
    push_cast
    ring
  have rhs_eq :
      Real.sqrt (((n : ℝ) + 2 - k) / ((n : ℝ) + 2)) *
          Real.sqrt (((k : ℝ) + 1) * (((n + 2 : ℕ) : ℝ) - k)) =
      ((n : ℝ) + 2 - k) * Real.sqrt (((k + 1 : ℝ)) / ((n : ℝ) + 2)) := by
    rw [← Real.sqrt_mul (div_nonneg (by linarith) (le_of_lt hden))]
    have hre : (((n : ℝ) + 2 - k) / ((n : ℝ) + 2)) *
        (((k : ℝ) + 1) * (((n + 2 : ℕ) : ℝ) - k)) =
        (((k : ℝ) + 1) / ((n : ℝ) + 2)) * ((n : ℝ) + 2 - k) ^ 2 := by
      push_cast; ring
    rw [hre, Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
    ring
  exact_mod_cast (lhs_eq.trans rhs_eq.symm)

private theorem cg_plus_coeff_minus_0 (n k : ℕ) (hk0 : 0 < k) (hk : k < n + 1) :
    -(spinPlusCoeff (n + 1) k * cgBeta n (k + 1)) + cgAlpha n (k + 1) =
      -(cgBeta n k * spinPlusCoeff n (k - 1)) := by
  unfold spinPlusCoeff cgAlpha cgBeta
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hk_le : (k : ℝ) ≤ n + 1 := by exact_mod_cast (Nat.le_of_lt hk)
  have hsub1 : (((k - 1 : ℕ) : ℝ) + 1) = k := by
    have : (k - 1 + 1 : ℕ) = k := Nat.sub_add_cancel hk0
    exact_mod_cast this
  have hsub2 : ((n : ℝ) - ((k - 1 : ℕ) : ℝ)) = (n : ℝ) + 1 - k := by
    rw [Nat.cast_sub hk0]; push_cast; ring
  have lhs_eq :
      -(Real.sqrt (((k : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) - k)) *
          Real.sqrt (((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 2))) +
        Real.sqrt (((n : ℝ) + 2 - ((k + 1 : ℕ) : ℝ)) / ((n : ℝ) + 2)) =
      -(k * Real.sqrt (((n : ℝ) + 1 - k) / ((n : ℝ) + 2))) := by
    rw [← Real.sqrt_mul (by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - k := by push_cast; linarith
      positivity)]
    have hre1 : (((k : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) - k)) *
        (((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)) =
        (((n : ℝ) + 1 - k) / ((n : ℝ) + 2)) * ((k : ℝ) + 1) ^ 2 := by
      push_cast; ring
    have hre2 : ((n : ℝ) + 2 - ((k + 1 : ℕ) : ℝ)) / ((n : ℝ) + 2) =
        ((n : ℝ) + 1 - k) / ((n : ℝ) + 2) := by
      push_cast; ring
    rw [hre1, hre2, Real.sqrt_mul (div_nonneg (by linarith) (le_of_lt hden)),
      Real.sqrt_sq (by positivity)]
    ring
  have rhs_eq :
      -(Real.sqrt ((k : ℝ) / ((n : ℝ) + 2)) *
          Real.sqrt ((((k - 1 : ℕ) : ℝ) + 1) * ((n : ℝ) - ((k - 1 : ℕ) : ℝ)))) =
      -(k * Real.sqrt (((n : ℝ) + 1 - k) / ((n : ℝ) + 2))) := by
    rw [hsub1, hsub2, ← Real.sqrt_mul (div_nonneg (Nat.cast_nonneg k) (le_of_lt hden))]
    have hre : ((k : ℝ) / ((n : ℝ) + 2)) * ((k : ℝ) * ((n : ℝ) + 1 - k)) =
        (((n : ℝ) + 1 - k) / ((n : ℝ) + 2)) * (k : ℝ) ^ 2 := by
      ring
    rw [hre, Real.sqrt_mul (div_nonneg (by linarith) (le_of_lt hden)),
      Real.sqrt_sq (Nat.cast_nonneg k)]
    ring
  exact_mod_cast (lhs_eq.trans rhs_eq.symm)

private theorem cg_plus_coeff_plus_1 (n k : ℕ) (hk : k < n + 1) :
    spinPlusCoeff (n + 1) k * cgBeta n (k + 2) =
      cgBeta n (k + 1) * spinPlusCoeff (n + 2) (k + 1) := by
  unfold spinPlusCoeff cgBeta
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hk_le : (k : ℝ) ≤ n + 1 := by exact_mod_cast (Nat.le_of_lt hk)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.sqrt_mul (by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - k := by push_cast; linarith
      positivity),
    ← Real.sqrt_mul (div_nonneg (by positivity) (le_of_lt hden))]
  congr 1
  push_cast
  ring

private theorem cg_plus_coeff_minus_1 (n k : ℕ) (hk : k < n) :
    spinPlusCoeff (n + 1) k * cgAlpha n (k + 2) =
      cgAlpha n (k + 1) * spinPlusCoeff n k := by
  unfold spinPlusCoeff cgAlpha
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hk_le : (k : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt hk)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.sqrt_mul (by
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - k := by push_cast; linarith
      positivity),
    ← Real.sqrt_mul (div_nonneg (by push_cast; linarith) (le_of_lt hden))]
  congr 1
  push_cast
  ring

theorem cgCoupling_intertwines_J_plus (n : ℕ) (ψ : CoupledHalfSpace n) :
    tensorHalfPlus n (cgCouplingBackward n ψ) =
      cgCouplingBackward n (spinPlus (n + 2) ψ.1, spinPlus n ψ.2) := by
  have h2_0 : ∀ h : 0 < 2, ((⟨0, h⟩ : Fin 2) = 0) ↔ True := fun _ => by simp
  have h2_1 : ∀ h : 1 < 2, ((⟨1, h⟩ : Fin 2) = 0) ↔ False :=
    fun _ => ⟨fun he => Nat.one_ne_zero (congrArg Fin.val he), False.elim⟩
  have h01 : (0 : ℕ) < 1 := Nat.zero_lt_one
  ext ⟨k, s⟩
  fin_cases s
  · by_cases hk : k.val < n + 1
    · have hk_lt2 : k.val < n + 2 := by omega
      have hpos_k1 : 0 < k.val + 1 := Nat.succ_pos k.val
      simp only [tensorHalfPlus, cgCouplingBackward, spinPlus, LinearMap.coe_mk, AddHom.coe_mk,
        hk, hk_lt2, hpos_k1, h01, h2_0, h2_1, ↓reduceDIte, ↓reduceIte]
      have hs1 : spinPlusCoeff 1 0 = 1 := by unfold spinPlusCoeff; norm_num
      simp only [hs1, one_mul, Nat.add_sub_cancel]
      by_cases hk0 : 0 < k.val
      · have hk_lt_n : k.val - 1 < n := by omega
        have hidx : (⟨k.val - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨k.val, hk⟩ := by
          ext; dsimp; omega
        simp only [hk0, hk_lt_n, ↓reduceDIte, hidx]
        have hp1 := cg_plus_coeff_plus_0 n k.val hk
        have hm1 := cg_plus_coeff_minus_0 n k.val hk0 hk
        linear_combination (ψ.1 ⟨k.val + 1, by omega⟩) * hp1 +
          (ψ.2 ⟨k.val, hk⟩) * hm1
      · have hk_eq : k.val = 0 := by omega
        simp only [hk_eq, zero_add]
        have hnot0 : ¬ (0 : ℕ) < 0 := by omega
        simp only [hnot0, ↓reduceDIte, sub_zero]
        have hcz : -((spinPlusCoeff (n + 1) 0 * cgBeta n 1) * ψ.2 ⟨0, Nat.succ_pos n⟩) +
            cgAlpha n 1 * ψ.2 ⟨0, Nat.succ_pos n⟩ = 0 := by
          have hsq1 : spinPlusCoeff (n + 1) 0 = Real.sqrt ((n : ℝ) + 1) := by
            unfold spinPlusCoeff; norm_num
          have hbet : cgBeta n 1 = 1 / ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ) := by
            unfold cgBeta; simp [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1)]
          have halp : cgAlpha n 1 = ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) /
              ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ) := by
            unfold cgAlpha
            have hnum : (n : ℝ) + 2 - ((1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num; ring
            rw [hnum, Real.sqrt_div (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
            simp
          rw [hsq1, hbet, halp]; ring
        have hp1 := cg_plus_coeff_plus_0 n 0 (Nat.succ_pos n)
        linear_combination (ψ.1 ⟨1, by omega⟩) * hp1 + hcz
    · have hk_eq : k.val = n + 1 := by omega
      simp [tensorHalfPlus, cgCouplingBackward, spinPlus, hk_eq]
      have hs1 : spinPlusCoeff 1 0 = 1 := by unfold spinPlusCoeff; norm_num
      have hsp : spinPlusCoeff (n + 2) (n + 1) = ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ) := by
        unfold spinPlusCoeff
        have hre : (((n + 1 : ℕ) : ℝ) + 1) * (((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) =
            (n : ℝ) + 2 := by push_cast; ring
        rw [hre]
      have halp : cgAlpha n (n + 1) = 1 / ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ) := by
        unfold cgAlpha
        have hre : (n : ℝ) + 2 - ((n + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
        rw [hre, Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1)]
        simp
      rw [hs1, hsp, halp]
      have hne : ((Real.sqrt ((n : ℝ) + 2) : ℝ) : ℂ) ≠ 0 := by
        have hposr : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
        exact_mod_cast ne_of_gt hposr
      field_simp [hne]
  · by_cases hk : k.val < n + 1
    · have hlt2 : k.val + 1 < n + 2 := by omega
      simp only [tensorHalfPlus, cgCouplingBackward, spinPlus, LinearMap.coe_mk, AddHom.coe_mk,
        hk, hlt2, h2_1, ↓reduceDIte, ↓reduceIte]
      norm_num
      by_cases hkn : k.val < n
      · simp only [hkn, ↓reduceDIte]
        have hp2 := cg_plus_coeff_plus_1 n k.val hk
        have hm2 := cg_plus_coeff_minus_1 n k.val hkn
        linear_combination (ψ.1 ⟨k.val + 2, by omega⟩) * hp2 +
          (ψ.2 ⟨k.val + 1, by omega⟩) * hm2
      · have hkeq : k.val = n := by omega
        simp only [hkn, ↓reduceDIte, add_zero]
        have hp2 := cg_plus_coeff_plus_1 n k.val hk
        linear_combination (ψ.1 ⟨k.val + 2, by omega⟩) * hp2
    · have hk_eq : k.val = n + 1 := by omega
      simp [tensorHalfPlus, cgCouplingBackward, spinPlus, hk_eq]

/-- Standard Hermitian inner product on `SpinSpace twoI`. -/
def spinInner (twoI : ℕ) (u v : SpinSpace twoI) : ℂ :=
  ∑ k : Fin (twoI + 1), star (u k) * v k

theorem star_spinPlusCoeff (twoI k : ℕ) : star (spinPlusCoeff twoI k) = spinPlusCoeff twoI k := by
  unfold spinPlusCoeff; simp

theorem star_spinMinusCoeff (twoI k : ℕ) : star (spinMinusCoeff twoI k) = spinMinusCoeff twoI k := by
  unfold spinMinusCoeff; simp

theorem spinInner_spinPlus_eq_spinMinus (twoI : ℕ) (u v : SpinSpace twoI) :
    spinInner twoI (spinPlus twoI u) v = spinInner twoI u (spinMinus twoI v) := by
  unfold spinInner
  have hL : ∑ k : Fin (twoI + 1), star (spinPlus twoI u k) * v k =
      ∑ k : Fin twoI, spinPlusCoeff twoI k.val * star (u ⟨k.val + 1, by omega⟩) *
        v ⟨k.val, by omega⟩ := by
    rw [Fin.sum_univ_castSucc]
    have hlast : star (spinPlus twoI u (Fin.last twoI)) * v (Fin.last twoI) = 0 := by
      simp [spinPlus]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hsp : star (spinPlusCoeff twoI k.val) = spinPlusCoeff twoI k.val :=
      star_spinPlusCoeff twoI k.val
    have hvv : v k.castSucc = v ⟨k.val, by omega⟩ := congrArg v (Fin.ext rfl)
    simp only [spinPlus, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_castSucc]
    split_ifs with hlt
    · rw [hvv, star_mul', hsp]
    · exact absurd k.isLt hlt
  have hR : ∑ k : Fin (twoI + 1), star (u k) * spinMinus twoI v k =
      ∑ k : Fin twoI, spinPlusCoeff twoI k.val * star (u ⟨k.val + 1, by omega⟩) *
        v ⟨k.val, by omega⟩ := by
    rw [Fin.sum_univ_succ]
    have hzero : star (u 0) * spinMinus twoI v 0 = 0 := by
      simp [spinMinus]
    rw [hzero, zero_add]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hidx_succ : (⟨k.val + 1, by omega⟩ : Fin (twoI + 1)) = k.succ := Fin.ext (by simp)
    simp only [spinMinus, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_succ]
    split_ifs with hlt
    · simp only [Nat.add_sub_cancel, ← spinPlusCoeff_eq_spinMinusCoeff_succ, hidx_succ]
      ring
    · omega
  exact hL.trans hR.symm

theorem tensorInner_tensorHalfPlus_eq_tensorHalfMinus (n : ℕ) (u v : SpinTensorHalfSpace n) :
    tensorInner n (tensorHalfPlus n u) v = tensorInner n u (tensorHalfMinus n v) := by
  unfold tensorInner
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hL : ∑ x : Fin (n + 2), ∑ y : Fin 2, star (tensorHalfPlus n u (x, y)) * v (x, y) =
      (∑ y : Fin 2, ∑ x : Fin (n + 2),
        star (spinPlus (n + 1) (fun k' => u (k', y)) x) * v (x, y)) +
      (∑ x : Fin (n + 2), ∑ y : Fin 2,
        star (spinPlus 1 (fun s' => u (x, s')) y) * v (x, y)) := by
    simp only [tensorHalfPlus, LinearMap.coe_mk, AddHom.coe_mk, star_add, add_mul,
      Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  have hR : ∑ x : Fin (n + 2), ∑ y : Fin 2, star (u (x, y)) * tensorHalfMinus n v (x, y) =
      (∑ y : Fin 2, ∑ x : Fin (n + 2),
        star (u (x, y)) * spinMinus (n + 1) (fun k' => v (k', y)) x) +
      (∑ x : Fin (n + 2), ∑ y : Fin 2,
        star (u (x, y)) * spinMinus 1 (fun s' => v (x, s')) y) := by
    simp only [tensorHalfMinus, LinearMap.coe_mk, AddHom.coe_mk, mul_add,
      Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  rw [hL, hR]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro y _
    exact spinInner_spinPlus_eq_spinMinus (n + 1) (fun k' => u (k', y)) (fun k' => v (k', y))
  · refine Finset.sum_congr rfl ?_
    intro x _
    exact spinInner_spinPlus_eq_spinMinus 1 (fun s' => u (x, s')) (fun s' => v (x, s'))

theorem tensorInner_eq_zero_imp {n : ℕ} {w : SpinTensorHalfSpace n}
    (hw : ∀ u : SpinTensorHalfSpace n, tensorInner n u w = 0) : w = 0 := by
  ext ks
  have h := hw (Pi.single ks 1)
  simpa [tensorInner, Pi.single_apply] using h

theorem cgCoupling_intertwines_J_minus (n : ℕ) (ψ : CoupledHalfSpace n) :
    tensorHalfMinus n (cgCouplingBackward n ψ) =
      cgCouplingBackward n (spinMinus (n + 2) ψ.1, spinMinus n ψ.2) := by
  have hdiff : tensorHalfMinus n (cgCouplingBackward n ψ) -
      cgCouplingBackward n (spinMinus (n + 2) ψ.1, spinMinus n ψ.2) = 0 := by
    apply tensorInner_eq_zero_imp
    intro u
    have hu : u = cgCouplingBackward n (cgCouplingForward n u) :=
      (cgCouplingBackward_forward n u).symm
    set g := cgCouplingForward n u
    have hinner : tensorInner n (cgCouplingBackward n g)
        (tensorHalfMinus n (cgCouplingBackward n ψ) -
          cgCouplingBackward n (spinMinus (n + 2) ψ.1, spinMinus n ψ.2)) = 0 := by
      have hsub : ∀ a b : SpinTensorHalfSpace n,
          tensorInner n (cgCouplingBackward n g) (a - b) =
            tensorInner n (cgCouplingBackward n g) a -
              tensorInner n (cgCouplingBackward n g) b := by
        intro a b
        simp [tensorInner, mul_sub, Finset.sum_sub_distrib]
      rw [hsub, ← tensorInner_tensorHalfPlus_eq_tensorHalfMinus,
        cgCoupling_intertwines_J_plus, cgCouplingBackward_unitary, cgCouplingBackward_unitary]
      unfold coupledInner
      have h1 := spinInner_spinPlus_eq_spinMinus (n + 2) g.1 ψ.1
      have h2 := spinInner_spinPlus_eq_spinMinus n g.2 ψ.2
      unfold spinInner at h1 h2
      rw [h1, h2, sub_self]
    rw [← hu] at hinner
    exact hinner
  exact sub_eq_zero.mp hdiff

/-- Exact intertwining of the total Casimir `(J₁ + J₂)^2` with the direct sum Casimir
on `(j + 1/2) ⊕ (j - 1/2)`, giving eigenvalues `(j+1/2)(j+3/2)` and `(j-1/2)(j+1/2)`. -/
theorem cgCoupling_intertwines_Casimir (n : ℕ) (ψ : CoupledHalfSpace n) :
    tensorHalfCasimir n (cgCouplingBackward n ψ) =
      cgCouplingBackward n
        ((((n + 2 : ℂ) / 2) * ((n + 2 : ℂ) / 2 + 1)) • ψ.1,
         (((n : ℂ) / 2) * ((n : ℂ) / 2 + 1)) • ψ.2) := by
  have hzz : (tensorHalfZ n * tensorHalfZ n) (cgCouplingBackward n ψ) =
      cgCouplingBackward n ((spinZ (n + 2) * spinZ (n + 2)) ψ.1, (spinZ n * spinZ n) ψ.2) := by
    simp only [Module.End.mul_apply, cgCoupling_intertwines_J_zero]
  have hpm : (tensorHalfPlus n * tensorHalfMinus n) (cgCouplingBackward n ψ) =
      cgCouplingBackward n
        ((spinPlus (n + 2) * spinMinus (n + 2)) ψ.1, (spinPlus n * spinMinus n) ψ.2) := by
    simp only [Module.End.mul_apply, cgCoupling_intertwines_J_minus, cgCoupling_intertwines_J_plus]
  have hmp : (tensorHalfMinus n * tensorHalfPlus n) (cgCouplingBackward n ψ) =
      cgCouplingBackward n
        ((spinMinus (n + 2) * spinPlus (n + 2)) ψ.1, (spinMinus n * spinPlus n) ψ.2) := by
    simp only [Module.End.mul_apply, cgCoupling_intertwines_J_plus, cgCoupling_intertwines_J_minus]
  calc
    tensorHalfCasimir n (cgCouplingBackward n ψ)
        = (tensorHalfZ n * tensorHalfZ n) (cgCouplingBackward n ψ) +
            (1 / 2 : ℂ) • ((tensorHalfPlus n * tensorHalfMinus n) (cgCouplingBackward n ψ) +
              (tensorHalfMinus n * tensorHalfPlus n) (cgCouplingBackward n ψ)) := rfl
    _ = cgCouplingBackward n (spinCasimirOp (n + 2) ψ.1, spinCasimirOp n ψ.2) := by
          rw [hzz, hpm, hmp, ← map_add, ← map_smul, ← map_add]
          rfl
    _ = cgCouplingBackward n
          ((((n + 2 : ℂ) / 2) * ((n + 2 : ℂ) / 2 + 1)) • ψ.1,
           (((n : ℂ) / 2) * ((n : ℂ) / 2 + 1)) • ψ.2) := by
          have h1 : spinCasimirOp (n + 2) ψ.1 =
              ((((n : ℂ) + 2) / 2 * (((n : ℂ) + 2) / 2 + 1)) • ψ.1) := by
            rw [spinCasimirOp_eq_scalar]
            push_cast
            simp only [LinearMap.smul_apply, Module.End.one_apply]
          have h2 : spinCasimirOp n ψ.2 =
              ((((n : ℂ) / 2) * ((n : ℂ) / 2 + 1)) • ψ.2) := by
            rw [spinCasimirOp_eq_scalar]
            simp only [LinearMap.smul_apply, Module.End.one_apply]
          rw [h1, h2]

/-- Specialization `n = 0`: `1/2 ⊗ 1/2 → 1 ⊕ 0` (triplet eigenvalue `2`, singlet eigenvalue `0`). -/
theorem twoSpinHalf_cg_recoupling (ψTriplet : SpinSpace 2) (ψSinglet : SpinSpace 0) :
    tensorHalfCasimir 0 (cgCouplingBackward 0 (ψTriplet, ψSinglet)) =
      cgCouplingBackward 0 ((2 : ℂ) • ψTriplet, (0 : ℂ) • ψSinglet) ∧
    (∀ k : Fin 3, tensorInner 0
      (cgCouplingBackward 0 (spinKet 2 k, 0))
      (cgCouplingBackward 0 (0, spinKet 0 0)) = 0) := by
  refine ⟨?_, ?_⟩
  · have h := cgCoupling_intertwines_Casimir 0 (ψTriplet, ψSinglet)
    norm_num at h
    simpa using h
  · intro k
    rw [cgCouplingBackward_unitary]
    simp [coupledInner]

/-- Specialization `n = 1`: `1 ⊗ 1/2 → 3/2 ⊕ 1/2` (quartet eigenvalue `15/4`, doublet eigenvalue `3/4`). -/
theorem spinOneHalf_cg_recoupling (ψQuartet : SpinSpace 3) (ψDoublet : SpinSpace 1) :
    tensorHalfCasimir 1 (cgCouplingBackward 1 (ψQuartet, ψDoublet)) =
      cgCouplingBackward 1 (((15 / 4 : ℂ)) • ψQuartet, ((3 / 4 : ℂ)) • ψDoublet) ∧
    (∀ (p : Fin 4) (q : Fin 2), tensorInner 1
      (cgCouplingBackward 1 (spinKet 3 p, 0))
      (cgCouplingBackward 1 (0, spinKet 1 q)) = 0) := by
  refine ⟨?_, ?_⟩
  · have h := cgCoupling_intertwines_Casimir 1 (ψQuartet, ψDoublet)
    norm_num at h
    exact h
  · intro p q
    rw [cgCouplingBackward_unitary]
    simp [coupledInner]

-- -----------------------------------------------------------------------------
-- SECTION 4: Wigner--Eckart Selection & Factorization Theorems (Rank 0 & Rank 1)
-- -----------------------------------------------------------------------------

/-- **Wigner--Eckart Rank-0 Scalar Theorem (Schur's Lemma on `SpinSpace twoI`)**:
Any operator `S` commuting with `spinZ twoI` and `spinPlus twoI` (in particular any scalar
commuting with `(J_z, J_+, J_-)`) is an `M`-independent scalar multiple of the identity. -/
theorem wigner_eckart_rank0_scalar (twoI : ℕ) (S : Module.End ℂ (SpinSpace twoI))
    (hcommZ : spinZ twoI * S = S * spinZ twoI)
    (hcommP : spinPlus twoI * S = S * spinPlus twoI) :
    let c : ℂ := (S (spinKet twoI ⟨0, Nat.succ_pos twoI⟩)) ⟨0, Nat.succ_pos twoI⟩
    S = c • (1 : Module.End ℂ (SpinSpace twoI)) := by
  intro c
  have hdiag : ∀ k : Fin (twoI + 1),
      S (spinKet twoI k) = (S (spinKet twoI k) k) • spinKet twoI k := by
    intro k
    have heig : spinZ twoI (S (spinKet twoI k)) = spinMValue twoI k • S (spinKet twoI k) := by
      have h := congrArg (fun f : Module.End ℂ (SpinSpace twoI) => f (spinKet twoI k)) hcommZ
      simpa [Module.End.mul_apply, spinZ_ket, map_smul] using h
    ext j
    by_cases hjk : j = k
    · subst hjk; simp
    · have hj : spinMValue twoI j * S (spinKet twoI k) j =
          spinMValue twoI k * S (spinKet twoI k) j := by
        simpa [spinZ, LinearMap.coe_mk, AddHom.coe_mk] using congrFun heig j
      have hne : spinMValue twoI j - spinMValue twoI k ≠ 0 :=
        sub_ne_zero.mpr (fun h => hjk (spinMValue_injective twoI h))
      have hprod : (spinMValue twoI j - spinMValue twoI k) * S (spinKet twoI k) j = 0 := by
        linear_combination hj
      have hz := (mul_eq_zero.mp hprod).resolve_left hne
      simp [hz, hjk]
  have hconst : ∀ (k : ℕ) (hk : k < twoI + 1),
      S (spinKet twoI ⟨k, hk⟩) ⟨k, hk⟩ = c := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        have hk_lt : k < twoI := by omega
        have hp := congrArg (fun f : Module.End ℂ (SpinSpace twoI) =>
          f (spinKet twoI ⟨k + 1, hk⟩)) hcommP
        simp only [Module.End.mul_apply] at hp
        rw [hdiag ⟨k + 1, hk⟩, map_smul, spinPlus_ket_succ twoI k hk_lt, map_smul,
          hdiag ⟨k, by omega⟩] at hp
        have hv := congrFun hp ⟨k, by omega⟩
        simp only [Pi.smul_apply, smul_eq_mul, spinKet_apply, ↓reduceIte, mul_one] at hv
        have hne : spinPlusCoeff twoI k ≠ 0 := spinPlusCoeff_ne_zero hk_lt
        have heq : S (spinKet twoI ⟨k + 1, hk⟩) ⟨k + 1, hk⟩ =
            S (spinKet twoI ⟨k, by omega⟩) ⟨k, by omega⟩ :=
          mul_left_cancel₀ hne (by linear_combination hv)
        rw [heq, ih (by omega)]
  apply LinearMap.ext
  intro ψ
  rw [spinSpace_basis_expand ψ, map_sum]
  simp only [map_smul]
  have hsum : (∑ k : Fin (twoI + 1), ψ k • S (spinKet twoI k)) =
      ∑ k : Fin (twoI + 1), ψ k • (c • spinKet twoI k) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hdiag k, hconst k.val k.isLt]
  rw [hsum, LinearMap.smul_apply, Module.End.one_apply]
  calc
    (∑ k : Fin (twoI + 1), ψ k • (c • spinKet twoI k))
        = ∑ k : Fin (twoI + 1), c • (ψ k • spinKet twoI k) :=
          Finset.sum_congr rfl (fun k _ => smul_comm _ _ _)
    _ = c • ∑ k : Fin (twoI + 1), ψ k • spinKet twoI k := Finset.smul_sum.symm

/-- **Wigner--Eckart Rank-1 Selection Rule on `SpinSpace twoI`**:
matrix elements of any rank-1 spherical tensor vanish unless `M_f = M_i + q`. -/
theorem wigner_eckart_rank1_selection (twoI : ℕ)
    (T : SphericalTensorOperator (spinIrrep twoI) 1 (racahPlus 1) (racahMinus 1))
    (q : ℤ) (kf ki : Fin (twoI + 1))
    (hne : spinMValue twoI kf ≠ spinMValue twoI ki + q) :
    (T.comp q (spinKet twoI ki)) kf = 0 := by
  let bra : SpinSpace twoI →ₗ[ℂ] ℂ := LinearMap.proj kf
  have hket : (spinIrrep twoI).J_zero (spinKet twoI ki) =
      spinMValue twoI ki • spinKet twoI ki := spinZ_ket twoI ki
  have hbra : ∀ v : SpinSpace twoI,
      bra ((spinIrrep twoI).J_zero v) = spinMValue twoI kf * bra v := by
    intro v
    simp [bra, spinIrrep, spinZ]
  exact magnetic_selection_rule T q bra (spinKet twoI ki)
    (spinMValue twoI ki) (spinMValue twoI kf) hket hbra hne

/-- **Wigner--Eckart Rank-1 Factorization Theorem on `SpinSpace twoI`** (arbitrary spin `twoI`):
every rank-1 spherical tensor operator `T` on `spinIrrep twoI` is proportional to
`vectorTensorOperator (spinIrrep twoI)` (`(-(1/√2) J_+, J_z, (1/√2) J_-)`). -/
theorem wigner_eckart_rank1_factorization (twoI : ℕ)
    (T : SphericalTensorOperator (spinIrrep twoI) 1 (racahPlus 1) (racahMinus 1)) :
    let c_red : ℂ := if twoI = 0 then 0 else
      (2 / (twoI : ℂ)) * (T.comp 0 (spinKet twoI ⟨0, Nat.succ_pos twoI⟩))
        ⟨0, Nat.succ_pos twoI⟩
    ∀ q : ℤ, T.comp q = c_red • (vectorTensorOperator (spinIrrep twoI)).comp q := by
  intro c_red q
  have hsqrt_re : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_sq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast (by simpa [sq] using hsqrt_re)
  have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hsqrt_sq; norm_num at hsqrt_sq
  have hrp0 : racahPlus 1 0 = (Real.sqrt 2 : ℂ) := by unfold racahPlus; norm_num
  have hrpm1 : racahPlus 1 (-1) = (Real.sqrt 2 : ℂ) := by unfold racahPlus; norm_num
  have hrm0 : racahMinus 1 0 = (Real.sqrt 2 : ℂ) := by unfold racahMinus; norm_num
  have hrm1 : racahMinus 1 1 = (Real.sqrt 2 : ℂ) := by unfold racahMinus; norm_num
  by_cases h0 : twoI = 0
  · subst h0
    have hc_zero : c_red = 0 := by simp [c_red]
    rw [hc_zero, zero_smul]
    have hZ0 : (spinIrrep 0).J_zero = 0 := by
      apply LinearMap.ext; intro ψ; ext k; fin_cases k; simp [spinIrrep, spinZ, spinMValue]
    have hP0 : (spinIrrep 0).J_plus = 0 := by
      apply LinearMap.ext; intro ψ; ext k; fin_cases k; simp [spinIrrep, spinPlus]
    have hM0 : (spinIrrep 0).J_minus = 0 := by
      apply LinearMap.ext; intro ψ; ext k; fin_cases k; simp [spinIrrep, spinMinus]
    have hT1 : T.comp 1 = 0 := by
      have h := T.comm_J_plus 0
      rw [hP0, zero_mul, mul_zero, sub_self, hrp0] at h
      norm_num at h
      exact (smul_eq_zero.mp h.symm).resolve_left hsqrt_ne
    have hTm1 : T.comp (-1) = 0 := by
      have h := T.comm_J_minus 0
      rw [hM0, zero_mul, mul_zero, sub_self, hrm0] at h
      norm_num at h
      exact (smul_eq_zero.mp h.symm).resolve_left hsqrt_ne
    have hT0 : T.comp 0 = 0 := by
      have h := T.comm_J_plus (-1)
      rw [hP0, zero_mul, mul_zero, sub_self, hrpm1, neg_add_cancel] at h
      exact (smul_eq_zero.mp h.symm).resolve_left hsqrt_ne
    by_cases hq1 : q = 1
    · subst hq1; exact hT1
    · by_cases hq0 : q = 0
      · subst hq0; exact hT0
      · by_cases hqm1 : q = -1
        · subst hqm1; exact hTm1
        · apply T.support_zero
          rcases abs_cases q with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · have hpos : 0 < twoI := Nat.pos_of_ne_zero h0
    have htwoI_ne : (twoI : ℂ) ≠ 0 := by exact_mod_cast h0
    have hc_eq : c_red = (2 / (twoI : ℂ)) *
        (T.comp 0 (spinKet twoI ⟨0, Nat.succ_pos twoI⟩)) ⟨0, Nat.succ_pos twoI⟩ := by
      simp [c_red, h0]
    let a : Fin (twoI + 1) → ℂ := fun k => (T.comp 0 (spinKet twoI k)) k
    have hT0_ket : ∀ k : Fin (twoI + 1), T.comp 0 (spinKet twoI k) = a k • spinKet twoI k := by
      intro k
      ext j
      by_cases hjk : j = k
      · subst hjk; simp [a]
      · have hne : spinMValue twoI j ≠ spinMValue twoI k + (0 : ℤ) := by
          intro heq
          apply hjk
          apply spinMValue_injective twoI
          simpa using heq
        have hz := wigner_eckart_rank1_selection twoI T 0 j k hne
        simp [hz, hjk]
    have hT1_top : T.comp 1 (spinKet twoI ⟨0, Nat.succ_pos twoI⟩) = 0 := by
      have h := congrArg (fun op : Module.End ℂ (SpinSpace twoI) =>
        op (spinKet twoI ⟨0, Nat.succ_pos twoI⟩)) (T.comm_J_plus 0)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        hrp0, zero_add] at h
      change spinPlus twoI (T.comp 0 (spinKet twoI ⟨0, Nat.succ_pos twoI⟩)) -
          T.comp 0 (spinPlus twoI (spinKet twoI ⟨0, Nat.succ_pos twoI⟩)) =
        (Real.sqrt 2 : ℂ) • T.comp 1 (spinKet twoI ⟨0, Nat.succ_pos twoI⟩) at h
      rw [hT0_ket, map_smul, spinPlus_ket_zero, map_zero, smul_zero, sub_zero] at h
      exact (smul_eq_zero.mp h.symm).resolve_left hsqrt_ne
    have hT1_succ : ∀ k : ℕ, (hk : k < twoI) →
        T.comp 1 (spinKet twoI ⟨k + 1, by omega⟩) =
          (((a ⟨k + 1, by omega⟩ - a ⟨k, by omega⟩) * spinPlusCoeff twoI k) /
            (Real.sqrt 2 : ℂ)) • spinKet twoI ⟨k, by omega⟩ := by
      intro k hk
      have h := congrArg (fun op : Module.End ℂ (SpinSpace twoI) =>
        op (spinKet twoI ⟨k + 1, by omega⟩)) (T.comm_J_plus 0)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        hrp0, zero_add] at h
      change spinPlus twoI (T.comp 0 (spinKet twoI ⟨k + 1, by omega⟩)) -
          T.comp 0 (spinPlus twoI (spinKet twoI ⟨k + 1, by omega⟩)) =
        (Real.sqrt 2 : ℂ) • T.comp 1 (spinKet twoI ⟨k + 1, by omega⟩) at h
      rw [hT0_ket ⟨k + 1, by omega⟩, map_smul, spinPlus_ket_succ twoI k hk,
        map_smul, hT0_ket ⟨k, by omega⟩] at h
      have hs : (Real.sqrt 2 : ℂ) • T.comp 1 (spinKet twoI ⟨k + 1, by omega⟩) =
          ((a ⟨k + 1, by omega⟩ - a ⟨k, by omega⟩) * spinPlusCoeff twoI k) •
            spinKet twoI ⟨k, by omega⟩ := by
        rw [← h, smul_smul, smul_smul, ← sub_smul]
        congr 1; ring
      have hs2 := congrArg (fun v => (1 / (Real.sqrt 2 : ℂ)) • v) hs
      rw [smul_smul, smul_smul, one_div, inv_mul_cancel₀ hsqrt_ne, one_smul] at hs2
      simpa [div_eq_mul_inv, mul_comm] using hs2
    have hTm1_bot : T.comp (-1) (spinKet twoI ⟨twoI, Nat.lt_succ_self twoI⟩) = 0 := by
      have h := congrArg (fun op : Module.End ℂ (SpinSpace twoI) =>
        op (spinKet twoI ⟨twoI, Nat.lt_succ_self twoI⟩)) (T.comm_J_minus 0)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        hrm0, zero_sub] at h
      change spinMinus twoI (T.comp 0 (spinKet twoI ⟨twoI, Nat.lt_succ_self twoI⟩)) -
          T.comp 0 (spinMinus twoI (spinKet twoI ⟨twoI, Nat.lt_succ_self twoI⟩)) =
        (Real.sqrt 2 : ℂ) • T.comp (-1) (spinKet twoI ⟨twoI, Nat.lt_succ_self twoI⟩) at h
      rw [hT0_ket, map_smul, spinMinus_ket_top, map_zero, smul_zero, sub_zero] at h
      exact (smul_eq_zero.mp h.symm).resolve_left hsqrt_ne
    have hTm1_lt : ∀ k : ℕ, (hk : k < twoI) →
        T.comp (-1) (spinKet twoI ⟨k, by omega⟩) =
          (((a ⟨k, by omega⟩ - a ⟨k + 1, by omega⟩) * spinPlusCoeff twoI k) /
            (Real.sqrt 2 : ℂ)) • spinKet twoI ⟨k + 1, by omega⟩ := by
      intro k hk
      have h := congrArg (fun op : Module.End ℂ (SpinSpace twoI) =>
        op (spinKet twoI ⟨k, by omega⟩)) (T.comm_J_minus 0)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        hrm0, zero_sub] at h
      change spinMinus twoI (T.comp 0 (spinKet twoI ⟨k, by omega⟩)) -
          T.comp 0 (spinMinus twoI (spinKet twoI ⟨k, by omega⟩)) =
        (Real.sqrt 2 : ℂ) • T.comp (-1) (spinKet twoI ⟨k, by omega⟩) at h
      rw [hT0_ket ⟨k, by omega⟩, map_smul, spinMinus_ket_lt twoI k hk,
        map_smul, hT0_ket ⟨k + 1, by omega⟩] at h
      have hs : (Real.sqrt 2 : ℂ) • T.comp (-1) (spinKet twoI ⟨k, by omega⟩) =
          ((a ⟨k, by omega⟩ - a ⟨k + 1, by omega⟩) * spinPlusCoeff twoI k) •
            spinKet twoI ⟨k + 1, by omega⟩ := by
        rw [← h, smul_smul, smul_smul, ← sub_smul]
        congr 1; ring
      have hs2 := congrArg (fun v => (1 / (Real.sqrt 2 : ℂ)) • v) hs
      rw [smul_smul, smul_smul, one_div, inv_mul_cancel₀ hsqrt_ne, one_smul] at hs2
      simpa [div_eq_mul_inv, mul_comm] using hs2
    have ha_formula : ∀ (k : ℕ) (hk : k < twoI + 1),
        a ⟨k, hk⟩ = c_red * spinMValue twoI ⟨k, hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        match k with
        | 0 =>
            intro hk
            simp only [spinMValue, CharP.cast_eq_zero, sub_zero, hc_eq]
            field_simp [htwoI_ne]
            rfl
        | k + 1 =>
            intro hk
            have hk_lt : k < twoI := by omega
            have hk_lt1 : k < twoI + 1 := by omega
            have hcm := congrArg (fun op : Module.End ℂ (SpinSpace twoI) =>
              op (spinKet twoI ⟨k, hk_lt1⟩)) (T.comm_J_minus 1)
            simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
              hrm1, sub_self] at hcm
            change spinMinus twoI (T.comp 1 (spinKet twoI ⟨k, hk_lt1⟩)) -
                T.comp 1 (spinMinus twoI (spinKet twoI ⟨k, hk_lt1⟩)) =
              (Real.sqrt 2 : ℂ) • T.comp 0 (spinKet twoI ⟨k, hk_lt1⟩) at hcm
            rw [spinMinus_ket_lt twoI k hk_lt, map_smul, hT1_succ k hk_lt, hT0_ket ⟨k, hk_lt1⟩] at hcm
            have hcsq : spinPlusCoeff twoI k * spinPlusCoeff twoI k =
                ((k : ℂ) + 1) * ((twoI : ℂ) - k) := spinPlusCoeff_sq (Nat.le_of_lt hk_lt)
            have hne_c : ((k : ℂ) + 1) * ((twoI : ℂ) - k) ≠ 0 := by
              have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
              have h2 : (twoI : ℂ) - k ≠ 0 := by
                intro hd
                have heq : (twoI : ℂ) = k := sub_eq_zero.mp hd
                have heq' : twoI = k := by exact_mod_cast heq
                omega
              exact mul_ne_zero h1 h2
            by_cases hk0 : k = 0
            · subst hk0
              rw [hT1_top, map_zero, zero_sub] at hcm
              have hv := congrFun hcm ⟨0, hk_lt1⟩
              simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, spinKet_apply, ↓reduceIte,
                mul_one] at hv
              have hmul : -((a ⟨1, hk⟩ - a ⟨0, hk_lt1⟩) *
                  (spinPlusCoeff twoI 0 * spinPlusCoeff twoI 0)) =
                  ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * a ⟨0, hk_lt1⟩ := by
                have hdiv := congrArg (fun z => (Real.sqrt 2 : ℂ) * z) hv
                field_simp [hsqrt_ne] at hdiv
                linear_combination hdiv
              rw [hcsq, hsqrt_sq] at hmul
              simp only [CharP.cast_eq_zero, zero_add, sub_zero, one_mul] at hmul
              have ha0 : a ⟨0, hk_lt1⟩ = c_red * ((twoI : ℂ) / 2) := by
                have h0' := ih 0 (by omega) hk_lt1
                simpa [spinMValue] using h0'
              have hdiff : (twoI : ℂ) * (a ⟨1, hk⟩ - a ⟨0, hk_lt1⟩ + c_red) = 0 := by
                rw [ha0] at hmul ⊢
                linear_combination -hmul
              have hlin := (mul_eq_zero.mp hdiff).resolve_left htwoI_ne
              rw [ha0] at hlin
              simp only [spinMValue]
              push_cast
              linear_combination hlin
            · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
              have hk_pred_lt : k - 1 < twoI := by omega
              have hidx_pred : (⟨k - 1 + 1, by omega⟩ : Fin (twoI + 1)) = ⟨k, hk_lt1⟩ := by
                ext; dsimp; omega
              have hT1k := hT1_succ (k - 1) hk_pred_lt
              simp only [hidx_pred] at hT1k
              rw [hT1k, map_smul, spinMinus_ket_lt twoI (k - 1) hk_pred_lt, hidx_pred] at hcm
              have hv := congrFun hcm ⟨k, hk_lt1⟩
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, spinKet_apply, ↓reduceIte,
                mul_one] at hv
              have hcsq_prev : spinPlusCoeff twoI (k - 1) * spinPlusCoeff twoI (k - 1) =
                  (k : ℂ) * ((twoI : ℂ) + 1 - k) := by
                have hsq' := spinPlusCoeff_sq (twoI := twoI) (k := k - 1) (by omega)
                have hsub1 : ((k - 1 : ℕ) : ℂ) + 1 = k := by
                  have : (k - 1 + 1 : ℕ) = k := Nat.sub_add_cancel hk_pos
                  exact_mod_cast this
                have hsub2 : (twoI : ℂ) - ((k - 1 : ℕ) : ℂ) = (twoI : ℂ) + 1 - k := by
                  rw [Nat.cast_sub hk_pos]; push_cast; ring
                rwa [hsub1, hsub2] at hsq'
              have hmul : (a ⟨k, hk_lt1⟩ - a ⟨k - 1, by omega⟩) *
                    (spinPlusCoeff twoI (k - 1) * spinPlusCoeff twoI (k - 1)) -
                  (a ⟨k + 1, hk⟩ - a ⟨k, hk_lt1⟩) *
                    (spinPlusCoeff twoI k * spinPlusCoeff twoI k) =
                  ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * a ⟨k, hk_lt1⟩ := by
                have hdiv := congrArg (fun z => (Real.sqrt 2 : ℂ) * z) hv
                field_simp [hsqrt_ne] at hdiv
                linear_combination hdiv
              rw [hcsq_prev, hcsq, hsqrt_sq] at hmul
              have ihk := ih k (by omega) hk_lt1
              have ihkm1 := ih (k - 1) (by omega) (by omega : k - 1 < twoI + 1)
              simp only [spinMValue] at ihk ihkm1
              have hsub_cast : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by
                rw [Nat.cast_sub hk_pos]; simp
              rw [hsub_cast] at ihkm1
              have hdiff_prev : a ⟨k, hk_lt1⟩ - a ⟨k - 1, by omega⟩ = -c_red := by
                rw [ihk, ihkm1]; ring
              rw [hdiff_prev, ihk] at hmul
              have hfac : (((k : ℂ) + 1) * ((twoI : ℂ) - k)) *
                  (a ⟨k + 1, hk⟩ - a ⟨k, hk_lt1⟩ + c_red) = 0 := by
                rw [ihk]
                linear_combination -hmul
              have hlin := (mul_eq_zero.mp hfac).resolve_left hne_c
              rw [ihk] at hlin
              simp only [spinMValue]
              push_cast
              linear_combination hlin
    have hbasis : ∀ (f g : Module.End ℂ (SpinSpace twoI)),
        (∀ k : Fin (twoI + 1), f (spinKet twoI k) = g (spinKet twoI k)) → f = g := by
      intro f g hfg
      apply LinearMap.ext; intro ψ
      rw [spinSpace_basis_expand ψ, map_sum, map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [map_smul, hfg k]
    by_cases hq1 : q = 1
    · subst hq1
      apply hbasis
      intro k
      rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
      · have hkz : k = ⟨0, Nat.succ_pos twoI⟩ := Fin.ext hk0
        rw [hkz, hT1_top]
        simp only [vectorTensorOperator, vectorTensorOperatorOver, vectorTensorComp, ↓reduceIte,
          LinearMap.smul_apply, LinearMap.neg_apply, spinIrrep, spinPlus_ket_zero, neg_zero,
          smul_zero]
      · have hkp : k.val - 1 < twoI := by omega
        have hks : k = ⟨(k.val - 1) + 1, by omega⟩ := by ext; dsimp; omega
        rw [hks, hT1_succ (k.val - 1) hkp]
        have ha1 := ha_formula (k.val - 1 + 1) (by omega)
        have ha0 := ha_formula (k.val - 1) (by omega)
        have hdiff : a ⟨k.val - 1 + 1, by omega⟩ - a ⟨k.val - 1, by omega⟩ = -c_red := by
          rw [ha1, ha0]
          simp only [spinMValue]
          push_cast
          ring
        rw [hdiff]
        simp only [vectorTensorOperator, vectorTensorOperatorOver, vectorTensorComp, ↓reduceIte,
          LinearMap.smul_apply, LinearMap.neg_apply, spinIrrep, spinPlus_ket_succ twoI (k.val - 1) hkp]
        rw [smul_neg, smul_smul, smul_smul, ← neg_smul]
        congr 1
        ring
    · by_cases hq0 : q = 0
      · subst hq0
        apply hbasis
        intro k
        rw [hT0_ket k, ha_formula k.val k.isLt]
        simp [vectorTensorOperator, vectorTensorOperatorOver, vectorTensorComp, spinIrrep,
          spinZ_ket, smul_smul]
      · by_cases hqm1 : q = -1
        · subst hqm1
          apply hbasis
          intro k
          by_cases hk_top : k.val = twoI
          · have hkt : k = ⟨twoI, Nat.lt_succ_self twoI⟩ := Fin.ext hk_top
            rw [hkt, hTm1_bot]
            simp [vectorTensorOperator, vectorTensorOperatorOver, vectorTensorComp, spinIrrep,
              spinMinus_ket_top]
          · have hkl : k.val < twoI := by omega
            have hke : k = ⟨k.val, by omega⟩ := rfl
            rw [hke, hTm1_lt k.val hkl]
            have ha1 := ha_formula (k.val + 1) (by omega)
            have ha0 := ha_formula k.val (by omega)
            have hdiff : a ⟨k.val, by omega⟩ - a ⟨k.val + 1, by omega⟩ = c_red := by
              rw [ha0, ha1]
              simp only [spinMValue]
              push_cast
              ring
            rw [hdiff]
            simp only [vectorTensorOperator, vectorTensorOperatorOver, vectorTensorComp,
              show (-1 : ℤ) ≠ 1 by decide, show (-1 : ℤ) ≠ 0 by decide, ↓reduceIte,
              LinearMap.smul_apply, spinIrrep, spinMinus_ket_lt twoI k.val hkl]
            rw [smul_smul, smul_smul]
            congr 1
            ring
        · have hgt : (1 : ℤ) < |q| := by
            rcases abs_cases q with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
          rw [T.support_zero q hgt,
            (vectorTensorOperator (spinIrrep twoI)).support_zero q hgt, smul_zero]

/-- Matrix-element form of the Rank-1 Wigner--Eckart theorem on `SpinSpace twoI`. -/
theorem wigner_eckart_rank1_matrix_elements (twoI : ℕ)
    (T : SphericalTensorOperator (spinIrrep twoI) 1 (racahPlus 1) (racahMinus 1)) :
    ∃ c_red : ℂ, ∀ (q : ℤ) (kf ki : Fin (twoI + 1)),
      (spinMValue twoI kf ≠ spinMValue twoI ki + q → (T.comp q (spinKet twoI ki)) kf = 0) ∧
      (T.comp q (spinKet twoI ki)) kf =
        c_red * ((vectorTensorOperator (spinIrrep twoI)).comp q (spinKet twoI ki)) kf := by
  refine ⟨if twoI = 0 then 0 else
      (2 / (twoI : ℂ)) * (T.comp 0 (spinKet twoI ⟨0, Nat.succ_pos twoI⟩))
        ⟨0, Nat.succ_pos twoI⟩, fun q kf ki => ⟨?_, ?_⟩⟩
  · intro hne
    exact wigner_eckart_rank1_selection twoI T q kf ki hne
  · have hf := wigner_eckart_rank1_factorization twoI T q
    have hv := congrFun (congrArg (fun op : Module.End ℂ (SpinSpace twoI) =>
      op (spinKet twoI ki)) hf) kf
    exact hv

-- -----------------------------------------------------------------------------
-- SECTION 5: Coriolis K = 1/2 Decoupling in Nilsson Rotational Bands
-- -----------------------------------------------------------------------------

section NilssonCoriolisBand

open InfoGeometry.Physics.NuclearShellModel

/-- Coriolis decoupling sign factor `(-1)^{I + 1/2} (I + 1/2)` for half-integer `twoI = 2I`. -/
def coriolisDecouplingFactor (twoI : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((twoI + 1) / 2) * ((twoI : ℝ) / 2 + 1 / 2)

/-- Rotational energy including the Bohr--Mottelson `K = 1/2` Coriolis decoupling term
`(-1)^{I + 1/2} a (I + 1/2)` when `twoK = 1`. -/
def coriolisRotationalEnergy (hbar 𝓘 : ℝ) (twoI twoK : ℕ) (a : ℝ) : ℝ :=
  rotational_energy hbar 𝓘 ((twoI : ℝ) / 2) +
    if twoK = 1 then (hbar * hbar) / (2 * 𝓘) * a * coriolisDecouplingFactor twoI else 0

/-- Rotational energy of a deformed Nilsson band built on `s : NilssonAsymptoticState`. -/
def nilssonRotationalEnergy (hbar 𝓘 : ℝ) (twoI : ℕ) (s : NilssonAsymptoticState) : ℝ :=
  coriolisRotationalEnergy hbar 𝓘 twoI s.twoOmega (nilssonDecouplingParameter s)

theorem nilssonRotationalEnergy_eq_pure_rotor_of_Lambda_ne_zero
    (hbar 𝓘 : ℝ) (twoI : ℕ) (s : NilssonAsymptoticState) (hL : s.Lambda ≠ 0) :
    nilssonRotationalEnergy hbar 𝓘 twoI s = rotational_energy hbar 𝓘 ((twoI : ℝ) / 2) := by
  unfold nilssonRotationalEnergy coriolisRotationalEnergy
  rw [nilssonDecouplingParameter_eq_zero_of_Lambda_ne_zero s hL]
  split_ifs <;> ring

theorem nilssonRotationalEnergy_Lambda_zero_K_half
    (hbar 𝓘 : ℝ) (twoI : ℕ) (s : NilssonAsymptoticState)
    (hL : s.Lambda = 0) (hO : s.twoOmega = 1) :
    nilssonRotationalEnergy hbar 𝓘 twoI s =
      rotational_energy hbar 𝓘 ((twoI : ℝ) / 2) +
        (hbar * hbar) / (2 * 𝓘) * ((-1 : ℝ) ^ s.N * ((s.N : ℝ) + 1 / 2)) *
          ((-1 : ℝ) ^ ((twoI + 1) / 2) * ((twoI : ℝ) / 2 + 1 / 2)) := by
  unfold nilssonRotationalEnergy coriolisRotationalEnergy coriolisDecouplingFactor
  rw [nilssonDecouplingParameter_Lambda_zero s hL hO, if_pos hO]

/-- Exact `ΔI = 1` level spacing in a `K = 1/2` band (`twoI = 2*k + 1 → 2*(k + 1) + 1`):
`E(I+1) - E(I) = (ħ² / 𝓘) (k + 3/2) (1 + (-1)^(k+2) a)`, proving signature alternation
and level inversion when `(-1)^(k+2) a < -1`. -/
theorem coriolisRotationalEnergy_K_half_spacing (hbar 𝓘 a : ℝ) (hI : 𝓘 ≠ 0) (k : ℕ) :
    coriolisRotationalEnergy hbar 𝓘 (2 * (k + 1) + 1) 1 a -
      coriolisRotationalEnergy hbar 𝓘 (2 * k + 1) 1 a =
        (hbar * hbar) / 𝓘 * ((k : ℝ) + 3 / 2) * (1 + (-1 : ℝ) ^ (k + 2) * a) := by
  unfold coriolisRotationalEnergy coriolisDecouplingFactor rotational_energy
  have h1 : (2 * (k + 1) + 1 + 1) / 2 = k + 2 := by omega
  have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [↓reduceIte, h1, h2]
  have hpow : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ (k + 2)) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  push_cast
  field_simp [hI]
  ring

end NilssonCoriolisBand

end SU2SpinRepresentations

/-! ## Section 6: K^π Rotational Bandheads, Selection Rules & Taxonomy Bridge -/

section KPiBandsAndSelection

open InfoGeometry.Physics.NuclearSymmetrySectors
open InfoGeometry.Physics.NuclearAngularMomentum

/-- Rotational bandhead quantum numbers `(2K, π)`. -/
structure RotationalBandhead where
  twoK : ℕ
  parity : SpatialParity
  deriving DecidableEq, Repr

/-- Ground-state even-even rotational bandhead `K^π = 0^+`. -/
def groundBandhead : RotationalBandhead where
  twoK := 0
  parity := .positive

/-- Band-membership compatibility for a sector `(2J, π)` inside a bandhead `b`:
`K ≤ J`, matching integer/half-integer parity (`twoJ ≡ twoK mod 2`), and matching parity. -/
def bandMemberCompatible (b : RotationalBandhead) (s : SpinParitySector) :
    Prop :=
  b.twoK ≤ s.twoJ ∧ (s.twoJ + b.twoK) % 2 = 0 ∧ s.parity = b.parity

/-- Generalized axial rotational energy `E(I, K) = ħ² (I(I+1) - K²) / (2 𝓘)`
over any characteristic-zero field `𝒦`. -/
def rotational_energy_K (hbar 𝓘 I K : 𝒦) : 𝒦 :=
  (hbar * hbar : 𝒦) * (I * (I + 1 : 𝒦) - K * K) / (2 * 𝓘 : 𝒦)

theorem rotational_energy_K_zero (hbar 𝓘 I : 𝒦) :
    rotational_energy_K hbar 𝓘 I 0 = rotational_energy hbar 𝓘 I := by
  unfold rotational_energy_K rotational_energy
  ring

theorem rotational_energy_K_even_in_K (hbar 𝓘 I K : 𝒦) :
    rotational_energy_K hbar 𝓘 I (-K) = rotational_energy_K hbar 𝓘 I K := by
  unfold rotational_energy_K
  ring

theorem rotational_energy_K_spacing (hbar 𝓘 I K : 𝒦) (hI : 𝓘 ≠ 0) :
    rotational_energy_K hbar 𝓘 (I + 1) K - rotational_energy_K hbar 𝓘 I K =
      (hbar * hbar : 𝒦) * (I + 1 : 𝒦) / 𝓘 := by
  unfold rotational_energy_K
  field_simp [hI]
  ring

/-- Rotational energy evaluated on a concrete `SpinParitySector`. -/
def sector_rotational_energy (hbar 𝓘 : ℝ) (s : SpinParitySector) : ℝ :=
  rotational_energy hbar 𝓘 ((s.twoJ : ℝ) / 2)

theorem sector_rotational_energy_nonneg (hbar 𝓘 : ℝ) (hI : 0 ≤ 𝓘) (s : SpinParitySector) :
    0 ≤ sector_rotational_energy hbar 𝓘 s := by
  unfold sector_rotational_energy rotational_energy
  have hsq : 0 ≤ hbar * hbar := mul_self_nonneg hbar
  have hj : 0 ≤ (s.twoJ : ℝ) / 2 := by positivity
  have hj1 : 0 ≤ (s.twoJ : ℝ) / 2 + 1 := by positivity
  have hnum : 0 ≤ hbar * hbar * ((s.twoJ : ℝ) / 2) * ((s.twoJ : ℝ) / 2 + 1) := by positivity
  have hden : 0 ≤ 2 * 𝓘 := mul_nonneg (by norm_num) hI
  exact div_nonneg hnum hden

/-- Allowed sequence of a `K^π = 0^+` band: `I^π = 0^+, 2^+, 4^+, ...` (`twoJ ≡ 0 mod 4`). -/
def k0PositiveBandAllowed (s : SpinParitySector) :
    Prop :=
  s.parity = .positive ∧ s.twoJ % 4 = 0

/-- Signature-staggered `K = 0` band with parity `(-1)^I = π`:
`I` even for `π = +1` (`twoJ ≡ 0 mod 4`) and `I` odd for `π = -1` (`twoJ ≡ 2 mod 4`). -/
def k0AlternatingBandAllowed (b : RotationalBandhead) (s : SpinParitySector) :
    Prop :=
  b.twoK = 0 ∧ s.twoJ % 2 = 0 ∧ s.parity = b.parity ∧
    ((b.parity = .positive ∧ s.twoJ % 4 = 0) ∨
     (b.parity = .negative ∧ s.twoJ % 4 = 2))

theorem k0PositiveBand_forbids_odd (s : SpinParitySector) (hk : k0PositiveBandAllowed s)
    (hodd : s.twoJ % 4 = 2) : False := by
  unfold k0PositiveBandAllowed at hk
  have h0 : s.twoJ % 4 = 0 := hk.2
  have h2 : s.twoJ % 4 = 2 := hodd
  omega

theorem k0AlternatingBand_iff_parity_sign (b : RotationalBandhead) (hb : b.twoK = 0)
    (s : SpinParitySector) (heven : s.twoJ % 2 = 0) (hp : s.parity = b.parity) :
    (k0AlternatingBandAllowed b s ↔
      ((b.parity = .positive ∧ s.twoJ % 4 = 0) ∨
       (b.parity = .negative ∧ s.twoJ % 4 = 2))) := by
  unfold k0AlternatingBandAllowed
  constructor
  · intro ⟨_, _, _, hst⟩
    exact hst
  · intro hst
    exact ⟨hb, heven, hp, hst⟩

/-- Stretched electric quadrupole (`E2`) intraband cascade `I + 2 → I` in a `K^π = 0^+` band
satisfies `MultipoleAllowed .electric 2`. -/
theorem k0Positive_e2_multipole_allowed (k : ℕ) :
    MultipoleAllowed .electric 2 ⟨4 * (k + 1), .positive⟩ ⟨4 * k, .positive⟩ := by
  unfold MultipoleAllowed SpinTriangle
  dsimp only
  refine ⟨by norm_num, ⟨by omega, by omega, by omega, by omega⟩, ?_⟩
  simp [multipoleCharacter, SpatialParity.sign]

/-- Ladder noncommutativity obstruction `[J_z, J_±] = ±J_±` drives Coriolis `ΔK = ±1` shifts
on any `K`-module `V` carrying an `SU2Rep K V`. -/
theorem rotational_coriolis_ladder_shift
    {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (rep : SU2Rep K V) (ket : V) (m : K) (hket : rep.J_zero ket = m • ket) :
    rep.J_zero (rep.J_plus ket) = (m + 1) • rep.J_plus ket ∧
    rep.J_zero (rep.J_minus ket) = (m - 1) • rep.J_minus ket := by
  have hp := ladder_shifts_weight rep ket m hket
  exact hp

/-- Generalized `K`-forbiddenness from spherical tensor rank `k`: if `T` is a rank-`k`
spherical tensor in an `SU2Rep` over a characteristic-zero field, then any transition changing
`K` by more than `k` vanishes identically. -/
theorem rotational_k_forbidden_vanishes
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {rep : SU2Rep K V} {k : ℕ} {cPlus cMinus : ℤ → K}
    (T : SphericalTensorOperator rep k cPlus cMinus)
    (bra : V →ₗ[K] K) (ket : V) (Ki Kf q : ℤ)
    (hket : rep.J_zero ket = (Ki : K) • ket)
    (hbra : ∀ v, bra (rep.J_zero v) = (Kf : K) * bra v)
    (hforb : (k : ℤ) < |Kf - Ki|) :
    bra (T.comp q ket) = 0 := by
  have hket2 : rep.J_zero ket = (((2 * Ki : ℤ) : K) / 2) • ket := by
    rw [show (((2 * Ki : ℤ) : K) / 2) = (Ki : K) by push_cast; ring]
    exact hket
  have hbra2 : ∀ v, bra (rep.J_zero v) = (((2 * Kf : ℤ) : K) / 2) * bra v := by
    intro v
    rw [show (((2 * Kf : ℤ) : K) / 2) = (Kf : K) by push_cast; ring]
    exact hbra v
  have hforb2 : 2 * (k : ℤ) < |2 * Kf - 2 * Ki| := by
    rw [show 2 * Kf - 2 * Ki = 2 * (Kf - Ki) by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
    linarith [hforb]
  exact k_forbidden_transition_vanishes T bra ket (2 * Ki) (2 * Kf) hket2 hbra2 hforb2 q

/-- Embed a rotational bandhead `(2K, π)` and base `QuantumNumbers` into `NuclearTaxonomyPacket`. -/
def RotationalBandhead.toTaxonomyPacket (b : RotationalBandhead) (q : QuantumNumbers)
    (twoOmega : ℕ) : NuclearTaxonomyPacket where
  base := q
  twoK := b.twoK
  twoOmega := twoOmega
  spatialParitySign := match b.parity with | .positive => 1 | .negative => -1
  spatial_parity_sq := by cases b.parity <;> norm_num
  wmSector := .wmEven
  chitureSector := .chiEven
  spinPairing := .spinSinglet
  isospinPairing := .isoTriplet

/-- Exact bridge: `k0AlternatingBandAllowed` matches `kZeroStaggeringAllowed` on the
associated `NuclearTaxonomyPacket`. -/
theorem k0Alternating_iff_packet_staggering (b : RotationalBandhead) (hb : b.twoK = 0)
    (s : SpinParitySector) (q : QuantumNumbers) (twoOmega : ℕ)
    (hp : s.parity = b.parity) :
    (k0AlternatingBandAllowed b s ↔
      NuclearTaxonomyPacket.kZeroStaggeringAllowed s.twoJ
        (b.toTaxonomyPacket q twoOmega).spatialParitySign) := by
  unfold k0AlternatingBandAllowed NuclearTaxonomyPacket.kZeroStaggeringAllowed
    RotationalBandhead.toTaxonomyPacket
  dsimp only
  cases hpar : b.parity <;> simp [hb, hp, hpar]

/-- Embed a rotational bandhead `(2K, π)` into the `K^π` label carrier. -/
def RotationalBandhead.toKParitySector (b : RotationalBandhead) :
    InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.KParitySector :=
  ⟨b.twoK, b.parity⟩

/-- All members of one axial band share the same `K^π` label. This is derived
from `bandMemberCompatible`; the band Hamiltonian itself is not constructed. -/
theorem bandMembers_share_KParity
    (b : RotationalBandhead) (s f : InfoGeometry.Physics.NuclearSymmetrySectors.SpinParitySector)
    (hs : bandMemberCompatible b s)
    (hf : bandMemberCompatible b f) :
    (⟨b.twoK, s.parity⟩ :
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.KParitySector) =
      ⟨b.twoK, f.parity⟩ := by
  have hs_par : s.parity = b.parity := hs.2.2
  have hf_par : f.parity = b.parity := hf.2.2
  rw [hs_par, hf_par]

/-- A band member satisfies the axial bound `K ≤ J` and the integer/half-integer
matching `twoJ ≡ twoK (mod 2)`. -/
theorem bandMemberCompatible_K_bound_and_parity
    (b : RotationalBandhead) (s : InfoGeometry.Physics.NuclearSymmetrySectors.SpinParitySector)
    (hs : bandMemberCompatible b s) :
    b.twoK ≤ s.twoJ ∧ (s.twoJ + b.twoK) % 2 = 0 := by
  have hk : b.twoK ≤ s.twoJ := hs.1
  have hmod : (s.twoJ + b.twoK) % 2 = 0 := hs.2.1
  exact ⟨hk, hmod⟩

end KPiBandsAndSelection

end InfoGeometry.Physics.NuclearRotationalBand
