/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.Physics.CPTAtom
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Chiral Tensor Recoupling — Wigner-Jones / Temperley-Lieb Bridge

TL generator on `M₂(ℂ) ⊗ M₂(ℂ)` in the chiral basis:

```
e = σ⁺ ⊗ σ⁻ + σ⁻ ⊗ σ⁺ + ½(I ⊗ I - σ₃ ⊗ σ₃)
```

Main theorem: **TL idempotency** `e² = 2·e` (loop parameter `d = 2`).

Tactical note: `module` handles scalar-linear tensor equalities; `noncomm_ring`
expands non-commutative products; `TensorProduct.smul_tmul_smul` cleans the
projector calculation.
-/

noncomputable section

namespace ChiralTensorRecoupling

open Matrix
open TensorProduct
open InfoGeometry.Physics.ChiralCausalCone

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1000000

abbrev SpinPair := M2C ⊗[ℂ] M2C

/-! ## Projector matrix identities -/

theorem PPlus_half_I_add_σ3c : PPlus = (1/2 : ℂ) • ((1 : M2C) + σ3c) := by
  rw [PPlus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, Matrix.smul_apply, Matrix.add_apply]; norm_num

theorem PMinus_half_I_sub_σ3c : PMinus = (1/2 : ℂ) • ((1 : M2C) - σ3c) := by
  rw [PMinus_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σ3c, Matrix.smul_apply, Matrix.sub_apply]; norm_num

/-! ## TL generator -/

/-- The two chiral exchange terms in the TL generator. -/
def X : SpinPair := σPlus ⊗ₜ[ℂ] σMinus
def Y : SpinPair := σMinus ⊗ₜ[ℂ] σPlus
def Z : SpinPair := (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)

/-- The Temperley-Lieb generator on two sites: `e = X + Y + Z`. -/
def e : SpinPair := X + Y + Z

/-- The TL generator as the singlet projector in the chiral basis. -/
theorem e_eq_X_add_Y_add_Z : e = X + Y + Z := rfl

/-! ## Chiral eigenvector relations

The chiral exchange terms `X` and `Y` are left- and right-eigenvectors
of the Cartan diagonal `Z`, and their products solder onto `Z`. -/

theorem X_mul_X : X * X = 0 := by
  unfold X
  rw [Algebra.TensorProduct.tmul_mul_tmul σPlus σPlus σMinus σMinus, σPlus_sq, σMinus_sq]; simp

theorem Y_mul_Y : Y * Y = 0 := by
  unfold Y
  rw [Algebra.TensorProduct.tmul_mul_tmul σMinus σMinus σPlus σPlus, σMinus_sq, σPlus_sq]; simp

theorem Z_mul_Z : Z * Z = Z := by
  unfold Z
  let A := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c
  have hA_sq : A * A = (2 : ℂ) • A := by
    unfold A
    rw [mul_sub, sub_mul, sub_mul]
    have h1 : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
    have h2 : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (σ3c ⊗ₜ[ℂ] σ3c) = σ3c ⊗ₜ[ℂ] σ3c := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
    have h3 : (σ3c ⊗ₜ[ℂ] σ3c) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) = σ3c ⊗ₜ[ℂ] σ3c := by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
    have h4 : (σ3c ⊗ₜ[ℂ] σ3c) * (σ3c ⊗ₜ[ℂ] σ3c) = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) :=
      calc
        (σ3c ⊗ₜ[ℂ] σ3c) * (σ3c ⊗ₜ[ℂ] σ3c) = (σ3c * σ3c) ⊗ₜ[ℂ] (σ3c * σ3c) :=
          Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
        _ = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) := by rw [σ3c_sq]
    rw [h1, h2, h3, h4]; abel; simp [two_smul]
  have hsmul : ((1/2 : ℂ) • A) * ((1/2 : ℂ) • A) = ((1/2 : ℂ) * (1/2 : ℂ)) • (A * A) := by
    calc
      ((1/2 : ℂ) • A) * ((1/2 : ℂ) • A) = (1/2 : ℂ) • (A * ((1/2 : ℂ) • A)) :=
        Algebra.smul_mul_assoc _ _ _
      _ = (1/2 : ℂ) • ((1/2 : ℂ) • (A * A)) := by
        rw [Algebra.mul_smul_comm (1/2 : ℂ) A A]
      _ = ((1/2 : ℂ) * (1/2 : ℂ)) • (A * A) := by rw [smul_smul]
  rw [hsmul, hA_sq]
  dsimp [A]; simp [smul_smul]

theorem X_mul_Z : X * Z = X := by
  unfold X Z
  calc
    (σPlus ⊗ₜ[ℂ] σMinus) * ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c))
      = (1/2 : ℂ) • ((σPlus ⊗ₜ[ℂ] σMinus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) :=
      Algebra.mul_smul_comm _ _ _
    _ = (1/2 : ℂ) • ((σPlus ⊗ₜ[ℂ] σMinus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) -
        (σPlus ⊗ₜ[ℂ] σMinus) * (σ3c ⊗ₜ[ℂ] σ3c)) := by rw [mul_sub]
    _ = (1/2 : ℂ) • ((σPlus * (1 : M2C)) ⊗ₜ[ℂ] (σMinus * (1 : M2C)) -
        (σPlus * σ3c) ⊗ₜ[ℂ] (σMinus * σ3c)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - (-σPlus) ⊗ₜ[ℂ] σMinus) := by
      simp [σPlus_mul_σ3c, σMinus_mul_σ3c]
    _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - (-(σPlus ⊗ₜ[ℂ] σMinus))) := by
      simp [TensorProduct.neg_tmul]
    _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus + σPlus ⊗ₜ[ℂ] σMinus) := by simp
    _ = (1/2 : ℂ) • ((2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus)) := by simp [two_smul]
    _ = σPlus ⊗ₜ[ℂ] σMinus := by simp [smul_smul]

theorem Z_mul_X : Z * X = X := by
  unfold Z X
  calc
    ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) * (σPlus ⊗ₜ[ℂ] σMinus)
      = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) * (σPlus ⊗ₜ[ℂ] σMinus)) :=
      Algebra.smul_mul_assoc _ _ _
    _ = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (σPlus ⊗ₜ[ℂ] σMinus) -
        (σ3c ⊗ₜ[ℂ] σ3c) * (σPlus ⊗ₜ[ℂ] σMinus)) := by rw [sub_mul]
    _ = (1/2 : ℂ) • (((1 : M2C) * σPlus) ⊗ₜ[ℂ] ((1 : M2C) * σMinus) -
        (σ3c * σPlus) ⊗ₜ[ℂ] (σ3c * σMinus)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - σPlus ⊗ₜ[ℂ] (-σMinus)) := by
      simp [σ3c_mul_σPlus, σ3c_mul_σMinus]
    _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - (-(σPlus ⊗ₜ[ℂ] σMinus))) := by
      simp [TensorProduct.tmul_neg]
    _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus + σPlus ⊗ₜ[ℂ] σMinus) := by simp
    _ = (1/2 : ℂ) • ((2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus)) := by simp [two_smul]
    _ = σPlus ⊗ₜ[ℂ] σMinus := by simp [smul_smul]

theorem Y_mul_Z : Y * Z = Y := by
  unfold Y Z
  calc
    (σMinus ⊗ₜ[ℂ] σPlus) * ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c))
      = (1/2 : ℂ) • ((σMinus ⊗ₜ[ℂ] σPlus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) :=
      Algebra.mul_smul_comm _ _ _
    _ = (1/2 : ℂ) • ((σMinus ⊗ₜ[ℂ] σPlus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) -
        (σMinus ⊗ₜ[ℂ] σPlus) * (σ3c ⊗ₜ[ℂ] σ3c)) := by rw [mul_sub]
    _ = (1/2 : ℂ) • ((σMinus * (1 : M2C)) ⊗ₜ[ℂ] (σPlus * (1 : M2C)) -
        (σMinus * σ3c) ⊗ₜ[ℂ] (σPlus * σ3c)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - σMinus ⊗ₜ[ℂ] (-σPlus)) := by
      simp [σMinus_mul_σ3c, σPlus_mul_σ3c]
    _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - (-(σMinus ⊗ₜ[ℂ] σPlus))) := by
      simp [TensorProduct.tmul_neg]
    _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus + σMinus ⊗ₜ[ℂ] σPlus) := by simp
    _ = (1/2 : ℂ) • ((2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus)) := by simp [two_smul]
    _ = σMinus ⊗ₜ[ℂ] σPlus := by simp [smul_smul]

theorem Z_mul_Y : Z * Y = Y := by
  unfold Z Y
  calc
    ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) * (σMinus ⊗ₜ[ℂ] σPlus)
      = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) * (σMinus ⊗ₜ[ℂ] σPlus)) :=
      Algebra.smul_mul_assoc _ _ _
    _ = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (σMinus ⊗ₜ[ℂ] σPlus) -
        (σ3c ⊗ₜ[ℂ] σ3c) * (σMinus ⊗ₜ[ℂ] σPlus)) := by rw [sub_mul]
    _ = (1/2 : ℂ) • (((1 : M2C) * σMinus) ⊗ₜ[ℂ] ((1 : M2C) * σPlus) -
        (σ3c * σMinus) ⊗ₜ[ℂ] (σ3c * σPlus)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - (-σMinus) ⊗ₜ[ℂ] σPlus) := by
      simp [σ3c_mul_σMinus, σ3c_mul_σPlus]
    _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - (-(σMinus ⊗ₜ[ℂ] σPlus))) := by
      simp [TensorProduct.neg_tmul]
    _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus + σMinus ⊗ₜ[ℂ] σPlus) := by simp
    _ = (1/2 : ℂ) • ((2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus)) := by simp [two_smul]
    _ = σMinus ⊗ₜ[ℂ] σPlus := by simp [smul_smul]

/-- Projector soldering: the chiral exchange anticommutator equals the Cartan diagonal.
This is the algebraic core of the TL relation `e² = 2e`. -/
theorem XY_add_YX : X * Y + Y * X = Z := by
  unfold X Y Z
  simp [Algebra.TensorProduct.tmul_mul_tmul]
  -- Now: (σ⁺σ⁻)⊗(σ⁻σ⁺) + (σ⁻σ⁺)⊗(σ⁺σ⁻) = ½(I⊗I - σ₃⊗σ₃)
  -- This is exactly projector_tensor_identity (defined below with its core lemma)
  -- We inline the core computation:
  have h_core : (((1/2 : ℂ) • ((1 : M2C) + σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) - σ3c))) +
      (((1/2 : ℂ) • ((1 : M2C) - σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) + σ3c))) =
      (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) := by
    have h1 : (((1/2 : ℂ) • ((1 : M2C) + σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) - σ3c))) +
        (((1/2 : ℂ) • ((1 : M2C) - σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) + σ3c))) =
        (1/4 : ℂ) • (((1 : M2C) + σ3c) ⊗ₜ[ℂ] ((1 : M2C) - σ3c) +
          ((1 : M2C) - σ3c) ⊗ₜ[ℂ] ((1 : M2C) + σ3c)) := by
      rw [TensorProduct.smul_tmul_smul (1/2) (1/2) _ _,
        TensorProduct.smul_tmul_smul (1/2) (1/2) _ _, ← smul_add]; norm_num
    have h2 : ((1 : M2C) + σ3c) ⊗ₜ[ℂ] ((1 : M2C) - σ3c) +
        ((1 : M2C) - σ3c) ⊗ₜ[ℂ] ((1 : M2C) + σ3c) =
        (2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) := by
      simp [add_tmul, tmul_add, sub_tmul, tmul_sub, two_smul]; abel
    rw [h1, h2]; module
  -- Goal: (σ⁺σ⁻)⊗(σ⁻σ⁺) + (σ⁻σ⁺)⊗(σ⁺σ⁻) = ½(I⊗I - σ₃⊗σ₃)
  -- PPlus = σ⁺σ⁻, PMinus = σ⁻σ⁺, and PPlus_half_I_add_σ3c, PMinus_half_I_sub_σ3c
  -- rewrite the goal into the exact statement of h_core
  have hgoal : (σPlus * σMinus) ⊗ₜ[ℂ] (σMinus * σPlus) + (σMinus * σPlus) ⊗ₜ[ℂ] (σPlus * σMinus) =
      (PPlus ⊗ₜ[ℂ] PMinus) + (PMinus ⊗ₜ[ℂ] PPlus) := by
    simp [PPlus, PMinus]
  rw [hgoal]
  rw [PPlus_half_I_add_σ3c, PMinus_half_I_sub_σ3c]
  -- h_core has (1/2)•... while goal has 2⁻¹•..., norm_num bridges this
  simpa using h_core

/-! ## Projector tensor pairing = Cartan diagonal -/

private lemma projector_tensor_identity_core :
    (((1/2 : ℂ) • ((1 : M2C) + σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) - σ3c))) +
    (((1/2 : ℂ) • ((1 : M2C) - σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) + σ3c))) =
    (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) := by
  have h1 :
      (((1/2 : ℂ) • ((1 : M2C) + σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) - σ3c))) +
      (((1/2 : ℂ) • ((1 : M2C) - σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) + σ3c))) =
      (1/4 : ℂ) •
        (((1 : M2C) + σ3c) ⊗ₜ[ℂ] ((1 : M2C) - σ3c) +
          ((1 : M2C) - σ3c) ⊗ₜ[ℂ] ((1 : M2C) + σ3c)) := by
    rw [TensorProduct.smul_tmul_smul (1/2) (1/2) _ _,
      TensorProduct.smul_tmul_smul (1/2) (1/2) _ _, ← smul_add]; norm_num
  have h2 :
      ((1 : M2C) + σ3c) ⊗ₜ[ℂ] ((1 : M2C) - σ3c) +
      ((1 : M2C) - σ3c) ⊗ₜ[ℂ] ((1 : M2C) + σ3c) =
      (2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) := by
    simp [add_tmul, tmul_add, sub_tmul, tmul_sub, two_smul]; abel
  calc
    (((1/2 : ℂ) • ((1 : M2C) + σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) - σ3c))) +
      (((1/2 : ℂ) • ((1 : M2C) - σ3c)) ⊗ₜ[ℂ] ((1/2 : ℂ) • ((1 : M2C) + σ3c)))
        = (1/4 : ℂ) •
            (((1 : M2C) + σ3c) ⊗ₜ[ℂ] ((1 : M2C) - σ3c) +
              ((1 : M2C) - σ3c) ⊗ₜ[ℂ] ((1 : M2C) + σ3c)) := h1
    _ = (1/4 : ℂ) •
          ((2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) := by rw [h2]
    _ = (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) := by module

theorem projector_tensor_identity :
    (PPlus ⊗ₜ[ℂ] PMinus) + (PMinus ⊗ₜ[ℂ] PPlus) =
      (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) := by
  simpa [PPlus_half_I_add_σ3c, PMinus_half_I_sub_σ3c] using projector_tensor_identity_core

/-! ## TL idempotency: `e² = 2·e` -/

theorem e_sq : e * e = (2 : ℂ) • e := by
  let X : SpinPair := σPlus ⊗ₜ[ℂ] σMinus
  let Y : SpinPair := σMinus ⊗ₜ[ℂ] σPlus
  let Z : SpinPair := (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)
  have he : e = X + Y + Z := rfl
  rw [he]
  -- Nilpotency: (a⊗b)*(c⊗d) = (a*c)⊗(b*d), then a²=0, b²=0 → 0
  have hXX : X * X = 0 := by
    unfold X
    rw [Algebra.TensorProduct.tmul_mul_tmul σPlus σPlus σMinus σMinus, σPlus_sq, σMinus_sq]; simp
  have hYY : Y * Y = 0 := by
    unfold Y
    rw [Algebra.TensorProduct.tmul_mul_tmul σMinus σMinus σPlus σPlus, σMinus_sq, σPlus_sq]; simp
  -- Cartan idempotent: Z = ½•A where A = I⊗I - σ₃⊗σ₃, and A² = 2•A
  have hZZ : Z * Z = Z := by
    unfold Z
    let A := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c
    have hA_sq : A * A = (2 : ℂ) • A := by
      unfold A
      rw [mul_sub, sub_mul, sub_mul]
      -- Four terms: (I⊗I)*(I⊗I), -(I⊗I)*(σ₃⊗σ₃), -(σ₃⊗σ₃)*(I⊗I), +(σ₃⊗σ₃)*(σ₃⊗σ₃)
      have h1 : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
      have h2 : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (σ3c ⊗ₜ[ℂ] σ3c) = σ3c ⊗ₜ[ℂ] σ3c := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
      have h3 : (σ3c ⊗ₜ[ℂ] σ3c) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) = σ3c ⊗ₜ[ℂ] σ3c := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
      have h4 : (σ3c ⊗ₜ[ℂ] σ3c) * (σ3c ⊗ₜ[ℂ] σ3c) = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) :=
        calc
          (σ3c ⊗ₜ[ℂ] σ3c) * (σ3c ⊗ₜ[ℂ] σ3c) = (σ3c * σ3c) ⊗ₜ[ℂ] (σ3c * σ3c) :=
            Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
          _ = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) := by rw [σ3c_sq]
      rw [h1, h2, h3, h4]
      -- Now: I⊗I - σ₃⊗σ₃ - σ₃⊗σ₃ + I⊗I = 2•(I⊗I - σ₃⊗σ₃)
      abel; simp [two_smul]
    have hsmul : ((1/2 : ℂ) • A) * ((1/2 : ℂ) • A) = ((1/2 : ℂ) * (1/2 : ℂ)) • (A * A) := by
      calc
        ((1/2 : ℂ) • A) * ((1/2 : ℂ) • A) = (1/2 : ℂ) • (A * ((1/2 : ℂ) • A)) :=
          Algebra.smul_mul_assoc _ _ _
        _ = (1/2 : ℂ) • ((1/2 : ℂ) • (A * A)) := by
          rw [Algebra.mul_smul_comm (1/2 : ℂ) A A]
        _ = ((1/2 : ℂ) * (1/2 : ℂ)) • (A * A) := by rw [smul_smul]
    rw [hsmul, hA_sq]
    dsimp [A]; simp [smul_smul]
  -- Chiral eigenvectors (calc style — avoids ring on tensor expressions)
  have hXZ : X * Z = X := by
    unfold X Z
    calc
      (σPlus ⊗ₜ[ℂ] σMinus) * ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c))
        = (1/2 : ℂ) • ((σPlus ⊗ₜ[ℂ] σMinus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) :=
        Algebra.mul_smul_comm _ _ _
      _ = (1/2 : ℂ) • ((σPlus ⊗ₜ[ℂ] σMinus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) -
          (σPlus ⊗ₜ[ℂ] σMinus) * (σ3c ⊗ₜ[ℂ] σ3c)) := by rw [mul_sub]
      _ = (1/2 : ℂ) • ((σPlus * (1 : M2C)) ⊗ₜ[ℂ] (σMinus * (1 : M2C)) -
          (σPlus * σ3c) ⊗ₜ[ℂ] (σMinus * σ3c)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - (-σPlus) ⊗ₜ[ℂ] σMinus) := by
        simp [σPlus_mul_σ3c, σMinus_mul_σ3c]
      _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - (-(σPlus ⊗ₜ[ℂ] σMinus))) := by
        simp [TensorProduct.neg_tmul]
      _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus + σPlus ⊗ₜ[ℂ] σMinus) := by simp
      _ = (1/2 : ℂ) • ((2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus)) := by simp [two_smul]
      _ = σPlus ⊗ₜ[ℂ] σMinus := by simp [smul_smul]
  have hZX : Z * X = X := by
    unfold Z X
    calc
      ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) * (σPlus ⊗ₜ[ℂ] σMinus)
        = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) * (σPlus ⊗ₜ[ℂ] σMinus)) := by
        exact Algebra.smul_mul_assoc _ _ _
      _ = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (σPlus ⊗ₜ[ℂ] σMinus) -
          (σ3c ⊗ₜ[ℂ] σ3c) * (σPlus ⊗ₜ[ℂ] σMinus)) := by rw [sub_mul]
      _ = (1/2 : ℂ) • (((1 : M2C) * σPlus) ⊗ₜ[ℂ] ((1 : M2C) * σMinus) -
          (σ3c * σPlus) ⊗ₜ[ℂ] (σ3c * σMinus)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul]
      _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - σPlus ⊗ₜ[ℂ] (-σMinus)) := by
        simp [σ3c_mul_σPlus, σ3c_mul_σMinus]
      _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus - (-(σPlus ⊗ₜ[ℂ] σMinus))) := by
        simp [TensorProduct.tmul_neg]
      _ = (1/2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus + σPlus ⊗ₜ[ℂ] σMinus) := by simp
      _ = (1/2 : ℂ) • ((2 : ℂ) • (σPlus ⊗ₜ[ℂ] σMinus)) := by simp [two_smul]
      _ = σPlus ⊗ₜ[ℂ] σMinus := by simp [smul_smul]
  have hYZ : Y * Z = Y := by
    unfold Y Z
    calc
      (σMinus ⊗ₜ[ℂ] σPlus) * ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c))
        = (1/2 : ℂ) • ((σMinus ⊗ₜ[ℂ] σPlus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) := by exact Algebra.mul_smul_comm _ _ _
      _ = (1/2 : ℂ) • ((σMinus ⊗ₜ[ℂ] σPlus) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) -
          (σMinus ⊗ₜ[ℂ] σPlus) * (σ3c ⊗ₜ[ℂ] σ3c)) := by rw [mul_sub]
      _ = (1/2 : ℂ) • ((σMinus * (1 : M2C)) ⊗ₜ[ℂ] (σPlus * (1 : M2C)) -
          (σMinus * σ3c) ⊗ₜ[ℂ] (σPlus * σ3c)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - σMinus ⊗ₜ[ℂ] (-σPlus)) := by
        simp [σMinus_mul_σ3c, σPlus_mul_σ3c]
      _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - (-(σMinus ⊗ₜ[ℂ] σPlus))) := by
        simp [TensorProduct.tmul_neg]
      _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus + σMinus ⊗ₜ[ℂ] σPlus) := by simp
      _ = (1/2 : ℂ) • ((2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus)) := by simp [two_smul]
      _ = σMinus ⊗ₜ[ℂ] σPlus := by simp [smul_smul]
  have hZY : Z * Y = Y := by
    unfold Z Y
    calc
      ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) * (σMinus ⊗ₜ[ℂ] σPlus)
        = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) * (σMinus ⊗ₜ[ℂ] σPlus)) := by exact Algebra.smul_mul_assoc _ _ _
      _ = (1/2 : ℂ) • (((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (σMinus ⊗ₜ[ℂ] σPlus) -
          (σ3c ⊗ₜ[ℂ] σ3c) * (σMinus ⊗ₜ[ℂ] σPlus)) := by rw [sub_mul]
      _ = (1/2 : ℂ) • (((1 : M2C) * σMinus) ⊗ₜ[ℂ] ((1 : M2C) * σPlus) -
          (σ3c * σMinus) ⊗ₜ[ℂ] (σ3c * σPlus)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - (-σMinus) ⊗ₜ[ℂ] σPlus) := by
        simp [σ3c_mul_σMinus, σ3c_mul_σPlus]
      _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus - (-(σMinus ⊗ₜ[ℂ] σPlus))) := by
        simp [TensorProduct.neg_tmul]
      _ = (1/2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus + σMinus ⊗ₜ[ℂ] σPlus) := by simp
      _ = (1/2 : ℂ) • ((2 : ℂ) • (σMinus ⊗ₜ[ℂ] σPlus)) := by simp [two_smul]
      _ = σMinus ⊗ₜ[ℂ] σPlus := by simp [smul_smul]
  -- Projector soldering: XY + YX = Z
  have hXY_YX : X * Y + Y * X = Z := by
    unfold X Y Z
    simpa only [PPlus, PMinus, ← Algebra.TensorProduct.tmul_mul_tmul] using
      projector_tensor_identity
  -- Assemble with grouped expansion — keeps X*Y + Y*X syntactically together
  have h_expand :
      (X + Y + Z) * (X + Y + Z) =
        (X*X + Y*Y) + (X*Y + Y*X) + (X*Z + Z*X) + (Y*Z + Z*Y) + Z*Z := by
    noncomm_ring
  rw [h_expand]
  rw [hXX, hYY, hXY_YX, hXZ, hZX, hYZ, hZY, hZZ]
  simp [two_smul, smul_add]; abel

/-! ## Klein Classification -/

structure KleinClassification where
  parabolicPlus : SpinPair
  parabolicMinus : SpinPair
  hyperbolicCartan : SpinPair
  parabolic_nilpotent : parabolicPlus * parabolicPlus = 0 ∧ parabolicMinus * parabolicMinus = 0
  hyperbolic_idempotent : hyperbolicCartan * hyperbolicCartan = hyperbolicCartan
  decomposition : e = parabolicPlus + parabolicMinus + hyperbolicCartan
  projector_soldering : parabolicPlus * parabolicMinus + parabolicMinus * parabolicPlus = hyperbolicCartan

def klein_classification : KleinClassification where
  parabolicPlus := σPlus ⊗ₜ[ℂ] σMinus
  parabolicMinus := σMinus ⊗ₜ[ℂ] σPlus
  hyperbolicCartan := (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)
  parabolic_nilpotent := by
    constructor
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; simp [ σPlus_sq, σMinus_sq]
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; simp [ σMinus_sq, σPlus_sq]
  hyperbolic_idempotent := by
    let A := (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c
    have hA_sq : A * A = (2 : ℂ) • A := by
      dsimp [A]
      rw [mul_sub, sub_mul, sub_mul]
      have h1 : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
      have h2 : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) * (σ3c ⊗ₜ[ℂ] σ3c) = σ3c ⊗ₜ[ℂ] σ3c := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
      have h3 : (σ3c ⊗ₜ[ℂ] σ3c) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) = σ3c ⊗ₜ[ℂ] σ3c := by
        rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
      have h4 : (σ3c ⊗ₜ[ℂ] σ3c) * (σ3c ⊗ₜ[ℂ] σ3c) = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) :=
        calc
          (σ3c ⊗ₜ[ℂ] σ3c) * (σ3c ⊗ₜ[ℂ] σ3c) = (σ3c * σ3c) ⊗ₜ[ℂ] (σ3c * σ3c) :=
            Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
          _ = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) := by rw [σ3c_sq]
      rw [h1, h2, h3, h4]; abel; simp [two_smul]
    calc
      ((1/2 : ℂ) • A) * ((1/2 : ℂ) • A) = ((1/2 : ℂ) * (1/2 : ℂ)) • (A * A) := by
        calc
          ((1/2 : ℂ) • A) * ((1/2 : ℂ) • A) = (1/2 : ℂ) • (A * ((1/2 : ℂ) • A)) :=
            Algebra.smul_mul_assoc _ _ _
          _ = (1/2 : ℂ) • ((1/2 : ℂ) • (A * A)) := by
            rw [Algebra.mul_smul_comm (1/2 : ℂ) A A]
          _ = ((1/2 : ℂ) * (1/2 : ℂ)) • (A * A) := by rw [smul_smul]
      _ = (1/2 : ℂ) • A := by
        rw [hA_sq]; dsimp [A]; simp [smul_smul]
  decomposition := rfl
  projector_soldering := by
    simpa only [PPlus, PMinus, ← Algebra.TensorProduct.tmul_mul_tmul] using
      projector_tensor_identity

/-! ## Synthesis -/

def loopParameter : ℂ := 2
noncomputable def braidParameter : ℂ := Complex.I

theorem loop_eq : loopParameter = 2 := rfl

theorem braid_relation : loopParameter = -(braidParameter ^ 2) - (braidParameter⁻¹) ^ 2 := by
  dsimp [loopParameter, braidParameter]
  norm_num

/-- The Jones representation of the braid generator. -/
noncomputable def b : SpinPair :=
  braidParameter • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) + braidParameter⁻¹ • e

/-- The inverse of the braid generator. -/
noncomputable def bInv : SpinPair :=
  braidParameter⁻¹ • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) + braidParameter • e

theorem chiral_tl_recoupling_synthesis :
    (e * e = (2 : ℂ) • e) ∧
    ((σPlus ⊗ₜ[ℂ] σMinus) * (σPlus ⊗ₜ[ℂ] σMinus) = 0) ∧
    ((σMinus ⊗ₜ[ℂ] σPlus) * (σMinus ⊗ₜ[ℂ] σPlus) = 0) ∧
    (PPlus ⊗ₜ[ℂ] PMinus + PMinus ⊗ₜ[ℂ] PPlus =
      (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) ∧
    (loopParameter = 2) ∧
    (loopParameter = -(braidParameter ^ 2) - (braidParameter⁻¹) ^ 2) := by
  refine ⟨e_sq, ?_, ?_, projector_tensor_identity, loop_eq, braid_relation⟩
  · rw [Algebra.TensorProduct.tmul_mul_tmul]; simp [ σPlus_sq, σMinus_sq]
  · rw [Algebra.TensorProduct.tmul_mul_tmul]; simp [ σMinus_sq, σPlus_sq]

/-! ## Cl(1,1) factorization — the TL generator factors through the CPT atom

The chiral TL generator `e = X+Y+Z` is built from `σ⁺, σ⁻, σ₃`. The
Cl(1,1)→chiral CAR weld expresses `σ⁺, σ⁻, σ₃` in terms of the real
Clifford generators `eps, J, CPT`. Substituting, `e` factors entirely
through the complexified Cl(1,1) atom. This closes the GEPA loop from
`SplitClifford.carAnn/carCre` to the 4-cell τ-ideal stability spine. -/

open _root_.InfoGeometry.Physics.CPTAtom

/-- The TL generator `e` factors through the complexified Cl(1,1) atom.
Expressed in terms of `eps_c = complexifyCl11 eps`, `J_c = complexifyCl11 J`,
`CPT_c = complexifyCl11 CPT`:
  `e = ½(eps_c⊗eps_c - J_c⊗J_c + I⊗I - CPT_c⊗CPT_c)`

This theorem routes the GEPA edge from `ChiralTensorRecoupling.e` to
`ChiralCausalCone.cl11_atom_to_chiral_CAR_basis`, closing the loop
from the real Clifford root to the chiral τ-ideal stability spine. -/
theorem e_factors_through_cl11_atom :
    e = (1/2 : ℂ) • (
      ((complexifyCl11 _root_.InfoGeometry.Physics.CPTAtom.eps) ⊗ₜ[ℂ] (complexifyCl11 _root_.InfoGeometry.Physics.CPTAtom.eps)) -
      ((complexifyCl11 _root_.InfoGeometry.Physics.CPTAtom.J) ⊗ₜ[ℂ] (complexifyCl11 _root_.InfoGeometry.Physics.CPTAtom.J)) +
      ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) -
      ((complexifyCl11 _root_.InfoGeometry.Physics.CPTAtom.CPT) ⊗ₜ[ℂ] (complexifyCl11 _root_.InfoGeometry.Physics.CPTAtom.CPT))
    ) := by
  -- Extract the weld identities
  have h_eps := complexifyCl11_eps
  have h_J := complexifyCl11_J
  have h_CPT := complexifyCl11_CPT
  have h_σPlus := σPlus_from_cl11
  have h_σMinus := σMinus_from_cl11
  -- Substitute into e = X + Y + Z
  unfold e X Y Z
  rw [h_σPlus, h_σMinus, h_CPT]
  -- Now everything is in terms of eps_c, J_c, CPT_c. Expand the algebra.
  simp [TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, smul_add, smul_sub]
  module

/-! ## Finite recoupling coefficient packets -/

namespace BashoreIntertwinerQubit

/-- Six computational-basis indices supporting the two intertwiner vectors. -/
def intertwinerSupport : List ℕ := [3, 5, 6, 9, 10, 12]

/-- First rational intertwiner coefficient vector. -/
def coeffZeroI : ℕ → ℚ
  | 5 => 1 / 2
  | 6 => -1 / 2
  | 9 => -1 / 2
  | 10 => 1 / 2
  | _ => 0

/-- Unnormalized second rational intertwiner coefficient vector. -/
def coeffOneIRaw : ℕ → ℚ
  | 3 => 1
  | 12 => 1
  | 5 => -1 / 2
  | 6 => -1 / 2
  | 9 => -1 / 2
  | 10 => -1 / 2
  | _ => 0

/-- Dot product restricted to the six support indices. -/
def supportDot (a b : ℕ → ℚ) : ℚ :=
  (intertwinerSupport.map (fun n => a n * b n)).sum

@[simp] theorem intertwiner_support_length : intertwinerSupport.length = 6 := rfl

theorem coeffZeroI_norm : supportDot coeffZeroI coeffZeroI = 1 := by
  norm_num [supportDot, intertwinerSupport, coeffZeroI]

theorem coeffOneIRaw_norm : supportDot coeffOneIRaw coeffOneIRaw = 3 := by
  norm_num [supportDot, intertwinerSupport, coeffOneIRaw]

theorem coeffZeroI_coeffOneIRaw_orthogonal :
    supportDot coeffZeroI coeffOneIRaw = 0 := by
  norm_num [supportDot, intertwinerSupport, coeffZeroI, coeffOneIRaw]

end BashoreIntertwinerQubit

namespace TwoQubitSchurCoefficients

/-- Computational basis indices for two qubits. -/
def basis : List ℕ := [0, 1, 2, 3]

/-- Raw singlet coefficient vector `|01⟩ - |10⟩`. -/
def singletRaw : ℕ → ℚ
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Raw zero-weight triplet coefficient vector `|01⟩ + |10⟩`. -/
def tripletZeroRaw : ℕ → ℚ
  | 1 => 1
  | 2 => 1
  | _ => 0

/-- Dot product over the four computational basis indices. -/
def dot (a b : ℕ → ℚ) : ℚ := (basis.map (fun n => a n * b n)).sum

@[simp] theorem basis_length : basis.length = 4 := rfl

@[simp] theorem singlet_raw_norm : dot singletRaw singletRaw = 2 := by
  norm_num [dot, basis, singletRaw]

@[simp] theorem triplet_zero_raw_norm : dot tripletZeroRaw tripletZeroRaw = 2 := by
  norm_num [dot, basis, tripletZeroRaw]

@[simp] theorem singlet_triplet_zero_orthogonal :
    dot singletRaw tripletZeroRaw = 0 := by
  norm_num [dot, basis, singletRaw, tripletZeroRaw]

end TwoQubitSchurCoefficients

#check e_factors_through_cl11_atom

theorem tl_parameter_two_nilpotent_eq_zero (x : SpinPair)
    (h_tl : x * x = (2 : ℂ) • x)
    (h_nil : x * x = 0) :
    x = 0 := by
  have hsmul : (2 : ℂ) • x = 0 := by
    rw [← h_tl, h_nil]
  exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)

/-! ## Braid Invertibility & 3-Strand Yang–Baxter / Temperley–Lieb Bridge -/

private lemma spinPair_one_def : ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) : SpinPair) = 1 := by
  rw [Algebra.TensorProduct.one_def]

section ThreeStrand

/-- Three-strand spin operator carrier `M₂(ℂ) ⊗ M₂(ℂ) ⊗ M₂(ℂ)` (left-associated). -/
abbrev SpinTriple := M2C ⊗[ℂ] M2C ⊗[ℂ] M2C

local instance : Semiring SpinPair := Algebra.TensorProduct.instSemiring
local instance : Ring SpinPair := Algebra.TensorProduct.instRing
local instance : Algebra ℂ SpinPair := Algebra.TensorProduct.instAlgebra
local instance : Semiring SpinTriple := Algebra.TensorProduct.instSemiring
local instance : Ring SpinTriple := Algebra.TensorProduct.instRing
local instance : Algebra ℂ SpinTriple := Algebra.TensorProduct.instAlgebra

private lemma b_eq_smul_sub : b = Complex.I • ((1 : SpinPair) - e) := by
  unfold b
  rw [spinPair_one_def]
  have hInv : braidParameter⁻¹ = -Complex.I := by
    dsimp [braidParameter]; exact Complex.inv_I
  change Complex.I • (1 : SpinPair) + braidParameter⁻¹ • e = Complex.I • ((1 : SpinPair) - e)
  rw [hInv, smul_sub, neg_smul, sub_eq_add_neg]

private lemma bInv_eq_smul_sub : bInv = (-Complex.I) • ((1 : SpinPair) - e) := by
  unfold bInv
  rw [spinPair_one_def]
  have hInv : braidParameter⁻¹ = -Complex.I := by
    dsimp [braidParameter]; exact Complex.inv_I
  change braidParameter⁻¹ • (1 : SpinPair) + Complex.I • e = (-Complex.I) • ((1 : SpinPair) - e)
  rw [hInv, smul_sub, neg_smul, neg_smul, sub_neg_eq_add]

theorem b_mul_bInv : b * bInv = 1 := by
  rw [b_eq_smul_sub, bInv_eq_smul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have hI : Complex.I * -Complex.I = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h1e : ((1 : SpinPair) - e) * ((1 : SpinPair) - e) = 1 := by
    have hexp : ((1 : SpinPair) - e) * ((1 : SpinPair) - e) = 1 - 2 • e + e * e := by
      noncomm_ring
    rw [hexp, e_sq]
    module
  rw [hI, h1e, one_smul]

theorem bInv_mul_b : bInv * b = 1 := by
  rw [b_eq_smul_sub, bInv_eq_smul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have hI : -Complex.I * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I, neg_neg]
  have h1e : ((1 : SpinPair) - e) * ((1 : SpinPair) - e) = 1 := by
    have hexp : ((1 : SpinPair) - e) * ((1 : SpinPair) - e) = 1 - 2 • e + e * e := by
      noncomm_ring
    rw [hexp, e_sq]
    module
  rw [hI, h1e, one_smul]

/-- Left two-strand embedding `x ↦ x ⊗ 1` into `SpinTriple`. -/
def embedLeft : SpinPair →ₐ[ℂ] SpinTriple :=
  Algebra.TensorProduct.includeLeft

/-- Right two-strand embedding `y ⊗ z ↦ (1 ⊗ y) ⊗ z` into `SpinTriple`. -/
def embedRight : SpinPair →ₐ[ℂ] SpinTriple :=
  Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : M2C →ₐ[ℂ] SpinPair)
    (AlgHom.id ℂ M2C)

/-- First 3-strand Temperley–Lieb generator `e₁ = e ⊗ 1`. -/
def e₁ : SpinTriple := embedLeft e

/-- Second 3-strand Temperley–Lieb generator `e₂ = 1 ⊗ e`. -/
def e₂ : SpinTriple := embedRight e

/-- First 3-strand braid generator `b₁ = b ⊗ 1`. -/
def b₁ : SpinTriple := embedLeft b

/-- Second 3-strand braid generator `b₂ = 1 ⊗ b`. -/
def b₂ : SpinTriple := embedRight b

/-- Inverse of the first 3-strand braid generator `b₁⁻¹ = bInv ⊗ 1`. -/
def b₁Inv : SpinTriple := embedLeft bInv

/-- Inverse of the second 3-strand braid generator `b₂⁻¹ = 1 ⊗ bInv`. -/
def b₂Inv : SpinTriple := embedRight bInv

theorem e₁_sq : e₁ * e₁ = (2 : ℂ) • e₁ := by
  unfold e₁
  rw [← map_mul, e_sq, map_smul]

theorem e₂_sq : e₂ * e₂ = (2 : ℂ) • e₂ := by
  unfold e₂
  rw [← map_mul, e_sq, map_smul]

theorem b₁_mul_b₁Inv : b₁ * b₁Inv = 1 := by
  unfold b₁ b₁Inv
  rw [← map_mul, b_mul_bInv, map_one]

theorem b₁Inv_mul_b₁ : b₁Inv * b₁ = 1 := by
  unfold b₁ b₁Inv
  rw [← map_mul, bInv_mul_b, map_one]

theorem b₂_mul_b₂Inv : b₂ * b₂Inv = 1 := by
  unfold b₂ b₂Inv
  rw [← map_mul, b_mul_bInv, map_one]

theorem b₂Inv_mul_b₂ : b₂Inv * b₂ = 1 := by
  unfold b₂ b₂Inv
  rw [← map_mul, bInv_mul_b, map_one]

private lemma PPlus_mul_σPlus_eq : PPlus * σPlus = σPlus := by
  rw [PPlus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma σPlus_mul_PPlus_eq : σPlus * PPlus = 0 := by
  rw [PPlus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma PPlus_mul_σMinus_eq : PPlus * σMinus = 0 := by
  rw [PPlus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σMinus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma σMinus_mul_PPlus_eq : σMinus * PPlus = σMinus := by
  rw [PPlus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σMinus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma PMinus_mul_σPlus_eq : PMinus * σPlus = 0 := by
  rw [PMinus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma σPlus_mul_PMinus_eq : σPlus * PMinus = σPlus := by
  rw [PMinus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σPlus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma PMinus_mul_σMinus_eq : PMinus * σMinus = σMinus := by
  rw [PMinus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σMinus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma σMinus_mul_PMinus_eq : σMinus * PMinus = 0 := by
  rw [PMinus_matrix]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [σMinus, Matrix.mul_apply, Fin.sum_univ_two]

private lemma e_eq_chiral_projectors :
    e = σPlus ⊗ₜ[ℂ] σMinus + σMinus ⊗ₜ[ℂ] σPlus + PPlus ⊗ₜ[ℂ] PMinus + PMinus ⊗ₜ[ℂ] PPlus := by
  rw [e_eq_X_add_Y_add_Z, X, Y, Z, ← projector_tensor_identity, PPlus, PMinus]
  abel

private lemma embedLeft_tmul (x y : M2C) :
    embedLeft (x ⊗ₜ[ℂ] y) = (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (1 : M2C) := by
  unfold embedLeft
  rfl

private lemma embedRight_tmul (y z : M2C) :
    embedRight (y ⊗ₜ[ℂ] z) = ((1 : M2C) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z := by
  unfold embedRight
  rfl

private lemma e₁_expand :
    e₁ = (σPlus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] (1 : M2C) +
         (σMinus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] (1 : M2C) +
         (PPlus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] (1 : M2C) +
         (PMinus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] (1 : M2C) := by
  unfold e₁
  rw [e_eq_chiral_projectors, map_add, map_add, map_add]
  rfl

private lemma e₂_expand :
    e₂ = ((1 : M2C) ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] σMinus +
         ((1 : M2C) ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] σPlus +
         ((1 : M2C) ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] PMinus +
         ((1 : M2C) ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] PPlus := by
  unfold e₂
  rw [e_eq_chiral_projectors, map_add, map_add, map_add]
  rfl

private lemma triple_tmul_mul (a₁ a₂ a₃ b₁ b₂ b₃ : M2C) :
    ((a₁ ⊗ₜ[ℂ] a₂) ⊗ₜ[ℂ] a₃) * ((b₁ ⊗ₜ[ℂ] b₂) ⊗ₜ[ℂ] b₃) =
      ((a₁ * b₁) ⊗ₜ[ℂ] (a₂ * b₂)) ⊗ₜ[ℂ] (a₃ * b₃) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]

theorem e₁_mul_e₂_mul_e₁ : e₁ * e₂ * e₁ = e₁ := by
  have he12 : e₁ * e₂ =
      ((σPlus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] σMinus) +
      ((σPlus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] PMinus) +
      ((σMinus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] σPlus) +
      ((σMinus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] PPlus) +
      ((PPlus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] σPlus) +
      ((PPlus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] PPlus) +
      ((PMinus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] σMinus) +
      ((PMinus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] PMinus) := by
    rw [e₁_expand, e₂_expand]
    simp only [add_mul, mul_add, triple_tmul_mul, mul_one, one_mul,
      σPlus_sq, σMinus_sq, show σPlus * σMinus = PPlus from rfl, show σMinus * σPlus = PMinus from rfl,
      PPlus_idempotent, PMinus_idempotent, PPlus_PMinus_orthogonal, PMinus_PPlus_orthogonal,
      PPlus_mul_σPlus_eq, σPlus_mul_PPlus_eq, PPlus_mul_σMinus_eq, σMinus_mul_PPlus_eq,
      PMinus_mul_σPlus_eq, σPlus_mul_PMinus_eq, PMinus_mul_σMinus_eq, σMinus_mul_PMinus_eq,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, add_zero]
    abel
  have h121 : e₁ * e₂ * e₁ =
      ((σPlus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] PPlus + (σPlus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] PMinus) +
      ((σMinus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] PPlus + (σMinus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] PMinus) +
      ((PPlus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] PPlus + (PPlus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] PMinus) +
      ((PMinus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] PPlus + (PMinus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] PMinus) := by
    rw [he12, e₁_expand]
    simp only [add_mul, mul_add, triple_tmul_mul, mul_one,
      σPlus_sq, σMinus_sq, show σPlus * σMinus = PPlus from rfl, show σMinus * σPlus = PMinus from rfl,
      PPlus_idempotent, PMinus_idempotent, PPlus_PMinus_orthogonal, PMinus_PPlus_orthogonal,
      PPlus_mul_σPlus_eq, σPlus_mul_PPlus_eq, PPlus_mul_σMinus_eq, σMinus_mul_PPlus_eq,
      PMinus_mul_σPlus_eq, σPlus_mul_PMinus_eq, PMinus_mul_σMinus_eq, σMinus_mul_PMinus_eq,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, add_zero]
    abel
  have hsum : ∀ x y : M2C,
      (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] PPlus + (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] PMinus = (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (1 : M2C) := by
    intro x y
    rw [← TensorProduct.tmul_add, PPlus_add_PMinus]
  rw [h121, hsum, hsum, hsum, hsum, e₁_expand]

theorem e₂_mul_e₁_mul_e₂ : e₂ * e₁ * e₂ = e₂ := by
  have he21 : e₂ * e₁ =
      ((σPlus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] σMinus) +
      ((σMinus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] σPlus) +
      ((PPlus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] σMinus) +
      ((PMinus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] σPlus) +
      ((σPlus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] PPlus) +
      ((PPlus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] PPlus) +
      ((σMinus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] PMinus) +
      ((PMinus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] PMinus) := by
    rw [e₂_expand, e₁_expand]
    simp only [add_mul, mul_add, triple_tmul_mul, mul_one, one_mul,
      σPlus_sq, σMinus_sq, show σPlus * σMinus = PPlus from rfl, show σMinus * σPlus = PMinus from rfl,
      PPlus_idempotent, PMinus_idempotent, PPlus_PMinus_orthogonal, PMinus_PPlus_orthogonal,
      PPlus_mul_σPlus_eq, σPlus_mul_PPlus_eq, PPlus_mul_σMinus_eq, σMinus_mul_PPlus_eq,
      PMinus_mul_σPlus_eq, σPlus_mul_PMinus_eq, PMinus_mul_σMinus_eq, σMinus_mul_PMinus_eq,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, add_zero]
    abel
  have h212 : e₂ * e₁ * e₂ =
      ((PPlus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] σMinus + (PMinus ⊗ₜ[ℂ] σPlus) ⊗ₜ[ℂ] σMinus) +
      ((PPlus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] σPlus + (PMinus ⊗ₜ[ℂ] σMinus) ⊗ₜ[ℂ] σPlus) +
      ((PPlus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] PMinus + (PMinus ⊗ₜ[ℂ] PPlus) ⊗ₜ[ℂ] PMinus) +
      ((PPlus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] PPlus + (PMinus ⊗ₜ[ℂ] PMinus) ⊗ₜ[ℂ] PPlus) := by
    rw [he21, e₂_expand]
    simp only [add_mul, mul_add, triple_tmul_mul, mul_one,
      σPlus_sq, σMinus_sq, show σPlus * σMinus = PPlus from rfl, show σMinus * σPlus = PMinus from rfl,
      PPlus_idempotent, PMinus_idempotent, PPlus_PMinus_orthogonal, PMinus_PPlus_orthogonal,
      PPlus_mul_σPlus_eq, σPlus_mul_PPlus_eq, PPlus_mul_σMinus_eq, σMinus_mul_PPlus_eq,
      PMinus_mul_σPlus_eq, σPlus_mul_PMinus_eq, PMinus_mul_σMinus_eq, σMinus_mul_PMinus_eq,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, add_zero]
    abel
  have hsum : ∀ y z : M2C,
      (PPlus ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z + (PMinus ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z = ((1 : M2C) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z := by
    intro y z
    rw [← TensorProduct.add_tmul, ← TensorProduct.add_tmul, PPlus_add_PMinus]
  rw [h212, hsum, hsum, hsum, hsum, e₂_expand]

private lemma b₁_eq_smul_sub :
    b₁ = Complex.I • ((1 : SpinTriple) - e₁) := by
  unfold b₁ e₁ b
  rw [spinPair_one_def, map_add, map_smul, map_smul, map_one]
  have hInv : braidParameter⁻¹ = -Complex.I := by
    dsimp [braidParameter]; exact Complex.inv_I
  change Complex.I • (1 : SpinTriple) + braidParameter⁻¹ • embedLeft e =
    Complex.I • ((1 : SpinTriple) - embedLeft e)
  rw [hInv, smul_sub, neg_smul, sub_eq_add_neg]

private lemma b₂_eq_smul_sub :
    b₂ = Complex.I • ((1 : SpinTriple) - e₂) := by
  unfold b₂ e₂ b
  rw [spinPair_one_def, map_add, map_smul, map_smul, map_one]
  have hInv : braidParameter⁻¹ = -Complex.I := by
    dsimp [braidParameter]; exact Complex.inv_I
  change Complex.I • (1 : SpinTriple) + braidParameter⁻¹ • embedRight e =
    Complex.I • ((1 : SpinTriple) - embedRight e)
  rw [hInv, smul_sub, neg_smul, sub_eq_add_neg]

/-- **3-Strand Yang–Baxter / Reidemeister III Equation (`b₁ * b₂ * b₁ = b₂ * b₁ * b₂`)**. -/
theorem braid_yang_baxter : b₁ * b₂ * b₁ = b₂ * b₁ * b₂ := by
  rw [b₁_eq_smul_sub, b₂_eq_smul_sub]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  congr 1
  have h1 : ((1 : SpinTriple) - e₁) * ((1 : SpinTriple) - e₂) * ((1 : SpinTriple) - e₁) =
      (1 : SpinTriple) - e₁ - e₂ + e₁ * e₂ + e₂ * e₁ := by
    have hexp :
        ((1 : SpinTriple) - e₁) * ((1 : SpinTriple) - e₂) * ((1 : SpinTriple) - e₁) =
          1 - 2 • e₁ - e₂ + e₁ * e₁ + e₁ * e₂ + e₂ * e₁ - e₁ * e₂ * e₁ := by
      noncomm_ring
    rw [hexp, e₁_sq, e₁_mul_e₂_mul_e₁]
    module
  have h2 : ((1 : SpinTriple) - e₂) * ((1 : SpinTriple) - e₁) * ((1 : SpinTriple) - e₂) =
      (1 : SpinTriple) - e₁ - e₂ + e₁ * e₂ + e₂ * e₁ := by
    have hexp :
        ((1 : SpinTriple) - e₂) * ((1 : SpinTriple) - e₁) * ((1 : SpinTriple) - e₂) =
          1 - 2 • e₂ - e₁ + e₂ * e₂ + e₂ * e₁ + e₁ * e₂ - e₂ * e₁ * e₂ := by
      noncomm_ring
    rw [hexp, e₂_sq, e₂_mul_e₁_mul_e₂]
    module
  rw [h1, h2]

end ThreeStrand

section GeneralizedChiralRecoupling

/-- General algebraic similarity obstruction between two Temperley–Lieb / idempotent
parameters `d₁` and `d₂` in any associative `R`-algebra: if `e₁² = d₁ • e₁`,
`e₂² = d₂ • e₂`, and `u * e₁ * u⁻¹ = e₂`, then `(d₁ - d₂) • e₂ = 0`. -/
theorem tl_similarity_param_obstruction {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {e₁ e₂ : A} {d₁ d₂ : R} (u : Aˣ)
    (he₁ : e₁ * e₁ = d₁ • e₁) (he₂ : e₂ * e₂ = d₂ • e₂)
    (hconj : (u : A) * e₁ * (↑u⁻¹ : A) = e₂) :
    (d₁ - d₂) • e₂ = 0 := by
  have hsq : e₂ * e₂ = d₁ • e₂ := by
    calc
      e₂ * e₂ = ((u : A) * e₁ * (↑u⁻¹ : A)) * ((u : A) * e₁ * (↑u⁻¹ : A)) := by rw [hconj]
      _ = (u : A) * (e₁ * ((↑u⁻¹ : A) * (u : A)) * e₁) * (↑u⁻¹ : A) := by
          simp only [mul_assoc]
      _ = (u : A) * (e₁ * e₁) * (↑u⁻¹ : A) := by
          rw [Units.inv_mul, mul_one]
      _ = (u : A) * (d₁ • e₁) * (↑u⁻¹ : A) := by rw [he₁]
      _ = d₁ • ((u : A) * e₁ * (↑u⁻¹ : A)) := by
          rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      _ = d₁ • e₂ := by rw [hconj]
  rw [sub_smul, ← hsq, he₂, sub_self]

/-- Corollary (`d = 2` vs `d = 1` over any commutative ring, no invertibility needed):
a loop-parameter-`2` operator and an idempotent (`d = 1`) cannot be conjugate unless both vanish. -/
theorem tl_two_not_similar_to_one {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {e₁ e₂ : A} (u : Aˣ)
    (he₁ : e₁ * e₁ = (2 : R) • e₁) (he₂ : e₂ * e₂ = (1 : R) • e₂)
    (hconj : (u : A) * e₁ * (↑u⁻¹ : A) = e₂) :
    e₁ = 0 ∧ e₂ = 0 := by
  have hob : ((2 : R) - 1) • e₂ = 0 := tl_similarity_param_obstruction u he₁ he₂ hconj
  have he₂_zero : e₂ = 0 := by
    rw [show (2 : R) - 1 = 1 by ring, one_smul] at hob
    exact hob
  have he₁_zero : e₁ = 0 := by
    calc
      e₁ = ((↑u⁻¹ : A) * (u : A)) * e₁ * ((↑u⁻¹ : A) * (u : A)) := by
          rw [Units.inv_mul, one_mul, mul_one]
      _ = (↑u⁻¹ : A) * ((u : A) * e₁ * (↑u⁻¹ : A)) * (u : A) := by
          simp only [mul_assoc]
      _ = (↑u⁻¹ : A) * e₂ * (u : A) := by rw [hconj]
      _ = 0 := by rw [he₂_zero, mul_zero, zero_mul]
  exact ⟨he₁_zero, he₂_zero⟩

/-- Corollary (`d = 2` vs `d = 0` over any `[CommRing R]` with `[Invertible (2 : R)]`):
a `d = 2` operator and a nilpotent `e₂² = 0` cannot be conjugate unless both vanish. -/
theorem tl_two_not_similar_to_zero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Invertible (2 : R)] {e₁ e₂ : A} (u : Aˣ)
    (he₁ : e₁ * e₁ = (2 : R) • e₁) (he₂ : e₂ * e₂ = (0 : R) • e₂)
    (hconj : (u : A) * e₁ * (↑u⁻¹ : A) = e₂) :
    e₁ = 0 ∧ e₂ = 0 := by
  have hob : ((2 : R) - 0) • e₂ = 0 := tl_similarity_param_obstruction u he₁ he₂ hconj
  rw [sub_zero] at hob
  have he₂_zero : e₂ = 0 := by
    calc
      e₂ = ⅟(2 : R) • ((2 : R) • e₂) := by
          rw [smul_smul, invOf_mul_self, one_smul]
      _ = 0 := by rw [hob, smul_zero]
  have he₁_zero : e₁ = 0 := by
    calc
      e₁ = ((↑u⁻¹ : A) * (u : A)) * e₁ * ((↑u⁻¹ : A) * (u : A)) := by
          rw [Units.inv_mul, one_mul, mul_one]
      _ = (↑u⁻¹ : A) * ((u : A) * e₁ * (↑u⁻¹ : A)) * (u : A) := by
          simp only [mul_assoc]
      _ = (↑u⁻¹ : A) * e₂ * (u : A) := by rw [hconj]
      _ = 0 := by rw [he₂_zero, mul_zero, zero_mul]
  exact ⟨he₁_zero, he₂_zero⟩

/-- Generalized `2 × 2` chiral Pauli operators over an arbitrary `[CommRing R]`. -/
def sigmaPlusR (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
def sigmaMinusR (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]
def sigma3R (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]
def pPlusR (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]
def pMinusR (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 0, 1]

/-- Generalized two-site spin carrier `M₂(R) ⊗[R] M₂(R)` over any `[CommRing R]`. -/
abbrev SpinPairR (R : Type*) [CommRing R] :=
  Matrix (Fin 2) (Fin 2) R ⊗[R] Matrix (Fin 2) (Fin 2) R

local instance (R : Type*) [CommRing R] : Semiring (SpinPairR R) :=
  Algebra.TensorProduct.instSemiring
local instance (R : Type*) [CommRing R] : Ring (SpinPairR R) :=
  Algebra.TensorProduct.instRing
local instance (R : Type*) [CommRing R] : Algebra R (SpinPairR R) :=
  Algebra.TensorProduct.instAlgebra

/-- Generalized Temperley–Lieb generator over any `[CommRing R]` with `[Invertible (2 : R)]`. -/
def tlGenR (R : Type*) [CommRing R] [Invertible (2 : R)] : SpinPairR R :=
  sigmaPlusR R ⊗ₜ[R] sigmaMinusR R +
    sigmaMinusR R ⊗ₜ[R] sigmaPlusR R +
    ⅟(2 : R) • ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) -
      sigma3R R ⊗ₜ[R] sigma3R R)

/-- Generalized chiral-sign-flipped singlet-twice operator
`(σ₃ ⊗ 1) · tlGenR R · (σ₃ ⊗ 1) = -σ⁺⊗σ⁻ - σ⁻⊗σ⁺ + ⅟2 (1⊗1 - σ₃⊗σ₃)`. -/
def singletDoubleSpinPairR (R : Type*) [CommRing R] [Invertible (2 : R)] : SpinPairR R :=
  -(sigmaPlusR R ⊗ₜ[R] sigmaMinusR R) -
    sigmaMinusR R ⊗ₜ[R] sigmaPlusR R +
    ⅟(2 : R) • ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) -
      sigma3R R ⊗ₜ[R] sigma3R R)

theorem sigmaPlusR_sq (R : Type*) [CommRing R] :
    sigmaPlusR R * sigmaPlusR R = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaPlusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaMinusR_sq (R : Type*) [CommRing R] :
    sigmaMinusR R * sigmaMinusR R = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaMinusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaPlusR_mul_sigmaMinusR (R : Type*) [CommRing R] :
    sigmaPlusR R * sigmaMinusR R = pPlusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaPlusR, sigmaMinusR, pPlusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaMinusR_mul_sigmaPlusR (R : Type*) [CommRing R] :
    sigmaMinusR R * sigmaPlusR R = pMinusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigmaPlusR, sigmaMinusR, pMinusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigma3R_sq (R : Type*) [CommRing R] :
    sigma3R R * sigma3R R = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3R, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigma3R_conj_sigmaPlusR (R : Type*) [CommRing R] :
    sigma3R R * sigmaPlusR R * sigma3R R = -sigmaPlusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3R, sigmaPlusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigma3R_conj_sigmaMinusR (R : Type*) [CommRing R] :
    sigma3R R * sigmaMinusR R * sigma3R R = -sigmaMinusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3R, sigmaMinusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem pPlusR_add_pMinusR (R : Type*) [CommRing R] :
    pPlusR R + pMinusR R = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pPlusR, pMinusR]

theorem sigma3R_mul_sigmaPlusR (R : Type*) [CommRing R] :
    sigma3R R * sigmaPlusR R = sigmaPlusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3R, sigmaPlusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaPlusR_mul_sigma3R (R : Type*) [CommRing R] :
    sigmaPlusR R * sigma3R R = -sigmaPlusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3R, sigmaPlusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigma3R_mul_sigmaMinusR (R : Type*) [CommRing R] :
    sigma3R R * sigmaMinusR R = -sigmaMinusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3R, sigmaMinusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaMinusR_mul_sigma3R (R : Type*) [CommRing R] :
    sigmaMinusR R * sigma3R R = sigmaMinusR R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma3R, sigmaMinusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem pPlusR_sub_pMinusR (R : Type*) [CommRing R] :
    pPlusR R - pMinusR R = sigma3R R := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pPlusR, pMinusR, sigma3R]

/-- Generalized two-site TL idempotency `(tlGenR R)^2 = 2 • tlGenR R` over any
`[CommRing R]` with `[Invertible (2 : R)]`. -/
theorem tlGenR_sq (R : Type*) [CommRing R] [Invertible (2 : R)] :
    tlGenR R * tlGenR R = (2 : R) • tlGenR R := by
  let XR : SpinPairR R := sigmaPlusR R ⊗ₜ[R] sigmaMinusR R
  let YR : SpinPairR R := sigmaMinusR R ⊗ₜ[R] sigmaPlusR R
  let ZR : SpinPairR R := ⅟(2 : R) •
    ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) -
      sigma3R R ⊗ₜ[R] sigma3R R)
  have hXX : XR * XR = 0 := by
    calc
      XR * XR = (sigmaPlusR R * sigmaPlusR R) ⊗ₜ[R] (sigmaMinusR R * sigmaMinusR R) :=
        Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
      _ = 0 := by rw [sigmaPlusR_sq R, sigmaMinusR_sq R, TensorProduct.zero_tmul]
  have hYY : YR * YR = 0 := by
    calc
      YR * YR = (sigmaMinusR R * sigmaMinusR R) ⊗ₜ[R] (sigmaPlusR R * sigmaPlusR R) :=
        Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
      _ = 0 := by rw [sigmaMinusR_sq R, sigmaPlusR_sq R, TensorProduct.zero_tmul]
  have hXY : XR * YR = pPlusR R ⊗ₜ[R] pMinusR R := by
    calc
      XR * YR = (sigmaPlusR R * sigmaMinusR R) ⊗ₜ[R] (sigmaMinusR R * sigmaPlusR R) :=
        Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
      _ = pPlusR R ⊗ₜ[R] pMinusR R := by
          rw [sigmaPlusR_mul_sigmaMinusR R, sigmaMinusR_mul_sigmaPlusR R]
  have hYX : YR * XR = pMinusR R ⊗ₜ[R] pPlusR R := by
    calc
      YR * XR = (sigmaMinusR R * sigmaPlusR R) ⊗ₜ[R] (sigmaPlusR R * sigmaMinusR R) :=
        Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
      _ = pMinusR R ⊗ₜ[R] pPlusR R := by
          rw [sigmaMinusR_mul_sigmaPlusR R, sigmaPlusR_mul_sigmaMinusR R]
  have hXY_YX : XR * YR + YR * XR = ZR := by
    rw [hXY, hYX]
    dsimp [ZR]
    have hZ_eq : (1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) -
        sigma3R R ⊗ₜ[R] sigma3R R =
        (2 : R) • (pPlusR R ⊗ₜ[R] pMinusR R + pMinusR R ⊗ₜ[R] pPlusR R) := by
      have h1 : (1 : Matrix (Fin 2) (Fin 2) R) = pPlusR R + pMinusR R :=
        (pPlusR_add_pMinusR R).symm
      have h3 : sigma3R R = pPlusR R - pMinusR R := (pPlusR_sub_pMinusR R).symm
      rw [h1, h3]
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      rw [two_smul]
      abel
    rw [hZ_eq, smul_smul, invOf_mul_self, one_smul]
  have hZZ : ZR * ZR = ZR := by
    dsimp [ZR]
    let A : SpinPairR R :=
      (1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) -
        sigma3R R ⊗ₜ[R] sigma3R R
    have hAsq : A * A = (2 : R) • A := by
      dsimp [A]
      rw [mul_sub, sub_mul, sub_mul]
      have h11 : ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) *
          ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) =
          (1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have h13 : ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) *
          (sigma3R R ⊗ₜ[R] sigma3R R) = sigma3R R ⊗ₜ[R] sigma3R R := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h31 : (sigma3R R ⊗ₜ[R] sigma3R R) *
          ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) =
          sigma3R R ⊗ₜ[R] sigma3R R := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have h33 : (sigma3R R ⊗ₜ[R] sigma3R R) * (sigma3R R ⊗ₜ[R] sigma3R R) =
          (1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, sigma3R_sq]
      rw [h11, h13, h31, h33, two_smul]
      abel
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hAsq, smul_smul, smul_smul,
      mul_assoc, invOf_mul_self, mul_one]
  have hZX : ZR * XR = XR := by
    dsimp [ZR, XR]
    rw [Algebra.smul_mul_assoc, sub_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.TensorProduct.tmul_mul_tmul, sigma3R_mul_sigmaPlusR, sigma3R_mul_sigmaMinusR,
      TensorProduct.tmul_neg, sub_neg_eq_add, one_mul, ← two_smul R,
      smul_smul, invOf_mul_self, one_smul]
  have hXZ : XR * ZR = XR := by
    dsimp [ZR, XR]
    rw [Algebra.mul_smul_comm, mul_sub,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, sigmaPlusR_mul_sigma3R, sigmaMinusR_mul_sigma3R,
      TensorProduct.neg_tmul, sub_neg_eq_add, mul_one, ← two_smul R,
      smul_smul, invOf_mul_self, one_smul]
  have hZY : ZR * YR = YR := by
    dsimp [ZR, YR]
    rw [Algebra.smul_mul_assoc, sub_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.TensorProduct.tmul_mul_tmul, sigma3R_mul_sigmaMinusR, sigma3R_mul_sigmaPlusR,
      TensorProduct.neg_tmul, sub_neg_eq_add, one_mul, ← two_smul R,
      smul_smul, invOf_mul_self, one_smul]
  have hYZ : YR * ZR = YR := by
    dsimp [ZR, YR]
    rw [Algebra.mul_smul_comm, mul_sub,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, sigmaMinusR_mul_sigma3R, sigmaPlusR_mul_sigma3R,
      TensorProduct.tmul_neg, sub_neg_eq_add, mul_one, ← two_smul R,
      smul_smul, invOf_mul_self, one_smul]
  change (XR + YR + ZR) * (XR + YR + ZR) = (2 : R) • (XR + YR + ZR)
  calc
    (XR + YR + ZR) * (XR + YR + ZR) =
        XR * XR + YR * YR + (XR * YR + YR * XR) +
          (XR * ZR + ZR * XR) + (YR * ZR + ZR * YR) + ZR * ZR := by noncomm_ring
    _ = 0 + 0 + ZR + (XR + XR) + (YR + YR) + ZR := by
        rw [hXX, hYY, hXY_YX, hXZ, hZX, hYZ, hZY, hZZ]
    _ = (2 : R) • (XR + YR + ZR) := by
        rw [two_smul]
        abel

/-- The local diagonal chiral sign flip `(σ₃ ⊗ 1)` conjugates `tlGenR R` into
`singletDoubleSpinPairR R` (`2` times the singlet projector), preserving `d = 2`. -/
theorem sigma3_conj_tlGenR (R : Type*) [CommRing R] [Invertible (2 : R)] :
    (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) * tlGenR R *
        (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) =
      singletDoubleSpinPairR R := by
  have hZ : (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) *
      (⅟(2 : R) • ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) -
        sigma3R R ⊗ₜ[R] sigma3R R)) *
      (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) =
      ⅟(2 : R) • ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) -
        sigma3R R ⊗ₜ[R] sigma3R R) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    congr 1
    simp only [mul_sub, sub_mul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, sigma3R_sq]
  have hX : (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) *
      (sigmaPlusR R ⊗ₜ[R] sigmaMinusR R) *
      (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) =
      -(sigmaPlusR R ⊗ₜ[R] sigmaMinusR R) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, sigma3R_conj_sigmaPlusR, TensorProduct.neg_tmul]
  have hY : (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) *
      (sigmaMinusR R ⊗ₜ[R] sigmaPlusR R) *
      (sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)) =
      -(sigmaMinusR R ⊗ₜ[R] sigmaPlusR R) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, sigma3R_conj_sigmaMinusR, TensorProduct.neg_tmul]
  unfold tlGenR singletDoubleSpinPairR
  rw [mul_add, mul_add, add_mul, add_mul, hX, hY, hZ]
  abel

theorem singletDoubleSpinPairR_sq (R : Type*) [CommRing R] [Invertible (2 : R)] :
    singletDoubleSpinPairR R * singletDoubleSpinPairR R =
      (2 : R) • singletDoubleSpinPairR R := by
  rw [← sigma3_conj_tlGenR]
  let S : SpinPairR R := sigma3R R ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R)
  have hS : S * S = 1 := by
    calc
      S * S = (sigma3R R * sigma3R R) ⊗ₜ[R] ((1 : Matrix (Fin 2) (Fin 2) R) * 1) :=
        Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
      _ = (1 : Matrix (Fin 2) (Fin 2) R) ⊗ₜ[R] (1 : Matrix (Fin 2) (Fin 2) R) := by
        rw [sigma3R_sq, mul_one]
      _ = 1 := Algebra.TensorProduct.one_def.symm
  calc
    (S * tlGenR R * S) * (S * tlGenR R * S) =
        S * (tlGenR R * (S * S) * tlGenR R) * S := by simp only [mul_assoc]
    _ = S * (tlGenR R * tlGenR R) * S := by rw [hS, mul_one]
    _ = S * ((2 : R) • tlGenR R) * S := by rw [tlGenR_sq]
    _ = (2 : R) • (S * tlGenR R * S) := by
        rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- Normalized singlet idempotent `singletProjSpinPairR R = ⅟2 • singletDoubleSpinPairR R`
satisfies `P² = P` (`d = 1`) over any `[CommRing R] [Invertible (2 : R)]`. -/
def singletProjSpinPairR (R : Type*) [CommRing R] [Invertible (2 : R)] : SpinPairR R :=
  ⅟(2 : R) • singletDoubleSpinPairR R

theorem singletProjSpinPairR_idempotent (R : Type*) [CommRing R] [Invertible (2 : R)] :
    singletProjSpinPairR R * singletProjSpinPairR R = singletProjSpinPairR R := by
  unfold singletProjSpinPairR
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, singletDoubleSpinPairR_sq,
    smul_smul, smul_smul, mul_assoc, invOf_mul_self, mul_one]

theorem tlGenR_non_zero_of_invertible (R : Type*) [CommRing R] [Invertible (2 : R)]
    [Nontrivial R] : tlGenR R ≠ 0 := by
  intro h0
  have hpair := congrArg (fun M : SpinPairR R =>
    (sigmaMinusR R ⊗ₜ[R] sigmaPlusR R) * M) h0
  rw [mul_zero] at hpair
  have h01 : (sigmaMinusR R ⊗ₜ[R] sigmaPlusR R) * tlGenR R =
      pMinusR R ⊗ₜ[R] pPlusR R + sigmaMinusR R ⊗ₜ[R] sigmaPlusR R := by
    unfold tlGenR
    rw [mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
      sigmaMinusR_mul_sigmaPlusR, sigmaPlusR_mul_sigmaMinusR,
      Algebra.TensorProduct.tmul_mul_tmul, sigmaMinusR_sq, sigmaPlusR_sq,
      TensorProduct.zero_tmul, add_zero, Algebra.mul_smul_comm,
      mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, sigmaMinusR_mul_sigma3R, sigmaPlusR_mul_sigma3R,
      TensorProduct.tmul_neg, sub_neg_eq_add, ← two_smul R, smul_smul,
      invOf_mul_self, one_smul]
  rw [h01] at hpair
  let readout1100 : SpinPairR R →ₗ[R] R :=
    TensorProduct.lift
      { toFun := fun A =>
          { toFun := fun B => A 1 1 * B 0 0
            map_add' := fun B₁ B₂ => by simp [mul_add]
            map_smul' := fun r B => by
              simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
              ring }
        map_add' := fun A₁ A₂ => by ext B; simp [add_mul]
        map_smul' := fun r A => by
          ext B
          simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, smul_eq_mul,
            LinearMap.smul_apply, RingHom.id_apply]
          ring }
  have hentry := congrArg readout1100 hpair
  simp only [map_add, map_zero] at hentry
  change pMinusR R 1 1 * pPlusR R 0 0 + sigmaMinusR R 1 1 * sigmaPlusR R 0 0 = 0 at hentry
  have hval : pMinusR R 1 1 * pPlusR R 0 0 + sigmaMinusR R 1 1 * sigmaPlusR R 0 0 = 1 := by
    simp [pMinusR, pPlusR, sigmaMinusR, sigmaPlusR]
  rw [hval] at hentry
  exact one_ne_zero hentry

end GeneralizedChiralRecoupling

section SingletZeroLoopGaugeBridge

/-- Unitary `d = 2` vs `d = 0` bridge on `SpinPair = M2C ⊗[ℂ] M2C`:
`zeroLoopSpinPair = σ⁺⊗σ⁻ + σ⁻⊗σ⁺ + i (PPlus⊗PMinus - PMinus⊗PPlus)` is nilpotent
(`e₀² = 0`) and is obtained from `e` (`d = 2`) by independent left/right local unitary
factors `(1 ⊗ U_R) * e * (U_L ⊗ 1)`, NOT a similarity conjugation! -/
def zeroLoopLeftTwist : SpinPair := (1 : M2C) ⊗ₜ[ℂ] (PPlus + Complex.I • PMinus)
def zeroLoopRightTwist : SpinPair := (PPlus - Complex.I • PMinus) ⊗ₜ[ℂ] (1 : M2C)

def zeroLoopSpinPair : SpinPair :=
  X + Y + Complex.I • (PPlus ⊗ₜ[ℂ] PMinus - PMinus ⊗ₜ[ℂ] PPlus)

def singletDoubleSpinPair : SpinPair :=
  -(X) - Y + Z

def singletProjSpinPair : SpinPair :=
  (1 / 2 : ℂ) • singletDoubleSpinPair

theorem zeroLoopLeftTwist_unitary :
    zeroLoopLeftTwist * star zeroLoopLeftTwist = 1 ∧
      star zeroLoopLeftTwist * zeroLoopLeftTwist = 1 := by
  have hU : (PPlus + Complex.I • PMinus) * star (PPlus + Complex.I • PMinus) = 1 ∧
      star (PPlus + Complex.I • PMinus) * (PPlus + Complex.I • PMinus) = 1 := by
    rw [PPlus_matrix, PMinus_matrix]
    constructor <;>
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  refine ⟨?_, ?_⟩
  · unfold zeroLoopLeftTwist
    rw [TensorProduct.star_tmul, star_one, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, hU.1, spinPair_one_def]
  · unfold zeroLoopLeftTwist
    rw [TensorProduct.star_tmul, star_one, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, hU.2, spinPair_one_def]

theorem zeroLoopRightTwist_unitary :
    zeroLoopRightTwist * star zeroLoopRightTwist = 1 ∧
      star zeroLoopRightTwist * zeroLoopRightTwist = 1 := by
  have hU : (PPlus - Complex.I • PMinus) * star (PPlus - Complex.I • PMinus) = 1 ∧
      star (PPlus - Complex.I • PMinus) * (PPlus - Complex.I • PMinus) = 1 := by
    rw [PPlus_matrix, PMinus_matrix]
    constructor <;>
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  refine ⟨?_, ?_⟩
  · unfold zeroLoopRightTwist
    rw [TensorProduct.star_tmul, star_one, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, hU.1, spinPair_one_def]
  · unfold zeroLoopRightTwist
    rw [TensorProduct.star_tmul, star_one, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, hU.2, spinPair_one_def]

theorem e_local_unitary_twist_eq_zeroLoopSpinPair :
    zeroLoopLeftTwist * e * zeroLoopRightTwist = zeroLoopSpinPair := by
  have hZ : Z = PPlus ⊗ₜ[ℂ] PMinus + PMinus ⊗ₜ[ℂ] PPlus := by
    unfold Z
    exact projector_tensor_identity.symm
  have hp1 : σPlus * (PPlus - Complex.I • PMinus) = -Complex.I • σPlus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σPlus, Matrix.mul_apply, Fin.sum_univ_two]
  have hp2 : (PPlus + Complex.I • PMinus) * σMinus = Complex.I • σMinus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σMinus, Matrix.mul_apply, Fin.sum_univ_two]
  have hm1 : σMinus * (PPlus - Complex.I • PMinus) = σMinus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σMinus, Matrix.mul_apply, Fin.sum_univ_two]
  have hm2 : (PPlus + Complex.I • PMinus) * σPlus = σPlus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σPlus, Matrix.mul_apply, Fin.sum_univ_two]
  have hpp1 : PPlus * (PPlus - Complex.I • PMinus) = PPlus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hpp2 : (PPlus + Complex.I • PMinus) * PMinus = Complex.I • PMinus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmp1 : PMinus * (PPlus - Complex.I • PMinus) = -Complex.I • PMinus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmp2 : (PPlus + Complex.I • PMinus) * PPlus = PPlus := by
    rw [PPlus_matrix, PMinus_matrix]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hLeft : zeroLoopLeftTwist * e =
      Complex.I • (σPlus ⊗ₜ[ℂ] σMinus) + σMinus ⊗ₜ[ℂ] σPlus +
        Complex.I • (PPlus ⊗ₜ[ℂ] PMinus) + PMinus ⊗ₜ[ℂ] PPlus := by
    let U : M2C := PPlus + Complex.I • PMinus
    have t1 : ((1 : M2C) ⊗ₜ[ℂ] U) * (σPlus ⊗ₜ[ℂ] σMinus) = Complex.I • (σPlus ⊗ₜ[ℂ] σMinus) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp2, TensorProduct.tmul_smul]
    have t2 : ((1 : M2C) ⊗ₜ[ℂ] U) * (σMinus ⊗ₜ[ℂ] σPlus) = σMinus ⊗ₜ[ℂ] σPlus := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hm2]
    have t3 : ((1 : M2C) ⊗ₜ[ℂ] U) * (PPlus ⊗ₜ[ℂ] PMinus) = Complex.I • (PPlus ⊗ₜ[ℂ] PMinus) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hpp2, TensorProduct.tmul_smul]
    have t4 : ((1 : M2C) ⊗ₜ[ℂ] U) * (PMinus ⊗ₜ[ℂ] PPlus) = PMinus ⊗ₜ[ℂ] PPlus := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hmp2]
    unfold e zeroLoopLeftTwist X Y
    rw [hZ]
    change ((1 : M2C) ⊗ₜ[ℂ] U) *
      (σPlus ⊗ₜ[ℂ] σMinus + σMinus ⊗ₜ[ℂ] σPlus + (PPlus ⊗ₜ[ℂ] PMinus + PMinus ⊗ₜ[ℂ] PPlus)) = _
    rw [mul_add, mul_add, mul_add, t1, t2, t3, t4]
    abel
  rw [hLeft]
  let V : M2C := PPlus - Complex.I • PMinus
  have r1 : (Complex.I • (σPlus ⊗ₜ[ℂ] σMinus)) * (V ⊗ₜ[ℂ] (1 : M2C)) = σPlus ⊗ₜ[ℂ] σMinus := by
    calc
      (Complex.I • (σPlus ⊗ₜ[ℂ] σMinus)) * (V ⊗ₜ[ℂ] (1 : M2C))
        = Complex.I • ((σPlus ⊗ₜ[ℂ] σMinus) * (V ⊗ₜ[ℂ] (1 : M2C))) :=
          Algebra.smul_mul_assoc _ _ _
      _ = Complex.I • ((-Complex.I • σPlus) ⊗ₜ[ℂ] σMinus) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp1]
      _ = (Complex.I * (-Complex.I)) • (σPlus ⊗ₜ[ℂ] σMinus) := by
          rw [← TensorProduct.smul_tmul', smul_smul]
      _ = σPlus ⊗ₜ[ℂ] σMinus := by
          have hii : Complex.I * (-Complex.I) = (1 : ℂ) := by
            rw [mul_neg, Complex.I_mul_I, neg_neg]
          rw [hii, one_smul]
  have r2 : (σMinus ⊗ₜ[ℂ] σPlus) * (V ⊗ₜ[ℂ] (1 : M2C)) = σMinus ⊗ₜ[ℂ] σPlus := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hm1]
  have r3 : (Complex.I • (PPlus ⊗ₜ[ℂ] PMinus)) * (V ⊗ₜ[ℂ] (1 : M2C)) =
      Complex.I • (PPlus ⊗ₜ[ℂ] PMinus) := by
    calc
      (Complex.I • (PPlus ⊗ₜ[ℂ] PMinus)) * (V ⊗ₜ[ℂ] (1 : M2C))
        = Complex.I • ((PPlus ⊗ₜ[ℂ] PMinus) * (V ⊗ₜ[ℂ] (1 : M2C))) :=
          Algebra.smul_mul_assoc _ _ _
      _ = Complex.I • (PPlus ⊗ₜ[ℂ] PMinus) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hpp1]
  have r4 : (PMinus ⊗ₜ[ℂ] PPlus) * (V ⊗ₜ[ℂ] (1 : M2C)) = (-Complex.I) • (PMinus ⊗ₜ[ℂ] PPlus) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hmp1, TensorProduct.smul_tmul']
  unfold zeroLoopRightTwist zeroLoopSpinPair X Y
  change _ * (V ⊗ₜ[ℂ] (1 : M2C)) = _
  rw [add_mul, add_mul, add_mul, r1, r2, r3, r4]
  module

theorem zeroLoopSpinPair_sq : zeroLoopSpinPair * zeroLoopSpinPair = 0 := by
  unfold zeroLoopSpinPair
  have hXX : X * X = 0 := X_mul_X
  have hYY : Y * Y = 0 := Y_mul_Y
  have hXY : X * Y = PPlus ⊗ₜ[ℂ] PMinus := by
    unfold X Y
    rw [Algebra.TensorProduct.tmul_mul_tmul, show σPlus * σMinus = PPlus from rfl,
      show σMinus * σPlus = PMinus from rfl]
  have hYX : Y * X = PMinus ⊗ₜ[ℂ] PPlus := by
    unfold X Y
    rw [Algebra.TensorProduct.tmul_mul_tmul, show σMinus * σPlus = PMinus from rfl,
      show σPlus * σMinus = PPlus from rfl]
  let D : SpinPair := PPlus ⊗ₜ[ℂ] PMinus - PMinus ⊗ₜ[ℂ] PPlus
  have hDD : D * D = PPlus ⊗ₜ[ℂ] PMinus + PMinus ⊗ₜ[ℂ] PPlus := by
    dsimp [D]
    rw [mul_sub, sub_mul, sub_mul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, PPlus_idempotent, PMinus_idempotent,
      PPlus_PMinus_orthogonal, PMinus_PPlus_orthogonal,
      TensorProduct.tmul_zero, sub_zero, zero_sub, sub_neg_eq_add]
  have hXD : X * D = -X := by
    dsimp [D, X]
    rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      σPlus_mul_PPlus_eq, σPlus_mul_PMinus_eq, σMinus_mul_PPlus_eq, σMinus_mul_PMinus_eq]
    simp
  have hDX : D * X = X := by
    dsimp [D, X]
    rw [sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      PPlus_mul_σPlus_eq, PMinus_mul_σPlus_eq, PPlus_mul_σMinus_eq, PMinus_mul_σMinus_eq]
    simp
  have hYD : Y * D = Y := by
    dsimp [D, Y]
    rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      σMinus_mul_PPlus_eq, σMinus_mul_PMinus_eq, σPlus_mul_PPlus_eq, σPlus_mul_PMinus_eq]
    simp
  have hDY : D * Y = -Y := by
    dsimp [D, Y]
    rw [sub_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      PPlus_mul_σMinus_eq, PMinus_mul_σMinus_eq, PPlus_mul_σPlus_eq, PMinus_mul_σPlus_eq]
    simp
  have hIDx : (Complex.I • D) * X = Complex.I • (D * X) := Algebra.smul_mul_assoc _ _ _
  have hxID : X * (Complex.I • D) = Complex.I • (X * D) := Algebra.mul_smul_comm _ _ _
  have hIDy : (Complex.I • D) * Y = Complex.I • (D * Y) := Algebra.smul_mul_assoc _ _ _
  have hyID : Y * (Complex.I • D) = Complex.I • (Y * D) := Algebra.mul_smul_comm _ _ _
  have hIDID : (Complex.I • D) * (Complex.I • D) = (Complex.I * Complex.I) • (D * D) := by
    calc
      (Complex.I • D) * (Complex.I • D)
        = Complex.I • (D * (Complex.I • D)) := Algebra.smul_mul_assoc _ _ _
      _ = Complex.I • (Complex.I • (D * D)) := by rw [Algebra.mul_smul_comm _ D D]
      _ = (Complex.I * Complex.I) • (D * D) := smul_smul _ _ _
  calc
    (X + Y + Complex.I • D) * (X + Y + Complex.I • D) =
        X * X + Y * Y + (X * Y + Y * X) +
          (X * (Complex.I • D) + (Complex.I • D) * X + Y * (Complex.I • D) + (Complex.I • D) * Y) +
          (Complex.I • D) * (Complex.I • D) := by
        simp only [add_mul, mul_add]
        abel
    _ = (PPlus ⊗ₜ[ℂ] PMinus + PMinus ⊗ₜ[ℂ] PPlus) +
          Complex.I • (-X + X + Y + -Y) +
          (-1 : ℂ) • (PPlus ⊗ₜ[ℂ] PMinus + PMinus ⊗ₜ[ℂ] PPlus) := by
        rw [hxID, hIDx, hyID, hIDy, hIDID, hXX, hYY, hXY, hYX, hXD, hDX, hYD, hDY, hDD,
          Complex.I_mul_I, ← smul_add, ← smul_add, ← smul_add]
        abel
    _ = 0 := by module

theorem sigma3_conj_e_eq_singletDouble :
    (σ3c ⊗ₜ[ℂ] (1 : M2C)) * e * (σ3c ⊗ₜ[ℂ] (1 : M2C)) = singletDoubleSpinPair := by
  have h3sq : σ3c * σ3c = 1 := σ3c_sq
  have h3p3 : σ3c * σPlus * σ3c = -σPlus := by
    rw [σ3c_mul_σPlus, σPlus_mul_σ3c]
  have h3m3 : σ3c * σMinus * σ3c = -σMinus := by
    rw [σ3c_mul_σMinus, neg_mul, σMinus_mul_σ3c]
  have hZ : (σ3c ⊗ₜ[ℂ] (1 : M2C)) * Z * (σ3c ⊗ₜ[ℂ] (1 : M2C)) = Z := by
    unfold Z
    have hpull : (σ3c ⊗ₜ[ℂ] (1 : M2C)) *
        ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) =
        (1/2 : ℂ) • ((σ3c ⊗ₜ[ℂ] (1 : M2C)) *
          ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) :=
      Algebra.mul_smul_comm _ _ _
    calc
      (σ3c ⊗ₜ[ℂ] (1 : M2C)) * ((1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) *
          (σ3c ⊗ₜ[ℂ] (1 : M2C))
        = ((1/2 : ℂ) • ((σ3c ⊗ₜ[ℂ] (1 : M2C)) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c))) *
            (σ3c ⊗ₜ[ℂ] (1 : M2C)) := congrArg (· * (σ3c ⊗ₜ[ℂ] (1 : M2C))) hpull
      _ = (1/2 : ℂ) • (((σ3c ⊗ₜ[ℂ] (1 : M2C)) * ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c)) *
            (σ3c ⊗ₜ[ℂ] (1 : M2C))) := Algebra.smul_mul_assoc _ _ _
      _ = (1/2 : ℂ) • ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C) - σ3c ⊗ₜ[ℂ] σ3c) := by
          congr 1
          simp only [mul_sub, sub_mul, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, mul_one, h3sq]
  unfold e singletDoubleSpinPair
  rw [mul_add, mul_add, add_mul, add_mul, hZ]
  have hX : (σ3c ⊗ₜ[ℂ] (1 : M2C)) * X * (σ3c ⊗ₜ[ℂ] (1 : M2C)) = -X := by
    unfold X
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, h3p3, TensorProduct.neg_tmul]
  have hY : (σ3c ⊗ₜ[ℂ] (1 : M2C)) * Y * (σ3c ⊗ₜ[ℂ] (1 : M2C)) = -Y := by
    unfold Y
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, h3m3, TensorProduct.neg_tmul]
  rw [hX, hY]
  abel

theorem singletProjSpinPair_idempotent :
    singletProjSpinPair * singletProjSpinPair = singletProjSpinPair := by
  have hsq : singletDoubleSpinPair * singletDoubleSpinPair = (2 : ℂ) • singletDoubleSpinPair := by
    rw [← sigma3_conj_e_eq_singletDouble]
    let S : SpinPair := σ3c ⊗ₜ[ℂ] (1 : M2C)
    have hS : S * S = 1 := by
      calc
        S * S = (σ3c * σ3c) ⊗ₜ[ℂ] ((1 : M2C) * (1 : M2C)) :=
          Algebra.TensorProduct.tmul_mul_tmul _ _ _ _
        _ = (1 : M2C) ⊗ₜ[ℂ] (1 : M2C) := by rw [σ3c_sq, mul_one]
        _ = 1 := spinPair_one_def
    have hpull : S * ((2 : ℂ) • e) = (2 : ℂ) • (S * e) := Algebra.mul_smul_comm _ _ _
    calc
      (S * e * S) * (S * e * S) = S * (e * (S * S) * e) * S := by simp only [mul_assoc]
      _ = S * (e * e) * S := by rw [hS, mul_one]
      _ = S * ((2 : ℂ) • e) * S := by rw [e_sq]
      _ = ((2 : ℂ) • (S * e)) * S := congrArg (· * S) hpull
      _ = (2 : ℂ) • (S * e * S) := Algebra.smul_mul_assoc _ _ _
  unfold singletProjSpinPair
  have hpull2 : singletDoubleSpinPair * ((1 / 2 : ℂ) • singletDoubleSpinPair) =
      (1 / 2 : ℂ) • (singletDoubleSpinPair * singletDoubleSpinPair) :=
    Algebra.mul_smul_comm _ _ _
  calc
    ((1 / 2 : ℂ) • singletDoubleSpinPair) * ((1 / 2 : ℂ) • singletDoubleSpinPair)
      = (1 / 2 : ℂ) • (singletDoubleSpinPair * ((1 / 2 : ℂ) • singletDoubleSpinPair)) :=
        Algebra.smul_mul_assoc _ _ _
    _ = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (singletDoubleSpinPair * singletDoubleSpinPair)) :=
        congrArg ((1 / 2 : ℂ) • ·) hpull2
    _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((2 : ℂ) • singletDoubleSpinPair) := by
        rw [hsq, smul_smul]
    _ = (1 / 2 : ℂ) • singletDoubleSpinPair := by
        rw [smul_smul]; norm_num

/-- Explicit noncommutativity witness for `sigmaPlusR` and `sigmaMinusR` over any nontrivial
commutative ring `R`. -/
theorem sigmaPlusR_sigmaMinusR_noncomm (R : Type*) [CommRing R] [Nontrivial R] :
    sigmaPlusR R * sigmaMinusR R ≠ sigmaMinusR R * sigmaPlusR R := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simp [sigmaPlusR, sigmaMinusR, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Existential noncommutativity witness for `Matrix (Fin 2) (Fin 2) R` over any nontrivial
commutative ring `R`. -/
theorem matrix2_R_noncomm_witness {R : Type*} [CommRing R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A := by
  refine ⟨sigmaPlusR R, sigmaMinusR R, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simp [sigmaPlusR, sigmaMinusR, Matrix.mul_apply, Fin.sum_univ_two] at h00

end SingletZeroLoopGaugeBridge

end ChiralTensorRecoupling
