import Mathlib
import InfoGeometry.Physics.ChiralCausalCone
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
    simpa [Algebra.TensorProduct.tmul_mul_tmul] using projector_tensor_identity
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
    simpa [Algebra.TensorProduct.tmul_mul_tmul] using projector_tensor_identity

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

open InfoGeometry.Physics.CPTAtom

/-- The TL generator `e` factors through the complexified Cl(1,1) atom.
Expressed in terms of `eps_c = complexifyCl11 eps`, `J_c = complexifyCl11 J`,
`CPT_c = complexifyCl11 CPT`:
  `e = ½(eps_c⊗eps_c - J_c⊗J_c + I⊗I - CPT_c⊗CPT_c)`

This theorem routes the GEPA edge from `ChiralTensorRecoupling.e` to
`ChiralCausalCone.cl11_atom_to_chiral_CAR_basis`, closing the loop
from the real Clifford root to the chiral τ-ideal stability spine. -/
theorem e_factors_through_cl11_atom :
    e = (1/2 : ℂ) • (
      ((complexifyCl11 InfoGeometry.Physics.CPTAtom.eps) ⊗ₜ[ℂ] (complexifyCl11 InfoGeometry.Physics.CPTAtom.eps)) -
      ((complexifyCl11 InfoGeometry.Physics.CPTAtom.J) ⊗ₜ[ℂ] (complexifyCl11 InfoGeometry.Physics.CPTAtom.J)) +
      ((1 : M2C) ⊗ₜ[ℂ] (1 : M2C)) -
      ((complexifyCl11 InfoGeometry.Physics.CPTAtom.CPT) ⊗ₜ[ℂ] (complexifyCl11 InfoGeometry.Physics.CPTAtom.CPT))
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
  simp [TensorProduct.smul_tmul_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, smul_add, add_smul, smul_sub, sub_smul]
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

end ChiralTensorRecoupling
