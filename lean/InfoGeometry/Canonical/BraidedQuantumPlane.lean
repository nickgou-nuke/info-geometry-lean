import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

open scoped TensorProduct

namespace InfoGeometry.Canonical.BraidedQuantumPlane

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

def delta_d (d K : A) : A ⊗[R] A :=
  d ⊗ₜ 1 + K ⊗ₜ d

def delta_K (K : A) : A ⊗[R] A :=
  K ⊗ₜ K

def delta_one : A ⊗[R] A :=
  1 ⊗ₜ 1

theorem delta_d_coassociative (d K : A) :
    (TensorProduct.assoc R A A A) ((delta_d d K) ⊗ₜ (1 : A) + (delta_K K) ⊗ₜ d) =
      d ⊗ₜ (delta_one : A ⊗[R] A) + K ⊗ₜ (delta_d d K) := by
  dsimp [delta_d, delta_K, delta_one]
  rw [TensorProduct.add_tmul]
  simp only [map_add, TensorProduct.assoc_tmul, TensorProduct.tmul_add]
  abel

theorem delta_K_coassociative (K : A) :
    (TensorProduct.assoc R A A A) ((delta_K K) ⊗ₜ K) = K ⊗ₜ (delta_K K) := by
  exact TensorProduct.assoc_tmul K K K

theorem counit_d_left (d K : A) (ε : A →ₗ[R] R) (hε_d : ε d = 0) (hε_K : ε K = 1) :
    (TensorProduct.lid R A) (TensorProduct.map ε LinearMap.id (delta_d d K)) = d := by
  dsimp [delta_d]
  simp [hε_d, hε_K]

theorem counit_d_right (d K : A) (ε : A →ₗ[R] R) (hε_d : ε d = 0) (hε_one : ε 1 = 1) :
    (TensorProduct.rid R A) (TensorProduct.map LinearMap.id ε (delta_d d K)) = d := by
  dsimp [delta_d]
  simp [hε_d, hε_one]

theorem counit_K_left (K : A) (ε : A →ₗ[R] R) (hε_K : ε K = 1) :
    (TensorProduct.lid R A) (TensorProduct.map ε LinearMap.id (delta_K K)) = K := by
  dsimp [delta_K]
  simp [hε_K]

theorem counit_K_right (K : A) (ε : A →ₗ[R] R) (hε_K : ε K = 1) :
    (TensorProduct.rid R A) (TensorProduct.map LinearMap.id ε (delta_K K)) = K := by
  dsimp [delta_K]
  simp [hε_K]

theorem antipode_d_left (d K_inv : A) :
    (LinearMap.mul' R A) ((- (K_inv * d)) ⊗ₜ (1 : A) + K_inv ⊗ₜ d) = 0 := by
  simp [LinearMap.mul'_apply]

theorem antipode_d_right (d K K_inv : A) (hK_inv : K * K_inv = 1) :
    (LinearMap.mul' R A) (d ⊗ₜ (1 : A) + K ⊗ₜ (- (K_inv * d))) = 0 := by
  simp [LinearMap.mul'_apply]
  rw [← mul_assoc, hK_inv, one_mul]
  exact add_neg_cancel d

def braidedCoprodOp (d K : A →ₗ[R] A) : (A ⊗[R] A) →ₗ[R] (A ⊗[R] A) :=
  TensorProduct.map d LinearMap.id + TensorProduct.map K d

theorem braided_coproduct_eval (d K : A →ₗ[R] A) (a b : A) :
    (LinearMap.mul' R A) (braidedCoprodOp d K (a ⊗ₜ b)) = d a * b + K a * d b := by
  dsimp [braidedCoprodOp]
  simp [LinearMap.mul'_apply]

theorem braided_coproduct_eval_q (d K : A →ₗ[R] A) (q : R) (a b : A)
    (hK : K a = q • a) :
    (LinearMap.mul' R A) (braidedCoprodOp d K (a ⊗ₜ b)) = d a * b + q • (a * d b) := by
  rw [braided_coproduct_eval]
  rw [hK, Algebra.smul_mul_assoc]

theorem braided_coproduct_pow_two (d K : A →ₗ[R] A) (q : R) (x : A)
    (hx : d x = 1) (hK : K x = q • x) :
    (LinearMap.mul' R A) (braidedCoprodOp d K (x ⊗ₜ x)) = (1 + q) • x := by
  rw [braided_coproduct_eval_q d K q x x hK]
  rw [hx, one_mul, mul_one]
  calc
    x + q • x = (1 : R) • x + q • x := by rw [one_smul]
    _ = (1 + q) • x := by rw [← add_smul]

end InfoGeometry.Canonical.BraidedQuantumPlane
