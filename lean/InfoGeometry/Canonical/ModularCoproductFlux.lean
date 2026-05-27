import Mathlib

/-!
# InfoGeometry.Canonical.ModularCoproductFlux

Concrete coproduct-flux algebra for a nilpotent generator `N`:

* `(N ⊗ N)^2 = 0`
* `C^2 = 2 • (N ⊗ N)` for `C = N ⊗ 1 + 1 ⊗ N + N ⊗ N`
* `C^3 = 0`
-/

namespace InfoGeometry.Canonical.ModularCoproductFlux

open scoped TensorProduct

section

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

def liftFlux (N : A) : A ⊗[R] A :=
  (N ⊗ₜ[R] (1 : A)) + ((1 : A) ⊗ₜ[R] N) + (N ⊗ₜ[R] N)

theorem tensor_nilpotent_sq_zero
    (N : A) (hN : N * N = 0) :
    ((N ⊗ₜ[R] N : A ⊗[R] A) * (N ⊗ₜ[R] N)) = 0 := by
  simp [Algebra.TensorProduct.tmul_mul_tmul, hN]

theorem liftFlux_sq
    (N : A) (hN : N * N = 0) :
    liftFlux (R := R) N * liftFlux (R := R) N =
      (2 : R) • (N ⊗ₜ[R] N : A ⊗[R] A) := by
  let a : A ⊗[R] A := N ⊗ₜ[R] (1 : A)
  let b : A ⊗[R] A := (1 : A) ⊗ₜ[R] N
  let c : A ⊗[R] A := N ⊗ₜ[R] N
  have ha2 : a * a = 0 := by
    simp [a, Algebra.TensorProduct.tmul_mul_tmul, hN]
  have hb2 : b * b = 0 := by
    simp [b, Algebra.TensorProduct.tmul_mul_tmul, hN]
  have hc2 : c * c = 0 := by
    simp [c, Algebra.TensorProduct.tmul_mul_tmul, hN]
  have hab : a * b = c := by
    simp [a, b, c, Algebra.TensorProduct.tmul_mul_tmul]
  have hba : b * a = c := by
    simp [a, b, c, Algebra.TensorProduct.tmul_mul_tmul]
  have hac : a * c = 0 := by
    simp [a, c, Algebra.TensorProduct.tmul_mul_tmul, hN]
  have hca : c * a = 0 := by
    simp [a, c, Algebra.TensorProduct.tmul_mul_tmul, hN]
  have hbc : b * c = 0 := by
    simp [b, c, Algebra.TensorProduct.tmul_mul_tmul, hN]
  have hcb : c * b = 0 := by
    simp [b, c, Algebra.TensorProduct.tmul_mul_tmul, hN]
  calc
    liftFlux (R := R) N * liftFlux (R := R) N
        = (a + b + c) * (a + b + c) := by rfl
    _ = a * a + a * b + a * c + (b * a + b * b + b * c) + (c * a + c * b + c * c) := by
          noncomm_ring
    _ = c + c := by
          simp [ha2, hb2, hc2, hab, hba, hac, hca, hbc, hcb]
    _ = (2 : R) • (N ⊗ₜ[R] N : A ⊗[R] A) := by
          simp [two_smul, c]

theorem liftFlux_cube_zero
    (N : A) (hN : N * N = 0) :
    liftFlux (R := R) N * liftFlux (R := R) N * liftFlux (R := R) N = 0 := by
  have hsquare :
      liftFlux (R := R) N * liftFlux (R := R) N =
        (2 : R) • (N ⊗ₜ[R] N : A ⊗[R] A) := liftFlux_sq (R := R) N hN
  rw [hsquare]
  have hright :
      (N ⊗ₜ[R] N : A ⊗[R] A) * liftFlux (R := R) N = 0 := by
    calc
      (N ⊗ₜ[R] N : A ⊗[R] A) * liftFlux (R := R) N
          = (N ⊗ₜ[R] N : A ⊗[R] A) * (N ⊗ₜ[R] (1 : A))
            + (N ⊗ₜ[R] N : A ⊗[R] A) * ((1 : A) ⊗ₜ[R] N)
            + (N ⊗ₜ[R] N : A ⊗[R] A) * (N ⊗ₜ[R] N) := by
              simp [liftFlux, mul_add, add_assoc]
      _ = 0 + 0 + 0 := by
            simp [Algebra.TensorProduct.tmul_mul_tmul, hN]
      _ = 0 := by simp
  calc
    (2 : R) • (N ⊗ₜ[R] N : A ⊗[R] A) * liftFlux (R := R) N
        = (2 : R) • ((N ⊗ₜ[R] N : A ⊗[R] A) * liftFlux (R := R) N) := by
          simp
    _ = 0 := by simp [hright]

end

end InfoGeometry.Canonical.ModularCoproductFlux
