import Mathlib

/-!
# InfoGeometry.Canonical.ModularCoproductFlux

Concrete coproduct-flux algebra for a nilpotent generator `N`:

* `(1 + N) ⊗ (1 + N) - 1 ⊗ 1 = N ⊗ 1 + 1 ⊗ N + N ⊗ N`
* `(N ⊗ N)^2 = 0`
* a linearized/primitive readout is valid only when the readout kills `N ⊗ N`
* `C^2 = 2 • (N ⊗ N)` for `C = N ⊗ 1 + 1 ⊗ N + N ⊗ N`
* `C^3 = 0`

No current-algebra central-charge claim.
No infinite-factor theorem.
No infinite-limit claim.
-/

namespace ModularCoproductFlux

open scoped TensorProduct

section

variable {R A : Type*}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Primitive, linearized flux part `N ⊗ 1 + 1 ⊗ N`. -/
def primitiveFlux (N : A) : A ⊗[R] A :=
  (N ⊗ₜ[R] (1 : A)) + ((1 : A) ⊗ₜ[R] N)

/-- Cross-flux part `N ⊗ N`. -/
def crossFlux (N : A) : A ⊗[R] A :=
  N ⊗ₜ[R] N

/-- Exact group-like centered flux part. -/
def liftFlux (N : A) : A ⊗[R] A :=
  primitiveFlux (R := R) N + crossFlux (R := R) N

/--
Exact group-like coproduct flux decomposition.

Writing `Δ = 1 + N`, the centered tensor product is

`Δ ⊗ Δ - 1 ⊗ 1 = N ⊗ 1 + 1 ⊗ N + N ⊗ N`.
-/
theorem one_add_tmul_one_add_sub_one_eq_liftFlux
    (N : A) :
    ((1 + N) ⊗ₜ[R] (1 + N) : A ⊗[R] A) -
        ((1 : A) ⊗ₜ[R] (1 : A)) =
      liftFlux (R := R) N := by
  simp [liftFlux, primitiveFlux, crossFlux, TensorProduct.add_tmul,
    TensorProduct.tmul_add, add_assoc, add_comm, add_left_comm]
  abel

/--
The exact flux splits as primitive part plus cross-flux.

This is a definitional readback, included to keep the primitive law separate
from the exact group-like law.
-/
theorem liftFlux_eq_primitive_add_cross (N : A) :
    liftFlux (R := R) N = primitiveFlux (R := R) N + crossFlux (R := R) N := by
  rfl

/--
Linearized/vacuum primitive readout under an explicit cross-annihilation
hypothesis.

The primitive formula is not the exact coproduct formula; it is what a linear
readout sees when it kills the cross term `N ⊗ N`.
-/
theorem readout_liftFlux_eq_readout_primitive_of_cross_zero
    {M : Type*} [AddCommGroup M] [Module R M]
    (readout : (A ⊗[R] A) →ₗ[R] M)
    (N : A)
    (hcross : readout (crossFlux (R := R) N) = 0) :
    readout (liftFlux (R := R) N) = readout (primitiveFlux (R := R) N) := by
  simp [liftFlux, hcross]

/--
If the cross-flux term itself vanishes, the exact group-like flux reduces to
the primitive flux.

This is still a finite algebraic statement: the primitive law is obtained only
under the explicit hypothesis `N ⊗ N = 0`.
-/
theorem liftFlux_eq_primitive_of_cross_zero
    (N : A)
    (hcross : crossFlux (R := R) N = 0) :
    liftFlux (R := R) N = primitiveFlux (R := R) N := by
  simp [liftFlux, hcross]

/--
Under cross-flux annihilation, the centered group-like tensor product reduces
to the primitive expression.
-/
theorem one_add_tmul_one_add_sub_one_eq_primitive_of_cross_zero
    (N : A)
    (hcross : crossFlux (R := R) N = 0) :
    ((1 + N) ⊗ₜ[R] (1 + N) : A ⊗[R] A) -
        ((1 : A) ⊗ₜ[R] (1 : A)) =
      primitiveFlux (R := R) N := by
  rw [one_add_tmul_one_add_sub_one_eq_liftFlux]
  exact liftFlux_eq_primitive_of_cross_zero (R := R) N hcross

theorem tensor_nilpotent_sq_zero
    (N : A) (hN : N * N = 0) :
    crossFlux (R := R) N * crossFlux (R := R) N = 0 := by
  simp [crossFlux, Algebra.TensorProduct.tmul_mul_tmul, hN]

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
              simp [liftFlux, primitiveFlux, crossFlux, mul_add, add_assoc]
      _ = 0 + 0 + 0 := by
            simp [Algebra.TensorProduct.tmul_mul_tmul, hN]
      _ = 0 := by simp
  calc
    (2 : R) • (N ⊗ₜ[R] N : A ⊗[R] A) * liftFlux (R := R) N
        = (2 : R) • ((N ⊗ₜ[R] N : A ⊗[R] A) * liftFlux (R := R) N) := by
          simp
    _ = 0 := by simp [hright]

end

end ModularCoproductFlux
