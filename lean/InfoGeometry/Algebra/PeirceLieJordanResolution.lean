/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Algebra.IdempotentProjector
import InfoGeometry.OperatorAlgebra.LieJordanDualTransport

/-!
# Peirce corners as joint Lie--Jordan readouts

The four unbundled corners are those of `IdempotentProjector`. The indexed
linear maps below package their projection and multiplication tables. All
identities are division-free; doubled formulas do not assert invertibility of
two. Orthogonality here is algebraic annihilation of projections, not positivity.
-/

namespace InfoGeometry.Algebra.PeirceLieJordanResolution

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanDualTransport

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The two existing complementary endpoints, indexed without a basis choice. -/
def endpoint (p : A) (i : Bool) : A := if i then p else compIdempotent p

/-- The four corners as native linear endomorphisms. -/
def cornerOp (p : A) (i j : Bool) : Module.End R A where
  toFun x := endpoint p i * x * endpoint p j
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' r x := by
    simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

@[simp] theorem corner11_apply (p x : A) :
    cornerOp (R := R) p true true x = peirce11 p x := rfl

@[simp] theorem corner00_apply (p x : A) :
    cornerOp (R := R) p false false x = peirce00 p x := rfl

@[simp] theorem corner10_apply (p x : A) :
    cornerOp (R := R) p true false x = peirce10 p x := rfl

@[simp] theorem corner01_apply (p x : A) :
    cornerOp (R := R) p false true x = peirce01 p x := rfl

theorem endpoint_mul {p : A} (hp : p * p = p) (i j : Bool) :
    endpoint p i * endpoint p j = if i = j then endpoint p i else 0 := by
  cases i <;> cases j <;>
    simp [endpoint, compIdempotent, mul_sub, sub_mul, hp]

/-- The full sixteen-cell composition table of the four projection operators. -/
theorem cornerOp_comp {p : A} (hp : p * p = p) (i j k l : Bool) :
    cornerOp (R := R) p i j * cornerOp p k l =
      if i = k ∧ j = l then cornerOp p i j else 0 := by
  ext x
  change endpoint p i * (endpoint p k * x * endpoint p l) * endpoint p j = _
  calc
    _ = (endpoint p i * endpoint p k) * x *
          (endpoint p l * endpoint p j) := by simp only [mul_assoc]
    _ = _ := by
      rw [endpoint_mul hp, endpoint_mul hp]
      by_cases hik : i = k <;> by_cases hjl : j = l <;>
        simp_all [cornerOp, mul_assoc]

/-- The full sixteen-cell product rule; no elements from distinct corners are
silently commuted. Compatible products retain the intermediate endpoint. -/
theorem cornerOp_product {p : A} (hp : p * p = p)
    (i j k l : Bool) (x y : A) :
    cornerOp (R := R) p i j x * cornerOp p k l y =
      if j = k then endpoint p i * x * endpoint p j * y * endpoint p l else 0 := by
  change (endpoint p i * x * endpoint p j) *
    (endpoint p k * y * endpoint p l) = _
  calc
    _ = (endpoint p i * x) * (endpoint p j * endpoint p k) *
          (y * endpoint p l) := by simp only [mul_assoc]
    _ = _ := by
      rw [endpoint_mul hp]
      by_cases hjk : j = k <;> simp [hjk, mul_assoc]

theorem cornerOp_resolution (p : A) :
    cornerOp (R := R) p true true + cornerOp p true false +
      cornerOp p false true + cornerOp p false false = 1 := by
  ext x
  exact peirce_decomposition_sum p x

/-- The idempotent double commutator, with its exact sandwich term. -/
theorem ad_square_apply {p : A} (hp : p * p = p) (x : A) :
    LieAlgebra.ad R A p (LieAlgebra.ad R A p x) =
      p * x + x * p - 2 • (p * x * p) := by
  change p * (p * x - x * p) - (p * x - x * p) * p = _
  rw [mul_sub, sub_mul, ← mul_assoc p p x, mul_assoc x p p]
  simp only [hp]
  simp only [two_nsmul]
  noncomm_ring

theorem twice_peirce11 {p : A} (hp : p * p = p) (x : A) :
    2 • peirce11 p x = jordanLeft (R := R) p x -
      LieAlgebra.ad R A p (LieAlgebra.ad R A p x) := by
  rw [ad_square_apply hp]
  change 2 • (p * x * p) = (p * x + x * p) - _
  simp only [two_nsmul]
  abel

theorem twice_peirce00 {p : A} (hp : p * p = p) (x : A) :
    2 • peirce00 p x = 2 • x - jordanLeft (R := R) p x -
      LieAlgebra.ad R A p (LieAlgebra.ad R A p x) := by
  rw [ad_square_apply hp]
  change 2 • ((1 - p) * x * (1 - p)) = 2 • x - (p * x + x * p) -
    (p * x + x * p - 2 • (p * x * p))
  simp only [two_nsmul]
  noncomm_ring

theorem twice_peirce10 {p : A} (hp : p * p = p) (x : A) :
    2 • peirce10 p x =
      LieAlgebra.ad R A p (LieAlgebra.ad R A p x) + LieAlgebra.ad R A p x := by
  rw [ad_square_apply hp]
  change 2 • (p * x * (1 - p)) = (p * x + x * p - 2 • (p * x * p)) +
    (p * x - x * p)
  simp only [two_nsmul]
  noncomm_ring

theorem twice_peirce01 {p : A} (hp : p * p = p) (x : A) :
    2 • peirce01 p x =
      LieAlgebra.ad R A p (LieAlgebra.ad R A p x) - LieAlgebra.ad R A p x := by
  rw [ad_square_apply hp]
  change 2 • ((1 - p) * x * p) = (p * x + x * p - 2 • (p * x * p)) -
    (p * x - x * p)
  simp only [two_nsmul]
  noncomm_ring

/-- The Jordan operator is the identity on the image of the idempotent adjoint. -/
theorem jordan_ad_apply {p : A} (hp : p * p = p) (x : A) :
    jordanLeft (R := R) p (LieAlgebra.ad R A p x) = LieAlgebra.ad R A p x := by
  change p * (p * x - x * p) + (p * x - x * p) * p = p * x - x * p
  rw [mul_sub, sub_mul, ← mul_assoc p p x, mul_assoc x p p]
  simp only [hp]
  noncomm_ring

theorem plus_ad_eq_twice_peirce10 {p : A} (hp : p * p = p) (x : A) :
    plus (R := R) p p (LieAlgebra.ad R A p x) = 2 • peirce10 p x := by
  change LieAlgebra.ad R A p (LieAlgebra.ad R A p x) +
    jordanLeft (R := R) p (LieAlgebra.ad R A p x) = _
  rw [jordan_ad_apply hp]
  exact (twice_peirce10 hp x).symm

/-- There is no additional minus sign on this lower-corner formula. -/
theorem minus_ad_eq_twice_peirce01 {p : A} (hp : p * p = p) (x : A) :
    minus (R := R) p p (LieAlgebra.ad R A p x) = 2 • peirce01 p x := by
  change LieAlgebra.ad R A p (LieAlgebra.ad R A p x) -
    jordanLeft (R := R) p (LieAlgebra.ad R A p x) = _
  rw [jordan_ad_apply hp]
  exact (twice_peirce01 hp x).symm

end InfoGeometry.Algebra.PeirceLieJordanResolution
