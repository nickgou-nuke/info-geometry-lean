/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Archetypes of Supergeometry: Graded Grassmann Algebras in Lean 4

This module formalizes the five foundational archetypes of supergeometry and
graded exterior (Grassmann) algebras over an arbitrary commutative ring `R`
and `R`-module `M`:

1. **Archetype I (`ℤ₂`-Grading Parity)**:
   `Parity := ZMod 2` with `bosonic : Parity := 0` and `fermionic : Parity := 1`.
2. **Archetype II (Koszul Sign Rule)**:
   `koszulSign p q = (-1 : R) ^ (p * q)` with left/right degree-0 identities,
   symmetry `koszulSign p q = koszulSign q p`, and additive multiplicativity
   `koszulSign (p₁ + p₂) q = koszulSign p₁ q * koszulSign p₂ q`.
3. **Archetype III (Exterior Power Universal Property & Generator Anticommutation)**:
   Degree-1 exterior generators `ι R v` satisfy `ι R v * ι R w + ι R w * ι R v = 0`,
   `ι R v * ι R w = - (ι R w * ι R v)`, and strict fermionic nilpotency `(ι R v) ^ 2 = 0`.
4. **Archetype IV (Graded Supercommutativity of the Wedge Product)**:
   * `ι_mul_graded_comm`: For any `v : M` and homogeneous degree-`q` element
     `y ∈ LinearMap.range (ι R) ^ q`, `ι R v * y = (-1 : R) ^ q • (y * ι R v)`.
   * `supercommutative_exterior`: For homogeneous elements `x ∈ LinearMap.range (ι R) ^ p`
     and `y ∈ LinearMap.range (ι R) ^ q`,
     `x * y = koszulSign p q • (y * x)`.
5. **Archetype V (Super-Grassmannian Invariants & Super-Commutator)**:
   `superCommutator p q x y = x * y - koszulSign p q • (y * x)` vanishes identically
   on pure homogeneous components of degrees `p` and `q`.
-/

namespace InfoGeometry.Superalgebra.SuperGrassmann

open ExteriorAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Archetype I & II: Parity, Grading, and the Koszul Sign Rule -/

/-- Parity grading over `ℤ₂ = ZMod 2`. -/
abbrev Parity := ZMod 2

/-- Bosonic (even) parity (`0 : ZMod 2`). -/
def bosonic : Parity := 0

/-- Fermionic (odd) parity (`1 : ZMod 2`). -/
def fermionic : Parity := 1

/-- Non-degeneracy of `ℤ₂` super-grading: bosonic and fermionic parities are distinct. -/
theorem bosonic_ne_fermionic : bosonic ≠ fermionic := by
  decide

/-- Koszul sign factor `(-1)^(p * q)` computed in the base ring `R`. -/
def koszulSign (p q : ℕ) : R :=
  (-1 : R) ^ (p * q)

@[simp]
theorem koszulSign_zero_left (q : ℕ) : koszulSign (R := R) 0 q = 1 := by
  dsimp [koszulSign]
  rw [Nat.zero_mul, pow_zero]

@[simp]
theorem koszulSign_zero_right (p : ℕ) : koszulSign (R := R) p 0 = 1 := by
  dsimp [koszulSign]
  rw [pow_zero]

theorem koszulSign_symm (p q : ℕ) :
    koszulSign (R := R) p q = koszulSign (R := R) q p := by
  dsimp [koszulSign]
  rw [Nat.mul_comm]

theorem koszulSign_mul (p₁ p₂ q : ℕ) :
    koszulSign (R := R) (p₁ + p₂) q =
      koszulSign (R := R) p₁ q * koszulSign (R := R) p₂ q := by
  dsimp [koszulSign]
  rw [Nat.add_mul, pow_add]

theorem koszulSign_one_left (q : ℕ) :
    koszulSign (R := R) 1 q = (-1 : R) ^ q := by
  dsimp [koszulSign]
  rw [Nat.one_mul]

theorem koszulSign_one_one :
    koszulSign (R := R) 1 1 = -1 := by
  dsimp [koszulSign]
  ring

/-! ### Archetype III & IV: Graded Commutativity of Exterior Products -/

/-- For degree-1 generators, `ι R v * ι R w + ι R w * ι R v = 0`. -/
theorem ι_mul_ι_anticomm (v w : M) :
    ι R v * ι R w + ι R w * ι R v = 0 := by
  have h1 : ι R (v + w) * ι R (v + w) = 0 := ι_sq_zero (v + w)
  have h2 : ι R v * ι R v = 0 := ι_sq_zero v
  have h3 : ι R w * ι R w = 0 := ι_sq_zero w
  rw [map_add, mul_add, add_mul, add_mul, h2, h3, zero_add, add_zero, add_comm] at h1
  exact h1

/-- Fermionic generator anticommutation: `ι R v * ι R w = - (ι R w * ι R v)`. -/
theorem ι_mul_ι_swap (v w : M) :
    ι R v * ι R w = - (ι R w * ι R v) := by
  rw [← add_eq_zero_iff_eq_neg]
  exact ι_mul_ι_anticomm v w

/-- Odd elements (fermions) are strictly nilpotent in the exterior Grassmann algebra:
    `(ι R v) ^ 2 = 0`. -/
theorem fermionic_nilpotent (v : M) :
    (ι R v) ^ 2 = 0 := by
  rw [pow_two]
  exact ι_sq_zero v

/-- Inductive proof that a pure 1-form `ι R v` graded-commutes with an arbitrary
    degree-`q` homogeneous element `y ∈ LinearMap.range (ι R) ^ q`:
    `ι R v * y = (-1 : R) ^ q • (y * ι R v)`. -/
theorem ι_mul_graded_comm (v : M) (q : ℕ) (y : ExteriorAlgebra R M)
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q) :
    ι R v * y = (-1 : R) ^ q • (y * ι R v) := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [pow_zero, one_smul, ← Algebra.commutes]
  | add x₁ x₂ i _ _ ih₁ ih₂ =>
    rw [mul_add, ih₁, ih₂, add_mul, smul_add]
  | mem_mul m hm i x _ ih =>
    rcases hm with ⟨w, rfl⟩
    calc
      ι R v * (ι R w * x)
        = (ι R v * ι R w) * x := (mul_assoc _ _ _).symm
      _ = (- (ι R w * ι R v)) * x := by rw [ι_mul_ι_swap v w]
      _ = - (ι R w * (ι R v * x)) := by rw [neg_mul, mul_assoc]
      _ = - (ι R w * ((-1 : R) ^ i • (x * ι R v))) := by rw [ih]
      _ = - ((-1 : R) ^ i • (ι R w * (x * ι R v))) := by rw [mul_smul_comm]
      _ = ((-1 : R) ^ i * (-1 : R)) • ((ι R w * x) * ι R v) := by
        rw [← mul_assoc (ι R w) x (ι R v), ← neg_smul, mul_neg_one]
      _ = (-1 : R) ^ i.succ • ((ι R w * x) * ι R v) := by
        rw [pow_succ]

/-- Canonical Supercommutativity of the Exterior Algebra:
    Homogeneous elements `x` of degree `p` and `y` of degree `q` satisfy
    `x * y = koszulSign (R := R) p q • (y * x) = (-1)^(p * q) • (y * x)`. -/
theorem supercommutative_exterior (p q : ℕ)
    (x y : ExteriorAlgebra R M)
    (hx : x ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ p)
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q) :
    x * y = koszulSign (R := R) p q • (y * x) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [koszulSign_zero_left, one_smul, Algebra.commutes]
  | add x₁ x₂ i _ _ ih₁ ih₂ =>
    rw [add_mul, ih₁, ih₂, mul_add, smul_add]
  | mem_mul m hm i x' _ ih =>
    rcases hm with ⟨v, rfl⟩
    have h_v : ι R v * y = (-1 : R) ^ q • (y * ι R v) :=
      ι_mul_graded_comm v q y hy
    calc
      (ι R v * x') * y
        = ι R v * (x' * y) := mul_assoc _ _ _
      _ = ι R v * (koszulSign (R := R) i q • (y * x')) := by rw [ih]
      _ = koszulSign (R := R) i q • ((ι R v * y) * x') := by
        rw [mul_smul_comm, mul_assoc]
      _ = koszulSign (R := R) i q • (((-1 : R) ^ q • (y * ι R v)) * x') := by
        rw [h_v]
      _ = (koszulSign (R := R) i q * (-1 : R) ^ q) • (y * (ι R v * x')) := by
        rw [smul_mul_assoc, smul_smul, mul_assoc]
      _ = koszulSign (R := R) i.succ q • (y * (ι R v * x')) := by
        dsimp [koszulSign]
        rw [Nat.succ_mul, pow_add]

/-! ### Archetype V: Super-Grassmannian Invariants & Subspaces -/

/-- The graded super-commutator `[x, y]_s = x * y - (-1)^(p * q) • (y * x)`. -/
def superCommutator (p q : ℕ) (x y : ExteriorAlgebra R M) : ExteriorAlgebra R M :=
  x * y - koszulSign (R := R) p q • (y * x)

/-- The super-commutator vanishes identically on pure homogeneous components
    `x ∈ LinearMap.range (ι R) ^ p` and `y ∈ LinearMap.range (ι R) ^ q`. -/
theorem superCommutator_vanishes (p q : ℕ)
    (x y : ExteriorAlgebra R M)
    (hx : x ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ p)
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q) :
    superCommutator (R := R) p q x y = 0 := by
  dsimp [superCommutator]
  rw [supercommutative_exterior p q x y hx hy, sub_self]

/-- Specialization to degree `(1, 1)`: for any `v, w : M`, the odd super-commutator
    `superCommutator (R := R) 1 1 (ι R v) (ι R w)` equals the anticommutator
    `ι R v * ι R w + ι R w * ι R v` and vanishes identically. -/
theorem superCommutator_one_one_eq_anticomm (v w : M) :
    superCommutator (R := R) 1 1 (ι R v) (ι R w) = ι R v * ι R w + ι R w * ι R v ∧
    superCommutator (R := R) 1 1 (ι R v) (ι R w) = 0 := by
  constructor
  · dsimp [superCommutator]
    rw [koszulSign_one_one, neg_one_smul, sub_neg_eq_add]
  · exact superCommutator_vanishes 1 1 (ι R v) (ι R w)
      (by simpa only [pow_one] using LinearMap.mem_range_self _ v)
      (by simpa only [pow_one] using LinearMap.mem_range_self _ w)

/-- **Degree-2 Bosonic Centrality**:
    Every degree-2 bivector `x ∈ LinearMap.range (ι R) ^ 2` commutes with any homogeneous
    element `y` of arbitrary degree `q`: `x * y = y * x`. -/
theorem bivector_central (q : ℕ) (x y : ExteriorAlgebra R M)
    (hx : x ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ 2)
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q) :
    x * y = y * x := by
  rw [supercommutative_exterior 2 q x y hx hy]
  dsimp [koszulSign]
  rw [pow_mul, neg_one_sq, one_pow, one_smul]

end InfoGeometry.Superalgebra.SuperGrassmann

namespace SuperGrassmann

export InfoGeometry.Superalgebra.SuperGrassmann (
  Parity bosonic fermionic bosonic_ne_fermionic
  koszulSign koszulSign_zero_left koszulSign_zero_right koszulSign_symm koszulSign_mul
  koszulSign_one_left koszulSign_one_one
  ι_mul_ι_anticomm ι_mul_ι_swap fermionic_nilpotent
  ι_mul_graded_comm supercommutative_exterior
  superCommutator superCommutator_vanishes superCommutator_one_one_eq_anticomm
  bivector_central
)

end SuperGrassmann

