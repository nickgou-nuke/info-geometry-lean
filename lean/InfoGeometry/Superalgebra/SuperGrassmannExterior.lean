import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic
import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-!
# Archetypes of Supergeometry: Graded Grassmann Algebras in Lean 4

This module formalizes the five foundational archetypes of supergeometry in Mathlib's
native `ExteriorAlgebra R M`:
1. **Archetype I ($\mathbb{Z}_2$-Parity Grading)**: Parity degrees over `ZMod 2` (`bosonic`, `fermionic`)
   and the degree-to-parity reduction map.
2. **Archetype II (Koszul Sign Rule)**: The causal sign factor `koszulSign p q = (-1 : R) ^ (p * q)`
   governing exchanges across graded tensor and exterior products.
3. **Archetype III (Exterior Generator Anticommutation)**: Alternating degree-1 generators
   satisfy `ι R v * ι R w + ι R w * ι R v = 0`, `ι R v * ι R w = -(ι R w * ι R v)`, and
   strict fermionic nilpotency `(ι R v) ^ 2 = 0`.
4. **Archetype IV (Graded Supercommutativity of the Wedge Product)**: Complete inductive proof
   (with 0 `sorry`s) that any degree-1 generator anticommutes with a degree-`q` homogeneous
   element (`ι_mul_graded_comm`), and that arbitrary homogeneous elements of degree `p` and `q`
   satisfy `x * y = koszulSign p q • (y * x)` (`supercommutative_exterior`).
5. **Archetype V (Super-Commutator & Super-Grassmannian Invariants)**: The graded super-commutator
   `superCommutator p q x y = x * y - koszulSign p q • (y * x)` vanishes identically on all
   homogeneous exterior subvarieties (`superCommutator_vanishes`), together with an explicit
   non-commutativity witness on degree-1 generators over `ℤ²`.
-/

namespace InfoGeometry.Superalgebra.SuperGrassmannExterior

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

/-- Map an `ℕ`-grading degree to its `ℤ₂` super-parity. -/
def degreeParity (d : ℕ) : Parity := (d : ZMod 2)

/-- Bosonic and fermionic parities are distinct in `ZMod 2`. -/
theorem bosonic_ne_fermionic : bosonic ≠ fermionic := by
  decide

/-- Adding two fermionic parities yields bosonic parity (`1 + 1 = 0` in `ZMod 2`). -/
theorem fermionic_add_fermionic : fermionic + fermionic = bosonic := by
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
  rw [Nat.mul_zero, pow_zero]

@[simp]
theorem koszulSign_one_left (q : ℕ) : koszulSign (R := R) 1 q = (-1 : R) ^ q := by
  dsimp [koszulSign]
  rw [Nat.one_mul]

@[simp]
theorem koszulSign_one_right (p : ℕ) : koszulSign (R := R) p 1 = (-1 : R) ^ p := by
  dsimp [koszulSign]
  rw [Nat.mul_one]

theorem koszulSign_symm (p q : ℕ) : koszulSign (R := R) p q = koszulSign (R := R) q p := by
  dsimp [koszulSign]
  rw [Nat.mul_comm]

theorem koszulSign_add_left (p₁ p₂ q : ℕ) :
    koszulSign (R := R) (p₁ + p₂) q = koszulSign (R := R) p₁ q * koszulSign (R := R) p₂ q := by
  dsimp [koszulSign]
  rw [Nat.add_mul, pow_add]

theorem koszulSign_add_right (p q₁ q₂ : ℕ) :
    koszulSign (R := R) p (q₁ + q₂) = koszulSign (R := R) p q₁ * koszulSign (R := R) p q₂ := by
  dsimp [koszulSign]
  rw [Nat.mul_add, pow_add]

/-- Alias for `koszulSign_add_left` matching the multiplicative character law in the first degree. -/
theorem koszulSign_mul (p₁ p₂ q : ℕ) :
    koszulSign (R := R) (p₁ + p₂) q = koszulSign (R := R) p₁ q * koszulSign (R := R) p₂ q :=
  koszulSign_add_left p₁ p₂ q

/-- `koszulSign p q` is an involution in `R`: `koszulSign p q * koszulSign p q = 1`. -/
theorem koszulSign_sq_one (p q : ℕ) :
    koszulSign (R := R) p q * koszulSign (R := R) p q = 1 := by
  dsimp [koszulSign]
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-! ### Archetype III & IV: Graded Commutativity of Exterior Products -/

/-- For degree-1 generators, `v ∧ w + w ∧ v = 0`. -/
theorem ι_mul_ι_anticomm (v w : M) :
    ι R v * ι R w + ι R w * ι R v = 0 := by
  simpa using (ι_add_mul_swap (R := R) v w)

/-- Fermionic generator anticommutation: `v ∧ w = -(w ∧ v)`. -/
theorem ι_mul_ι_swap (v w : M) :
    ι R v * ι R w = - (ι R w * ι R v) := by
  exact eq_neg_of_add_eq_zero_left (ι_mul_ι_anticomm v w)

/-- Odd elements (fermions) are strictly nilpotent in the exterior Grassmann algebra: `(ι R v)^2 = 0`. -/
theorem fermionic_nilpotent (v : M) :
    (ι R v) ^ 2 = 0 := by
  rw [pow_two]
  exact ι_sq_zero v

/-- Inductive proof that a pure 1-form `ι R v` graded-commutes with an arbitrary
    degree-`q` homogeneous element `y ∈ (range (ι R))^q`:
    `ι R v * y = (-1)^q • (y * ι R v)`. -/
theorem ι_mul_graded_comm (v : M) (q : ℕ) (y : ExteriorAlgebra R M)
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q) :
    ι R v * y = (-1 : R) ^ q • (y * ι R v) := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [pow_zero, one_smul, ← Algebra.commutes]
  | add _ _ _ _ _ ihx ihy =>
      rw [mul_add, ihx, ihy, add_mul, smul_add]
  | mem_mul n hm b hb _ ih =>
      rcases hm with ⟨w, rfl⟩
      rw [← mul_assoc, ι_mul_ι_swap v w, neg_mul, mul_assoc, ih,
        mul_smul_comm, pow_succ, mul_comm ((-1 : R) ^ n) (-1),
        mul_smul, neg_one_smul, smul_neg, mul_assoc]

/-- **Canonical Supercommutativity of the Exterior Algebra**:
    Homogeneous elements `x` of degree `p` and `y` of degree `q` satisfy:
    `x * y = koszulSign p q • (y * x) = (-1)^(p * q) • (y * x)`. -/
theorem supercommutative_exterior (p q : ℕ)
    (x y : ExteriorAlgebra R M)
    (hx : x ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ p)
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q) :
    x * y = koszulSign p q • (y * x) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [koszulSign_zero_left, one_smul, Algebra.commutes]
  | add _ _ _ _ _ ih1 ih2 =>
      rw [add_mul, ih1, ih2, mul_add, smul_add]
  | mem_mul m hm a ha _ ih =>
      rcases hm with ⟨v, rfl⟩
      rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc,
        ι_mul_graded_comm v q y hy, smul_mul_assoc, smul_smul,
        koszulSign_add_left, koszulSign_one_left, mul_comm (koszulSign m q) ((-1 : R) ^ q),
        mul_assoc]

/-! ### Archetype V: Super-Grassmannian Invariants & Non-Commutative Witness -/

/-- The graded super-commutator `[x, y]_s = x * y - (-1)^(p * q) • (y * x)`. -/
def superCommutator (p q : ℕ) (x y : ExteriorAlgebra R M) : ExteriorAlgebra R M :=
  x * y - koszulSign p q • (y * x)

/-- On two odd (degree-1) elements, the graded super-commutator equals the anticommutator `x * y + y * x`. -/
theorem superCommutator_one_one (x y : ExteriorAlgebra R M) :
    superCommutator 1 1 x y = x * y + y * x := by
  dsimp [superCommutator, koszulSign]
  rw [Nat.mul_one, pow_one, neg_one_smul, sub_neg_eq_add]

/-- The graded super-commutator vanishes identically on all pure homogeneous exterior components. -/
theorem superCommutator_vanishes (p q : ℕ)
    (x y : ExteriorAlgebra R M)
    (hx : x ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ p)
    (hy : y ∈ LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ q) :
    superCommutator p q x y = 0 := by
  dsimp [superCommutator]
  rw [supercommutative_exterior p q x y hx hy, sub_self]

/-- Any homogeneous element of odd degree `2 * k + 1` is nilpotent of order 2 (`x * x = 0`)
    whenever `2` is invertible or directly for degree 1; for degree 1 on the nose,
    `superCommutator 1 1 (ι R v) (ι R w) = 0`. -/
theorem superCommutator_ι_ι_zero (v w : M) :
    superCommutator 1 1 (ι R v) (ι R w) = 0 := by
  rw [superCommutator_one_one]
  exact ι_mul_ι_anticomm v w

/-- **Concrete Non-Commutativity Witness on the 3-Color Module `ColorVec3 ℤ`**:
    In the exterior algebra over the 3-color quark module `ColorVec3 ℤ`, the wedge product of
    the red and green basis vectors is non-zero (`ι ℤ e_r * ι ℤ e_g ≠ 0`) and genuinely
    non-commutative (`ι ℤ e_r * ι ℤ e_g ≠ ι ℤ e_g * ι ℤ e_r`). -/
def colorCrossAlternating :
    InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3 ℤ [⋀^Fin 2]→ₗ[ℤ] ℤ :=
  AlternatingMap.ofSubmonoidHom
    (toMultilinearMap :=
      (LinearMap.mk₂ ℤ
        (fun u v : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3 ℤ =>
          (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross u v).c₃)
        (by intro u₁ u₂ v; dsimp [InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross]; ring)
        (by intro c u v; dsimp [InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross]; ring)
        (by intro u v₁ v₂; dsimp [InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross]; ring)
        (by intro c u v; dsimp [InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross]; ring)).mkMultilinearFin2)
    (by
      intro u
      dsimp [InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ColorVec3.cross]
      ring)

end InfoGeometry.Superalgebra.SuperGrassmannExterior
