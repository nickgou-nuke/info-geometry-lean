/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornFreudenthalE7Group
import InfoGeometry.Algebra.H3ZornE7Simplicity
import InfoGeometry.Algebra.H3ZornAutomorphismConjugation
import InfoGeometry.Algebra.SplitE8Simplicity
import InfoGeometry.Exceptional.GenericGradedJacobiClosure
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# 248-Dimensional 5-Graded Freudenthal TKK Lie Algebra `𝔈₈(8)` on `H₃(𝕆_s)`

This module constructs the 248-dimensional 5-graded Kantor–Koecher–Tits (Heisenberg–parabolic)
real exceptional Lie algebra `𝔈₈(8)` from the 56-dimensional split-Albert Freudenthal charge
space `Charge := FreudenthalCharge (H3Zorn ℝ)` and the 133-dimensional split `𝔈₇(7)` algebra
`H3ZornTKKLie`:

  `FreudenthalTKK5E8 = 𝔤₋₂ (ℝ, 1D) ⊕ 𝔤₋₁ (Charge, 56D) ⊕ 𝔤₀ (H3ZornTKKLie × ℝ, 133 + 1 = 134D)`
  `                     ⊕ 𝔤₊₁ (Charge, 56D) ⊕ 𝔤₊₂ (ℝ, 1D)`
  `1 + 56 + (133 + 1) + 56 + 1 = 248`.

Here `𝔤₀ = H3ZornTKKLie × ℝ` carries the 1-dimensional grading center `Z` (`gradeCenterZ`) so that
`[e₊₂, e₋₂] = Z` and `(e₊₂, Z, e₋₂)` forms an `𝔰𝔩₂` triple commuting with `H3ZornTKKLie`.

Main results:
1. `FreudenthalTKK5E8` with `AddCommGroup`, `Module ℝ`, `Module.Finite ℝ`, and
   `finrank_freudenthalTKK5E8 : Module.finrank ℝ FreudenthalTKK5E8 = 248`.
2. Exact 56-dimensional `H3ZornTKKLie` representation `repE7 : H3ZornTKKLie →ₗ⁅ℝ⁆ Module.End ℝ Charge`
   (`t(T₀) = linearTrace (T₀.1 1)`, `1/2` scaling on `repNeg`), proved skew-symmetric with respect
   to `symplecticForm` (`repE7_symplecticForm_skew`) and infinitesimally invariant with respect to
   `quarticInvariant` (`repE7_preserves_quarticInvariant_deriv`, using `Freudenthal.lean`'s
   corrected `+⟨X#, Y#⟩` sign).
3. Symmetric `H3ZornTKKLie`-equivariant operator `K : Charge →ₗ[ℝ] Charge →ₗ[ℝ] H3ZornTKKLie`,
   the triple identity `triple_identity_p1_m1_p1`, full 248D bilinear bracket `bracket5LM`,
   `LieRing` / `LieAlgebra ℝ` via `GenericGradedJacobiClosure.global_leibniz_of_homogeneous`,
   and 5-grading submodules `gGrade : ℤ → Submodule ℝ FreudenthalTKK5E8` (`1, 56, 134, 56, 1`)
   with `gGrade_bracket_mem : ⁅U, V⁆ ∈ gGrade (i + j)`.
4. Unconditional simplicity `freudenthalTKK5E8_isSimple : LieAlgebra.IsSimple ℝ FreudenthalTKK5E8`.
5. Exact Cartan involution `θ₅`, ad-invariant bilinear form `B₅`, positive-definite Cartan inner
   product `cartanInner5`, eigenspace dimensions `120` (`k`) and `128` (`p`), Cartan signature
   `+8`, Killing form definiteness on `k`/`p` + `k ⊥ p`, and `freudenthalTKK5E8_isKilling`.
6. Structural comparison with `SplitE8Lie` (`zeroE7Hom`, `IsSl2Triple gradeCenterZ ePlus2 eMinus2`,
   `8D` split Cartan `tkk5E8Cartan`, matching `finrank = 248`, `IsSimple ℝ`, `IsKilling ℝ`,
   and `8D` Cartan rank).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Algebra

open scoped BigOperators
open H3Zorn
open InfoGeometry.Algebra.H3ZornFreudenthal
open InfoGeometry.Algebra.SplitAlbertStructureOperators
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Exceptional
open InfoGeometry.Exceptional.Freudenthal

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ## 1. Carrier `FreudenthalTKK5E8`, Module Structure, and Dimension `248` -/

section CarrierAndDimension

/-- Carrier of the 248-dimensional 5-graded Freudenthal TKK Lie algebra `𝔈₈(8)`:
`1 + 56 + (133 + 1) + 56 + 1 = 248`. -/
@[ext]
structure FreudenthalTKK5E8 where
  gMinus2 : ℝ
  gMinus1 : Charge
  gZeroE7 : H3ZornTKKLie
  gZeroCenter : ℝ
  gPlus1 : Charge
  gPlus2 : ℝ

instance instInhabitedFreudenthalTKK5E8 : Inhabited FreudenthalTKK5E8 :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

instance instSMulFreudenthalTKK5E8 : SMul ℝ FreudenthalTKK5E8 :=
  ⟨fun r U =>
    ⟨r • U.gMinus2, r • U.gMinus1, r • U.gZeroE7, r • U.gZeroCenter,
      r • U.gPlus1, r • U.gPlus2⟩⟩

instance instAddCommGroupFreudenthalTKK5E8 : AddCommGroup FreudenthalTKK5E8 where
  add U V :=
    ⟨U.gMinus2 + V.gMinus2, U.gMinus1 + V.gMinus1, U.gZeroE7 + V.gZeroE7,
      U.gZeroCenter + V.gZeroCenter, U.gPlus1 + V.gPlus1, U.gPlus2 + V.gPlus2⟩
  add_assoc U V W := by apply FreudenthalTKK5E8.ext <;> exact add_assoc _ _ _
  zero := ⟨0, 0, 0, 0, 0, 0⟩
  zero_add U := by apply FreudenthalTKK5E8.ext <;> exact zero_add _
  add_zero U := by apply FreudenthalTKK5E8.ext <;> exact add_zero _
  nsmul n U :=
    ⟨n • U.gMinus2, n • U.gMinus1, n • U.gZeroE7, n • U.gZeroCenter,
      n • U.gPlus1, n • U.gPlus2⟩
  nsmul_zero U := by apply FreudenthalTKK5E8.ext <;> exact zero_nsmul _
  nsmul_succ n U := by apply FreudenthalTKK5E8.ext <;> exact succ_nsmul _ _
  neg U :=
    ⟨-U.gMinus2, -U.gMinus1, -U.gZeroE7, -U.gZeroCenter, -U.gPlus1, -U.gPlus2⟩
  sub U V :=
    ⟨U.gMinus2 - V.gMinus2, U.gMinus1 - V.gMinus1, U.gZeroE7 - V.gZeroE7,
      U.gZeroCenter - V.gZeroCenter, U.gPlus1 - V.gPlus1, U.gPlus2 - V.gPlus2⟩
  sub_eq_add_neg U V := by apply FreudenthalTKK5E8.ext <;> exact sub_eq_add_neg _ _
  zsmul n U :=
    ⟨n • U.gMinus2, n • U.gMinus1, n • U.gZeroE7, n • U.gZeroCenter,
      n • U.gPlus1, n • U.gPlus2⟩
  zsmul_zero' U := by apply FreudenthalTKK5E8.ext <;> exact zero_zsmul _
  zsmul_succ' n U := by
    apply FreudenthalTKK5E8.ext <;>
    · change ((n + 1 : ℕ) : ℤ) • _ = (n : ℤ) • _ + _
      rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
  zsmul_neg' n U := by
    apply FreudenthalTKK5E8.ext <;>
    · change Int.negSucc n • _ = -(((n + 1 : ℕ) : ℤ) • _)
      rw [Int.negSucc_eq, neg_zsmul, Nat.cast_succ]
  neg_add_cancel U := by apply FreudenthalTKK5E8.ext <;> exact neg_add_cancel _
  add_comm U V := by apply FreudenthalTKK5E8.ext <;> exact add_comm _ _

instance instModuleFreudenthalTKK5E8 : Module ℝ FreudenthalTKK5E8 where
  one_smul U := by apply FreudenthalTKK5E8.ext <;> exact one_smul ℝ _
  mul_smul r s U := by apply FreudenthalTKK5E8.ext <;> exact mul_smul r s _
  smul_zero r := by apply FreudenthalTKK5E8.ext <;> exact smul_zero r
  smul_add r U V := by apply FreudenthalTKK5E8.ext <;> exact smul_add r _ _
  add_smul r s U := by apply FreudenthalTKK5E8.ext <;> exact add_smul r s _
  zero_smul U := by apply FreudenthalTKK5E8.ext <;> exact zero_smul ℝ _

@[simp] theorem zero_gMinus2 : (0 : FreudenthalTKK5E8).gMinus2 = 0 := rfl
@[simp] theorem zero_gMinus1 : (0 : FreudenthalTKK5E8).gMinus1 = 0 := rfl
@[simp] theorem zero_gZeroE7 : (0 : FreudenthalTKK5E8).gZeroE7 = 0 := rfl
@[simp] theorem zero_gZeroCenter : (0 : FreudenthalTKK5E8).gZeroCenter = 0 := rfl
@[simp] theorem zero_gPlus1 : (0 : FreudenthalTKK5E8).gPlus1 = 0 := rfl
@[simp] theorem zero_gPlus2 : (0 : FreudenthalTKK5E8).gPlus2 = 0 := rfl

@[simp] theorem add_gMinus2 (U V : FreudenthalTKK5E8) :
    (U + V).gMinus2 = U.gMinus2 + V.gMinus2 := rfl
@[simp] theorem add_gMinus1 (U V : FreudenthalTKK5E8) :
    (U + V).gMinus1 = U.gMinus1 + V.gMinus1 := rfl
@[simp] theorem add_gZeroE7 (U V : FreudenthalTKK5E8) :
    (U + V).gZeroE7 = U.gZeroE7 + V.gZeroE7 := rfl
@[simp] theorem add_gZeroCenter (U V : FreudenthalTKK5E8) :
    (U + V).gZeroCenter = U.gZeroCenter + V.gZeroCenter := rfl
@[simp] theorem add_gPlus1 (U V : FreudenthalTKK5E8) :
    (U + V).gPlus1 = U.gPlus1 + V.gPlus1 := rfl
@[simp] theorem add_gPlus2 (U V : FreudenthalTKK5E8) :
    (U + V).gPlus2 = U.gPlus2 + V.gPlus2 := rfl

@[simp] theorem neg_gMinus2 (U : FreudenthalTKK5E8) : (-U).gMinus2 = -U.gMinus2 := rfl
@[simp] theorem neg_gMinus1 (U : FreudenthalTKK5E8) : (-U).gMinus1 = -U.gMinus1 := rfl
@[simp] theorem neg_gZeroE7 (U : FreudenthalTKK5E8) : (-U).gZeroE7 = -U.gZeroE7 := rfl
@[simp] theorem neg_gZeroCenter (U : FreudenthalTKK5E8) : (-U).gZeroCenter = -U.gZeroCenter := rfl
@[simp] theorem neg_gPlus1 (U : FreudenthalTKK5E8) : (-U).gPlus1 = -U.gPlus1 := rfl
@[simp] theorem neg_gPlus2 (U : FreudenthalTKK5E8) : (-U).gPlus2 = -U.gPlus2 := rfl

@[simp] theorem sub_gMinus2 (U V : FreudenthalTKK5E8) :
    (U - V).gMinus2 = U.gMinus2 - V.gMinus2 := rfl
@[simp] theorem sub_gMinus1 (U V : FreudenthalTKK5E8) :
    (U - V).gMinus1 = U.gMinus1 - V.gMinus1 := rfl
@[simp] theorem sub_gZeroE7 (U V : FreudenthalTKK5E8) :
    (U - V).gZeroE7 = U.gZeroE7 - V.gZeroE7 := rfl
@[simp] theorem sub_gZeroCenter (U V : FreudenthalTKK5E8) :
    (U - V).gZeroCenter = U.gZeroCenter - V.gZeroCenter := rfl
@[simp] theorem sub_gPlus1 (U V : FreudenthalTKK5E8) :
    (U - V).gPlus1 = U.gPlus1 - V.gPlus1 := rfl
@[simp] theorem sub_gPlus2 (U V : FreudenthalTKK5E8) :
    (U - V).gPlus2 = U.gPlus2 - V.gPlus2 := rfl

@[simp] theorem smul_gMinus2 (r : ℝ) (U : FreudenthalTKK5E8) :
    (r • U).gMinus2 = r * U.gMinus2 := rfl
@[simp] theorem smul_gMinus1 (r : ℝ) (U : FreudenthalTKK5E8) :
    (r • U).gMinus1 = r • U.gMinus1 := rfl
@[simp] theorem smul_gZeroE7 (r : ℝ) (U : FreudenthalTKK5E8) :
    (r • U).gZeroE7 = r • U.gZeroE7 := rfl
@[simp] theorem smul_gZeroCenter (r : ℝ) (U : FreudenthalTKK5E8) :
    (r • U).gZeroCenter = r * U.gZeroCenter := rfl
@[simp] theorem smul_gPlus1 (r : ℝ) (U : FreudenthalTKK5E8) :
    (r • U).gPlus1 = r • U.gPlus1 := rfl
@[simp] theorem smul_gPlus2 (r : ℝ) (U : FreudenthalTKK5E8) :
    (r • U).gPlus2 = r * U.gPlus2 := rfl

/-- Linear equivalence identifying `FreudenthalTKK5E8` with the product
`ℝ × Charge × H3ZornTKKLie × ℝ × Charge × ℝ`. -/
def toProdEquiv :
    FreudenthalTKK5E8 ≃ₗ[ℝ] (ℝ × Charge × H3ZornTKKLie × ℝ × Charge × ℝ) where
  toFun U := (U.gMinus2, U.gMinus1, U.gZeroE7, U.gZeroCenter, U.gPlus1, U.gPlus2)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv U := by ext <;> rfl
  right_inv p := by rcases p with ⟨_, _, _, _, _, _⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private instance instModuleFiniteCharge : Module.Finite ℝ Charge :=
  Module.Finite.equiv chargeCoordinateLinearEquiv.symm

instance instModuleFiniteFreudenthalTKK5E8 : Module.Finite ℝ FreudenthalTKK5E8 :=
  Module.Finite.equiv toProdEquiv.symm

/-- **Exact 248-dimensionality of `FreudenthalTKK5E8`**: `1 + 56 + 133 + 1 + 56 + 1 = 248`. -/
theorem finrank_freudenthalTKK5E8 :
    Module.finrank ℝ FreudenthalTKK5E8 = 248 := by
  rw [LinearEquiv.finrank_eq toProdEquiv, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self, finrank_charge, finrank_H3ZornTKKLie]

end CarrierAndDimension

/-! ## 2. Jordan-Triple Bridge Lemmas (`H3Zorn` ↔ `JordanTKK`) -/

section JordanTripleBridge

@[simp] private theorem charge_zero_alpha : (0 : Charge).alpha = 0 := rfl
@[simp] private theorem charge_zero_beta : (0 : Charge).beta = 0 := rfl
@[simp] private theorem charge_zero_x : (0 : Charge).x = 0 := rfl
@[simp] private theorem charge_zero_y : (0 : Charge).y = 0 := rfl
@[simp] private theorem charge_neg_alpha (Q : Charge) : (-Q).alpha = -Q.alpha := rfl
@[simp] private theorem charge_neg_beta (Q : Charge) : (-Q).beta = -Q.beta := rfl
@[simp] private theorem charge_neg_x (Q : Charge) : (-Q).x = -Q.x := rfl
@[simp] private theorem charge_neg_y (Q : Charge) : (-Q).y = -Q.y := rfl
@[simp] private theorem charge_sub_alpha (Q P : Charge) : (Q - P).alpha = Q.alpha - P.alpha := rfl
@[simp] private theorem charge_sub_beta (Q P : Charge) : (Q - P).beta = Q.beta - P.beta := rfl
@[simp] private theorem charge_sub_x (Q P : Charge) : (Q - P).x = Q.x - P.x := rfl
@[simp] private theorem charge_sub_y (Q P : Charge) : (Q - P).y = Q.y - P.y := rfl

@[simp] private theorem h3_traceBilin_neg_left (x y : H3Zorn ℝ) :
    H3Zorn.traceBilin (-x) y = -H3Zorn.traceBilin x y := by
  rw [show (-x : H3Zorn ℝ) = (-1 : ℝ) • x by module, H3Zorn.traceBilin_smul_left]
  ring

@[simp] private theorem h3_traceBilin_neg_right (x y : H3Zorn ℝ) :
    H3Zorn.traceBilin x (-y) = -H3Zorn.traceBilin x y := by
  rw [show (-y : H3Zorn ℝ) = (-1 : ℝ) • y by module, H3Zorn.traceBilin_smul_right]
  ring

@[simp] private theorem h3_crossProduct_neg_left (x y : H3Zorn ℝ) :
    H3Zorn.crossProduct (-x) y = -H3Zorn.crossProduct x y := by
  rw [show (-x : H3Zorn ℝ) = (-1 : ℝ) • x by module, H3Zorn.crossProduct_smul_left]
  module

@[simp] private theorem h3_crossProduct_neg_right (x y : H3Zorn ℝ) :
    H3Zorn.crossProduct x (-y) = -H3Zorn.crossProduct x y := by
  rw [show (-y : H3Zorn ℝ) = (-1 : ℝ) • y by module, H3Zorn.crossProduct_smul_right]
  module

private theorem h3_mul_one (a : H3Zorn ℝ) : a * (1 : H3Zorn ℝ) = a :=
  candidateJordanMul_one_right a

private theorem h3_one_mul (a : H3Zorn ℝ) : (1 : H3Zorn ℝ) * a = a :=
  candidateJordanMul_one_left a

private theorem h3_mul_smul_right (r : ℝ) (a b : H3Zorn ℝ) : a * (r • b) = r • (a * b) := by
  change candidateJordanMul a (r • b) = r • candidateJordanMul a b
  exact candidateJordanMul_smul_right r a b

private theorem h3_mul_smul_left (r : ℝ) (a b : H3Zorn ℝ) : (r • a) * b = r • (a * b) := by
  change candidateJordanMul (r • a) b = r • candidateJordanMul a b
  exact candidateJordanMul_smul_left r a b

private theorem jordanTKK_triple_eq_half_T (x y z : H3Zorn ℝ) :
    JordanTKK.triple x y z = (1 / 2 : ℝ) • H3Zorn.T x y z := by
  have hP : ∀ u v : H3Zorn ℝ, H3Zorn.T u 1 v = (2 : ℝ) • (u * v) := by
    intro u v
    have hmul : u * v = (1 / 2 : ℝ) • H3Zorn.T u 1 v := by
      change candidateJordanMul u v = _
      rfl
    rw [hmul, smul_smul]
    norm_num
  have h4U : ∀ u v : H3Zorn ℝ,
      (4 : ℝ) • H3Zorn.U u v = (8 : ℝ) • (u * (u * v)) - (4 : ℝ) • ((u * u) * v) := by
    intro u v
    have h := H3Zorn.four_U u v
    rw [hP u v, hP u ((2 : ℝ) • (u * v)), hP u u, hP ((2 : ℝ) • (u * u)) v,
      h3_mul_smul_right, h3_mul_smul_left] at h
    rw [show (2 : ℝ) • ((2 : ℝ) • (2 : ℝ) • (u * (u * v))) = (8 : ℝ) • (u * (u * v)) by module,
      show (2 : ℝ) • ((2 : ℝ) • ((u * u) * v)) = (4 : ℝ) • ((u * u) * v) by module] at h
    exact h
  have hU : ∀ u v : H3Zorn ℝ, H3Zorn.U u v = (2 : ℝ) • (u * (u * v)) - (u * u) * v := by
    intro u v
    have h := congrArg (fun w : H3Zorn ℝ => (1 / 4 : ℝ) • w) (h4U u v)
    simp only [smul_sub, smul_smul] at h
    norm_num at h
    exact h
  rw [H3Zorn.T, hU (x + z) y, hU x y, hU z y]
  simp only [add_mul, mul_add]
  have hxz1 : x * (z * y) + z * (x * y) = (x * y) * z + (z * y) * x := by
    rw [mul_comm z (x * y), mul_comm x (z * y)]
    abel
  have hxz2 : (x * z) * y + (z * x) * y = (2 : ℝ) • ((x * z) * y) := by
    rw [mul_comm z x]
    module
  have hgoal :
      (1 / 2 : ℝ) • ((2 : ℝ) • (x * (x * y) + z * (x * y) + (x * (z * y) + z * (z * y))) -
          (x * x * y + z * x * y + (x * z * y + z * z * y)) -
          ((2 : ℝ) • (x * (x * y)) - x * x * y) -
          ((2 : ℝ) • (z * (z * y)) - z * z * y)) =
        (1 / 2 : ℝ) • ((2 : ℝ) • (x * (z * y) + z * (x * y)) - (x * z * y + z * x * y)) := by
    congr 1
    simp only [smul_add]
    abel
  rw [JordanTKK.triple, hgoal, hxz1, hxz2]
  module

/-- Expanded cubic-data formula for `JordanTKK.tripleD ℝ x y z`. -/
theorem tripleD_apply_expanded (x y z : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ x y z =
      (1 / 2 : ℝ) • (H3Zorn.traceBilin x y • z + H3Zorn.traceBilin z y • x -
        H3Zorn.crossProduct (H3Zorn.crossProduct x z) y) := by
  rw [JordanTKK.tripleD_apply, jordanTKK_triple_eq_half_T, H3Zorn.T_outer_formula]

/-- Evaluating `JordanTKK.tripleD ℝ x y` on the identity `1` recovers `x * y`. -/
theorem tripleD_apply_one (x y : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ x y (1 : H3Zorn ℝ) = x * y := by
  rw [JordanTKK.tripleD_apply, JordanTKK.triple, h3_mul_one, h3_one_mul, h3_mul_one, mul_comm y x]
  abel

/-- `linearTrace (JordanTKK.tripleD ℝ x y 1) = traceBilin x y`. -/
theorem linearTrace_tripleD_apply_one (x y : H3Zorn ℝ) :
    H3Zorn.linearTrace (JordanTKK.tripleD ℝ x y (1 : H3Zorn ℝ)) = H3Zorn.traceBilin x y := by
  rw [tripleD_apply_one]
  exact h3Zorn_linearTrace_jordanMul x y

/-- Trace-adjoint is involutive on `Module.End ℝ (H3Zorn ℝ)`. -/
theorem h3zornTraceAdjoint_involutive (f : Module.End ℝ (H3Zorn ℝ)) :
    h3zornTraceAdjoint (h3zornTraceAdjoint f) = f := by
  apply LinearMap.ext
  intro x
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro y
  rw [h3zornTraceAdjoint_pair, H3Zorn.traceBilin_symm, h3zornTraceAdjoint_pair,
    H3Zorn.traceBilin_symm]

private theorem symmetric_trilinear_h3zorn_eq_zero
    (F : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ)
    (h12 : ∀ x y z, F x y z = F y x z)
    (h23 : ∀ x y z, F x y z = F x z y)
    (hdiag : ∀ x, F x x x = 0) (x y z : H3Zorn ℝ) : F x y z = 0 := by
  have h13 (a b c : H3Zorn ℝ) : F a b c = F c b a := by rw [h12, h23, h12]
  have hpol : 6 * F x y z =
      F (x + y + z) (x + y + z) (x + y + z) -
      F (x + y) (x + y) (x + y) - F (x + z) (x + z) (x + z) -
      F (y + z) (y + z) (y + z) + F x x x + F y y y + F z z z := by
    simp only [map_add, LinearMap.add_apply]
    rw [h12 y x x, h23 x x y, h23 y y x, h12 y x y,
      h12 z x x, h23 x x z, h23 z z x, h12 z x z,
      h12 z y y, h23 y y z, h23 z z y, h12 z y z,
      h23 y z x, h12 y x z, h12 z x y, h23 x z y,
      h13 z y x]
    ring
  rw [hdiag, hdiag, hdiag, hdiag, hdiag, hdiag, hdiag] at hpol
  linarith

private theorem jordanLmul_crossProduct_rule (a x y : H3Zorn ℝ) :
    a * H3Zorn.crossProduct x y + H3Zorn.crossProduct (a * x) y +
      H3Zorn.crossProduct x (a * y) =
      H3Zorn.linearTrace a • H3Zorn.crossProduct x y := by
  have hdiag : ∀ w : H3Zorn ℝ,
      traceBilin (H3Zorn.adjointQuad w) (a * w) - normCubic w * linearTrace a = 0 := by
    intro w
    rw [traceBilin_adjointQuad_jordanLmul a w, sub_self]
  let F : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun u =>
        { toFun := fun v =>
            { toFun := fun w =>
                H3Zorn.traceBilin (a * H3Zorn.crossProduct u v +
                  H3Zorn.crossProduct (a * u) v +
                  H3Zorn.crossProduct u (a * v) -
                  H3Zorn.linearTrace a • H3Zorn.crossProduct u v) w
              map_add' := fun w₁ w₂ => by rw [H3Zorn.traceBilin_add_right]
              map_smul' := fun r w => by rw [H3Zorn.traceBilin_smul_right, smul_eq_mul]; rfl }
          map_add' := fun v₁ v₂ => by
            ext w
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
              H3Zorn.crossProduct_add_right, mul_add, smul_add,
              H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_sub_left]
            ring
          map_smul' := fun r v => by
            ext w
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
              H3Zorn.crossProduct_smul_right, h3_mul_smul_right, smul_eq_mul, RingHom.id_apply,
              H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_smul_left]
            ring }
      map_add' := fun u₁ u₂ => by
        ext v w
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          H3Zorn.crossProduct_add_left, mul_add, smul_add,
          H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_sub_left]
        ring
      map_smul' := fun r u => by
        ext v w
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          H3Zorn.crossProduct_smul_left, h3_mul_smul_right, smul_eq_mul, RingHom.id_apply,
          H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_smul_left]
        ring }
  have h12 : ∀ u v w, F u v w = F v u w := by
    intro u v w
    dsimp [F]
    rw [H3Zorn.crossProduct_symm u v, H3Zorn.crossProduct_symm (a * u) v,
      H3Zorn.crossProduct_symm u (a * v)]
    congr 2
    abel
  have h23 : ∀ u v w, F u v w = F u w v := by
    intro u v w
    dsimp [F]
    simp only [H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_add_left,
      H3Zorn.traceBilin_smul_left]
    have t1 : H3Zorn.traceBilin (a * H3Zorn.crossProduct u v) w =
        H3Zorn.traceBilin (H3Zorn.crossProduct u (a * w)) v := by
      calc H3Zorn.traceBilin (a * H3Zorn.crossProduct u v) w
          = H3Zorn.traceBilin w (a * H3Zorn.crossProduct u v) := H3Zorn.traceBilin_symm _ _
        _ = H3Zorn.traceBilin (w * a) (H3Zorn.crossProduct u v) := by
            rw [mul_comm w a]
            exact (h3Zorn_traceBilin_jordanLmul_assoc a w (H3Zorn.crossProduct u v)).symm
        _ = H3Zorn.traceBilin (H3Zorn.crossProduct u v) (a * w) := by
            rw [mul_comm w a, H3Zorn.traceBilin_symm]
        _ = H3Zorn.traceBilin u (H3Zorn.crossProduct v (a * w)) :=
            H3Zorn.traceBilin_crossProduct_assoc u v (a * w)
        _ = H3Zorn.traceBilin u (H3Zorn.crossProduct (a * w) v) := by
            rw [H3Zorn.crossProduct_symm v (a * w)]
        _ = H3Zorn.traceBilin (H3Zorn.crossProduct u (a * w)) v :=
            (H3Zorn.traceBilin_crossProduct_assoc u (a * w) v).symm
    have t2 : H3Zorn.traceBilin (H3Zorn.crossProduct (a * u) v) w =
        H3Zorn.traceBilin (H3Zorn.crossProduct (a * u) w) v := by
      calc H3Zorn.traceBilin (H3Zorn.crossProduct (a * u) v) w
          = H3Zorn.traceBilin (a * u) (H3Zorn.crossProduct v w) :=
            H3Zorn.traceBilin_crossProduct_assoc (a * u) v w
        _ = H3Zorn.traceBilin (a * u) (H3Zorn.crossProduct w v) := by
            rw [H3Zorn.crossProduct_symm v w]
        _ = H3Zorn.traceBilin (H3Zorn.crossProduct (a * u) w) v :=
            (H3Zorn.traceBilin_crossProduct_assoc (a * u) w v).symm
    have t3 : H3Zorn.traceBilin (H3Zorn.crossProduct u (a * v)) w =
        H3Zorn.traceBilin (a * H3Zorn.crossProduct u w) v := by
      calc H3Zorn.traceBilin (H3Zorn.crossProduct u (a * v)) w
          = H3Zorn.traceBilin (H3Zorn.crossProduct (a * v) u) w := by
            rw [H3Zorn.crossProduct_symm u (a * v)]
        _ = H3Zorn.traceBilin (a * v) (H3Zorn.crossProduct u w) :=
            H3Zorn.traceBilin_crossProduct_assoc (a * v) u w
        _ = H3Zorn.traceBilin v (a * H3Zorn.crossProduct u w) :=
            h3Zorn_traceBilin_jordanLmul_assoc a v (H3Zorn.crossProduct u w)
        _ = H3Zorn.traceBilin (a * H3Zorn.crossProduct u w) v := H3Zorn.traceBilin_symm _ _
    have t4 : H3Zorn.traceBilin (H3Zorn.crossProduct u v) w =
        H3Zorn.traceBilin (H3Zorn.crossProduct u w) v := by
      calc H3Zorn.traceBilin (H3Zorn.crossProduct u v) w
          = H3Zorn.traceBilin u (H3Zorn.crossProduct v w) :=
            H3Zorn.traceBilin_crossProduct_assoc u v w
        _ = H3Zorn.traceBilin u (H3Zorn.crossProduct w v) := by
            rw [H3Zorn.crossProduct_symm v w]
        _ = H3Zorn.traceBilin (H3Zorn.crossProduct u w) v :=
            (H3Zorn.traceBilin_crossProduct_assoc u w v).symm
    rw [t1, t2, t3, t4]
    ring
  have hFdiag : ∀ w : H3Zorn ℝ, F w w w = 0 := by
    intro w
    dsimp [F]
    simp only [H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_add_left,
      H3Zorn.traceBilin_smul_left]
    rw [H3Zorn.crossProduct_self, H3Zorn.crossProduct_symm w (a * w),
      h3_mul_smul_right, H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_left]
    have h1 : H3Zorn.traceBilin (a * H3Zorn.adjointQuad w) w =
        H3Zorn.normCubic w * H3Zorn.linearTrace a := by
      calc H3Zorn.traceBilin (a * H3Zorn.adjointQuad w) w
          = H3Zorn.traceBilin (a * H3Zorn.adjointQuad w) w := rfl
        _ = H3Zorn.traceBilin (H3Zorn.adjointQuad w) (a * w) :=
            h3Zorn_traceBilin_jordanLmul_assoc a (H3Zorn.adjointQuad w) w
        _ = H3Zorn.normCubic w * H3Zorn.linearTrace a :=
            traceBilin_adjointQuad_jordanLmul a w
    have h2 : H3Zorn.traceBilin (H3Zorn.crossProduct (a * w) w) w =
        2 * (H3Zorn.normCubic w * H3Zorn.linearTrace a) := by
      calc H3Zorn.traceBilin (H3Zorn.crossProduct (a * w) w) w
          = H3Zorn.traceBilin (a * w) (H3Zorn.crossProduct w w) :=
            H3Zorn.traceBilin_crossProduct_assoc (a * w) w w
        _ = 2 * H3Zorn.traceBilin (H3Zorn.adjointQuad w) (a * w) := by
            rw [H3Zorn.crossProduct_self, H3Zorn.traceBilin_smul_right, H3Zorn.traceBilin_symm]
        _ = 2 * (H3Zorn.normCubic w * H3Zorn.linearTrace a) := by
            rw [traceBilin_adjointQuad_jordanLmul a w]
    have h3 : H3Zorn.traceBilin (H3Zorn.adjointQuad w) w = 3 * H3Zorn.normCubic w :=
      H3Zorn.mccrimmon_identity_13 w
    rw [h1, h2, h3]
    ring
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  have h0 := symmetric_trilinear_h3zorn_eq_zero F h12 h23 hFdiag x y z
  dsimp [F] at h0
  rw [H3Zorn.traceBilin_sub_left] at h0
  exact sub_eq_zero.mp h0

/-- Structure-algebra infinitesimal cross-product intertwining law. -/
theorem str_crossProduct_rule (T₀ : h3zornTKKDatum.str) (x y : H3Zorn ℝ) :
    h3zornTraceAdjoint T₀.1 (H3Zorn.crossProduct x y) +
      H3Zorn.crossProduct (T₀.1 x) y + H3Zorn.crossProduct x (T₀.1 y) =
      H3Zorn.linearTrace (T₀.1 1) • H3Zorn.crossProduct x y := by
  rcases h3zornTKKDatum.str_decomp T₀.1 T₀.2 with ⟨D, a, hT⟩
  let E : H3ZornF4Derivations := ⟨D.1, D.2⟩
  have hT1 : T₀.1 1 = a := by
    rw [hT, LinearMap.add_apply, jordanLmul_apply]
    have hD1 : (E : Module.End ℝ (H3Zorn ℝ)) 1 = 0 :=
      h3ZornF4_derivation_apply_one_eq_zero E
    change (E : Module.End ℝ (H3Zorn ℝ)) 1 + candidateJordanMul a 1 = a
    rw [hD1, zero_add, candidateJordanMul_one_right]
  have hadj : h3zornTraceAdjoint T₀.1 = -(E : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a := by
    have hE' : (E : Module.End ℝ (H3Zorn ℝ)) = (D : Module.End ℝ (H3Zorn ℝ)) := rfl
    rw [hT, show h3zornTraceAdjoint ((D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a) =
        h3zornTraceAdjointLM ((D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a) from rfl,
      map_add, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjoint_derivation, h3zornTraceAdjoint_jordanLmul, hE']
  have hD_cross : (E : Module.End ℝ (H3Zorn ℝ)) (H3Zorn.crossProduct x y) =
      H3Zorn.crossProduct ((E : Module.End ℝ (H3Zorn ℝ)) x) y +
        H3Zorn.crossProduct x ((E : Module.End ℝ (H3Zorn ℝ)) y) := by
    have hxy := h3ZornF4_derivation_adjointQuad E (x + y)
    have hx := h3ZornF4_derivation_adjointQuad E x
    have hy := h3ZornF4_derivation_adjointQuad E y
    have hadj_sum : H3Zorn.adjointQuad (x + y) =
        H3Zorn.adjointQuad x + H3Zorn.crossProduct x y + H3Zorn.adjointQuad y := by
      simp only [H3Zorn.crossProduct]; abel
    rw [hadj_sum, map_add, map_add, map_add, hx, hy,
      H3Zorn.crossProduct_add_left, H3Zorn.crossProduct_add_right,
      H3Zorn.crossProduct_add_right] at hxy
    have hxy' :
        (E : Module.End ℝ (H3Zorn ℝ)) (H3Zorn.crossProduct x y) +
          (H3Zorn.crossProduct x ((E : Module.End ℝ (H3Zorn ℝ)) x) +
            H3Zorn.crossProduct y ((E : Module.End ℝ (H3Zorn ℝ)) y)) =
        (H3Zorn.crossProduct ((E : Module.End ℝ (H3Zorn ℝ)) x) y +
            H3Zorn.crossProduct x ((E : Module.End ℝ (H3Zorn ℝ)) y)) +
          (H3Zorn.crossProduct x ((E : Module.End ℝ (H3Zorn ℝ)) x) +
            H3Zorn.crossProduct y ((E : Module.End ℝ (H3Zorn ℝ)) y)) := by
      convert hxy using 1
      · abel
      · rw [H3Zorn.crossProduct_symm ((E : Module.End ℝ (H3Zorn ℝ)) x) y]
        abel
    exact add_right_cancel hxy'
  have hDE : (D : Module.End ℝ (H3Zorn ℝ)) = (E : Module.End ℝ (H3Zorn ℝ)) := rfl
  rw [hT1, hadj, LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply,
    hT, hDE, LinearMap.add_apply, LinearMap.add_apply, jordanLmul_apply, jordanLmul_apply,
    H3Zorn.crossProduct_add_left, H3Zorn.crossProduct_add_right, hD_cross]
  have ha_cross := jordanLmul_crossProduct_rule a x y
  rw [← ha_cross]
  abel

/-- Adjoint form of `str_crossProduct_rule`. -/
theorem str_crossProduct_rule_adj (T₀ : h3zornTKKDatum.str) (x y : H3Zorn ℝ) :
    T₀.1 (H3Zorn.crossProduct x y) +
      H3Zorn.crossProduct (h3zornTraceAdjoint T₀.1 x) y +
      H3Zorn.crossProduct x (h3zornTraceAdjoint T₀.1 y) =
      H3Zorn.linearTrace (T₀.1 1) • H3Zorn.crossProduct x y := by
  let T₀adj : h3zornTKKDatum.str :=
    ⟨h3zornTraceAdjoint T₀.1, h3zornTKKDatum.adj_mem_str T₀.2⟩
  have h := str_crossProduct_rule T₀adj x y
  have hinv : h3zornTraceAdjoint T₀adj.1 (H3Zorn.crossProduct x y) =
      T₀.1 (H3Zorn.crossProduct x y) := by
    change h3zornTraceAdjoint (h3zornTraceAdjoint T₀.1) _ = _
    rw [h3zornTraceAdjoint_involutive]
  have htr : H3Zorn.linearTrace (T₀adj.1 1) = H3Zorn.linearTrace (T₀.1 1) := by
    rw [← H3Zorn.traceBilin_one, show T₀adj.1 1 = h3zornTraceAdjoint T₀.1 1 from rfl,
      h3zornTraceAdjoint_pair, H3Zorn.traceBilin_symm, H3Zorn.traceBilin_one]
  rw [hinv, htr] at h
  exact h

/-- Polarized McCrimmon identity (12) in `tripleD` form (cross product in second slot). -/
theorem polarized_mccrimmon_12_tripleD_right (u v y z : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ u (H3Zorn.crossProduct v y) z +
      JordanTKK.tripleD ℝ v (H3Zorn.crossProduct u y) z +
      JordanTKK.tripleD ℝ y (H3Zorn.crossProduct u v) z =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z := by
  have hpol :
      H3Zorn.crossProduct (H3Zorn.adjointQuad (u + v)) (H3Zorn.crossProduct y z) +
        H3Zorn.crossProduct (H3Zorn.crossProduct (u + v) y) (H3Zorn.crossProduct (u + v) z) -
      (H3Zorn.crossProduct (H3Zorn.adjointQuad u) (H3Zorn.crossProduct y z) +
        H3Zorn.crossProduct (H3Zorn.crossProduct u y) (H3Zorn.crossProduct u z)) -
      (H3Zorn.crossProduct (H3Zorn.adjointQuad v) (H3Zorn.crossProduct y z) +
        H3Zorn.crossProduct (H3Zorn.crossProduct v y) (H3Zorn.crossProduct v z)) =
      (H3Zorn.traceBilin (H3Zorn.adjointQuad (u + v)) y • z +
        H3Zorn.traceBilin (H3Zorn.adjointQuad (u + v)) z • y +
        H3Zorn.traceBilin (H3Zorn.crossProduct y z) (u + v) • (u + v)) -
      (H3Zorn.traceBilin (H3Zorn.adjointQuad u) y • z +
        H3Zorn.traceBilin (H3Zorn.adjointQuad u) z • y +
        H3Zorn.traceBilin (H3Zorn.crossProduct y z) u • u) -
      (H3Zorn.traceBilin (H3Zorn.adjointQuad v) y • z +
        H3Zorn.traceBilin (H3Zorn.adjointQuad v) z • y +
        H3Zorn.traceBilin (H3Zorn.crossProduct y z) v • v) := by
    rw [H3Zorn.mccrimmon_identity_12 (u + v) y z,
      H3Zorn.mccrimmon_identity_12 u y z, H3Zorn.mccrimmon_identity_12 v y z]
  have hadj : H3Zorn.adjointQuad (u + v) =
      H3Zorn.adjointQuad u + H3Zorn.crossProduct u v + H3Zorn.adjointQuad v := by
    simp only [H3Zorn.crossProduct]; abel
  simp only [hadj, H3Zorn.crossProduct_add_left, H3Zorn.crossProduct_add_right,
    H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right, add_smul, smul_add] at hpol
  have h12 :
      H3Zorn.crossProduct (H3Zorn.crossProduct u v) (H3Zorn.crossProduct y z) +
        H3Zorn.crossProduct (H3Zorn.crossProduct u y) (H3Zorn.crossProduct v z) +
        H3Zorn.crossProduct (H3Zorn.crossProduct v y) (H3Zorn.crossProduct u z) =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z +
        H3Zorn.traceBilin (H3Zorn.crossProduct u v) z • y +
        H3Zorn.traceBilin (H3Zorn.crossProduct y z) u • v +
        H3Zorn.traceBilin (H3Zorn.crossProduct y z) v • u := by
    convert hpol using 1 <;> module
  simp only [tripleD_apply_expanded]
  have hcross_eq :
      H3Zorn.crossProduct (H3Zorn.crossProduct u z) (H3Zorn.crossProduct v y) +
        H3Zorn.crossProduct (H3Zorn.crossProduct v z) (H3Zorn.crossProduct u y) +
        H3Zorn.crossProduct (H3Zorn.crossProduct y z) (H3Zorn.crossProduct u v) =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z +
        H3Zorn.traceBilin (H3Zorn.crossProduct u v) z • y +
        H3Zorn.traceBilin (H3Zorn.crossProduct y z) u • v +
        H3Zorn.traceBilin (H3Zorn.crossProduct y z) v • u := by
    rw [H3Zorn.crossProduct_symm (H3Zorn.crossProduct u z) (H3Zorn.crossProduct v y),
      H3Zorn.crossProduct_symm (H3Zorn.crossProduct v z) (H3Zorn.crossProduct u y),
      H3Zorn.crossProduct_symm (H3Zorn.crossProduct y z) (H3Zorn.crossProduct u v)]
    convert h12 using 1
    abel
  have htr1 : H3Zorn.traceBilin u (H3Zorn.crossProduct v y) =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y :=
    (H3Zorn.traceBilin_crossProduct_assoc u v y).symm
  have htr2 : H3Zorn.traceBilin v (H3Zorn.crossProduct u y) =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y := by
    rw [← H3Zorn.traceBilin_crossProduct_assoc v u y, H3Zorn.crossProduct_symm v u]
  have htr3 : H3Zorn.traceBilin y (H3Zorn.crossProduct u v) =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y :=
    H3Zorn.traceBilin_symm _ _
  have htz1 : H3Zorn.traceBilin z (H3Zorn.crossProduct v y) =
      H3Zorn.traceBilin (H3Zorn.crossProduct y z) v := by
    calc H3Zorn.traceBilin z (H3Zorn.crossProduct v y)
        = H3Zorn.traceBilin (H3Zorn.crossProduct v y) z := H3Zorn.traceBilin_symm _ _
      _ = H3Zorn.traceBilin (H3Zorn.crossProduct y v) z := by rw [H3Zorn.crossProduct_symm v y]
      _ = H3Zorn.traceBilin y (H3Zorn.crossProduct v z) :=
          H3Zorn.traceBilin_crossProduct_assoc y v z
      _ = H3Zorn.traceBilin y (H3Zorn.crossProduct z v) := by rw [H3Zorn.crossProduct_symm v z]
      _ = H3Zorn.traceBilin (H3Zorn.crossProduct y z) v :=
          (H3Zorn.traceBilin_crossProduct_assoc y z v).symm
  have htz2 : H3Zorn.traceBilin z (H3Zorn.crossProduct u y) =
      H3Zorn.traceBilin (H3Zorn.crossProduct y z) u := by
    calc H3Zorn.traceBilin z (H3Zorn.crossProduct u y)
        = H3Zorn.traceBilin (H3Zorn.crossProduct u y) z := H3Zorn.traceBilin_symm _ _
      _ = H3Zorn.traceBilin (H3Zorn.crossProduct y u) z := by rw [H3Zorn.crossProduct_symm u y]
      _ = H3Zorn.traceBilin y (H3Zorn.crossProduct u z) :=
          H3Zorn.traceBilin_crossProduct_assoc y u z
      _ = H3Zorn.traceBilin y (H3Zorn.crossProduct z u) := by rw [H3Zorn.crossProduct_symm u z]
      _ = H3Zorn.traceBilin (H3Zorn.crossProduct y z) u :=
          (H3Zorn.traceBilin_crossProduct_assoc y z u).symm
  have htz3 : H3Zorn.traceBilin z (H3Zorn.crossProduct u v) =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) z :=
    H3Zorn.traceBilin_symm _ _
  rw [htr1, htr2, htr3, htz1, htz2, htz3]
  have hsum :
      (1 / 2 : ℝ) • (H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z +
          H3Zorn.traceBilin (H3Zorn.crossProduct y z) v • u -
          H3Zorn.crossProduct (H3Zorn.crossProduct u z) (H3Zorn.crossProduct v y)) +
        (1 / 2 : ℝ) • (H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z +
          H3Zorn.traceBilin (H3Zorn.crossProduct y z) u • v -
          H3Zorn.crossProduct (H3Zorn.crossProduct v z) (H3Zorn.crossProduct u y)) +
        (1 / 2 : ℝ) • (H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z +
          H3Zorn.traceBilin (H3Zorn.crossProduct u v) z • y -
          H3Zorn.crossProduct (H3Zorn.crossProduct y z) (H3Zorn.crossProduct u v)) =
      (1 / 2 : ℝ) • (3 • (H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z) +
          (H3Zorn.traceBilin (H3Zorn.crossProduct u v) z • y +
            H3Zorn.traceBilin (H3Zorn.crossProduct y z) u • v +
            H3Zorn.traceBilin (H3Zorn.crossProduct y z) v • u) -
          (H3Zorn.crossProduct (H3Zorn.crossProduct u z) (H3Zorn.crossProduct v y) +
            H3Zorn.crossProduct (H3Zorn.crossProduct v z) (H3Zorn.crossProduct u y) +
            H3Zorn.crossProduct (H3Zorn.crossProduct y z) (H3Zorn.crossProduct u v))) := by
    module
  rw [hsum, hcross_eq]
  module

/-- Polarized McCrimmon identity (12) in `tripleD` form (cross product in first slot). -/
theorem polarized_mccrimmon_12_tripleD (u v y z : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ (H3Zorn.crossProduct u v) y z +
      JordanTKK.tripleD ℝ (H3Zorn.crossProduct u y) v z +
      JordanTKK.tripleD ℝ (H3Zorn.crossProduct v y) u z =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y • z := by
  have h_op :
      h3zornTraceAdjoint (JordanTKK.tripleD ℝ u (H3Zorn.crossProduct v y) +
        JordanTKK.tripleD ℝ v (H3Zorn.crossProduct u y) +
        JordanTKK.tripleD ℝ y (H3Zorn.crossProduct u v)) =
      h3zornTraceAdjoint (H3Zorn.traceBilin (H3Zorn.crossProduct u v) y •
        (LinearMap.id : Module.End ℝ (H3Zorn ℝ))) := by
    congr 1
    apply LinearMap.ext
    intro w
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact polarized_mccrimmon_12_tripleD_right u v y w
  have hadj_sum :
      h3zornTraceAdjoint (JordanTKK.tripleD ℝ u (H3Zorn.crossProduct v y) +
        JordanTKK.tripleD ℝ v (H3Zorn.crossProduct u y) +
        JordanTKK.tripleD ℝ y (H3Zorn.crossProduct u v)) =
      JordanTKK.tripleD ℝ (H3Zorn.crossProduct v y) u +
        JordanTKK.tripleD ℝ (H3Zorn.crossProduct u y) v +
        JordanTKK.tripleD ℝ (H3Zorn.crossProduct u v) y := by
    change h3zornTraceAdjointLM _ = _
    simp only [map_add, h3zornTraceAdjointLM_apply]
    have ha1 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ u (H3Zorn.crossProduct v y)) =
        JordanTKK.tripleD ℝ (H3Zorn.crossProduct v y) u :=
      h3zornTKKDatum.adj_tripleD u (H3Zorn.crossProduct v y)
    have ha2 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ v (H3Zorn.crossProduct u y)) =
        JordanTKK.tripleD ℝ (H3Zorn.crossProduct u y) v :=
      h3zornTKKDatum.adj_tripleD v (H3Zorn.crossProduct u y)
    have ha3 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ y (H3Zorn.crossProduct u v)) =
        JordanTKK.tripleD ℝ (H3Zorn.crossProduct u v) y :=
      h3zornTKKDatum.adj_tripleD y (H3Zorn.crossProduct u v)
    rw [ha1, ha2, ha3]
  have hadj_rhs :
      h3zornTraceAdjoint (H3Zorn.traceBilin (H3Zorn.crossProduct u v) y •
        (LinearMap.id : Module.End ℝ (H3Zorn ℝ))) =
      H3Zorn.traceBilin (H3Zorn.crossProduct u v) y •
        (LinearMap.id : Module.End ℝ (H3Zorn ℝ)) := by
    change h3zornTraceAdjointLM _ = _
    rw [map_smul, h3zornTraceAdjointLM_apply, h3zornTraceAdjoint_id]
  rw [hadj_sum, hadj_rhs] at h_op
  have hz := congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f z) h_op
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hz
  rw [← hz]
  abel

end JordanTripleBridge

/-! ## 3. 56-Dimensional `H3ZornTKKLie` Representation `repE7` on `Charge` -/

section RepE7

/-- Linear trace functional `T₀ ↦ linearTrace (T₀.1 1)` on the 79D structure algebra. -/
def strTrace : h3zornTKKDatum.str →ₗ[ℝ] ℝ where
  toFun T₀ := H3Zorn.linearTrace (T₀.1 1)
  map_add' T₁ T₂ := by
    change H3Zorn.linearTrace (T₁.1 1 + T₂.1 1) = _
    exact H3Zorn.linearTrace_add _ _
  map_smul' r T₀ := by
    change H3Zorn.linearTrace (r • T₀.1 1) = _
    exact H3Zorn.linearTrace_smul r _

@[simp] theorem strTrace_apply (T₀ : h3zornTKKDatum.str) :
    strTrace T₀ = H3Zorn.linearTrace (T₀.1 1) := rfl

theorem strTrace_comm_eq_zero (T₁ T₂ : h3zornTKKDatum.str) :
    strTrace ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩ = 0 := by
  rcases h3zornTKKDatum.str_decomp T₁.1 T₁.2 with ⟨D₁, a₁, hT₁⟩
  rcases h3zornTKKDatum.str_decomp T₂.1 T₂.2 with ⟨D₂, a₂, hT₂⟩
  let E₁ : H3ZornF4Derivations := ⟨D₁.1, D₁.2⟩
  let E₂ : H3ZornF4Derivations := ⟨D₂.1, D₂.2⟩
  have hcomm : T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1 =
      ⁅structureOperator E₁ a₁, structureOperator E₂ a₂⁆ := by
    rw [hT₁, hT₂]
    rfl
  change H3Zorn.linearTrace ((T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1) 1) = 0
  rw [hcomm, structureOperator_lie_formula]
  simp only [LinearMap.add_apply, jordanLmul_apply]
  rw [H3Zorn.linearTrace_add, H3Zorn.linearTrace_add]
  have h1 : H3Zorn.linearTrace (⁅(E₁ : Operator), (E₂ : Operator)⁆ (1 : H3Zorn ℝ)) = 0 :=
    h3ZornF4_derivation_linearTrace_zero ⁅E₁, E₂⁆ 1
  have h2 : H3Zorn.linearTrace
      ((h3ZornJordanInnerDerivation a₁ a₂ : Operator) (1 : H3Zorn ℝ)) = 0 :=
    h3ZornF4_derivation_linearTrace_zero (h3ZornJordanInnerDerivation a₁ a₂) 1
  have h3 : H3Zorn.linearTrace (((E₁ : Operator) a₂ - (E₂ : Operator) a₁) * (1 : H3Zorn ℝ)) = 0 := by
    change H3Zorn.linearTrace (candidateJordanMul ((E₁ : Operator) a₂ - (E₂ : Operator) a₁) 1) = 0
    rw [candidateJordanMul_one_right]
    have hs : (E₁ : Operator) a₂ - (E₂ : Operator) a₁ =
        (E₁ : Operator) a₂ + (-1 : ℝ) • (E₂ : Operator) a₁ := by module
    rw [hs, H3Zorn.linearTrace_add, H3Zorn.linearTrace_smul,
      h3ZornF4_derivation_linearTrace_zero E₁ a₂,
      h3ZornF4_derivation_linearTrace_zero E₂ a₁, mul_zero, add_zero]
  rw [h1, h2, h3, add_zero, add_zero]

theorem strTrace_tripleD (x y : H3Zorn ℝ) :
    strTrace ⟨JordanTKK.tripleD ℝ x y, h3zornTKKDatum.tripleD_mem_str x y⟩ =
      H3Zorn.traceBilin x y := by
  exact linearTrace_tripleD_apply_one x y

/-- Action of grade `0` (`h3zornTKKDatum.str`) on `Charge`. -/
def repZero : h3zornTKKDatum.str →ₗ[ℝ] Module.End ℝ Charge where
  toFun T₀ :=
    { toFun := fun Q =>
        { alpha := ((1 / 2 : ℝ) * strTrace T₀) * Q.alpha
          beta := -((1 / 2 : ℝ) * strTrace T₀) * Q.beta
          x := T₀.1 Q.x - ((1 / 2 : ℝ) * strTrace T₀) • Q.x
          y := -(h3zornTraceAdjoint T₀.1 Q.y) + ((1 / 2 : ℝ) * strTrace T₀) • Q.y }
      map_add' Q₁ Q₂ := by
        apply FreudenthalCharge.ext <;> simp only [alpha_add, beta_add, x_add, y_add,
          map_add, smul_add]
        · ring
        · ring
        · module
        · module
      map_smul' r Q := by
        apply FreudenthalCharge.ext <;> simp only [alpha_smul, beta_smul, x_smul, y_smul,
          map_smul, RingHom.id_apply, smul_neg, smul_sub, smul_add, smul_smul]
        · ring
        · ring
        · rw [mul_comm r]
        · rw [mul_comm r] }
  map_add' T₁ T₂ := by
    apply LinearMap.ext; intro Q
    apply FreudenthalCharge.ext <;> simp only [LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply, Submodule.coe_add, map_add, alpha_add, beta_add, x_add, y_add]
    · ring
    · ring
    · module
    · change -(h3zornTraceAdjointLM (T₁.1 + T₂.1) Q.y) + _ = _
      rw [map_add, LinearMap.add_apply, h3zornTraceAdjointLM_apply,
        h3zornTraceAdjointLM_apply]
      module
  map_smul' r T₀ := by
    apply LinearMap.ext; intro Q
    apply FreudenthalCharge.ext <;> simp only [LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply,
      alpha_smul, beta_smul, x_smul, y_smul]
    · ring
    · ring
    · rw [smul_sub, smul_smul,
        show (1 / 2 : ℝ) * (r * strTrace T₀) = r * ((1 / 2 : ℝ) * strTrace T₀) by ring]
    · change -(h3zornTraceAdjointLM (r • T₀.1) Q.y) + _ = _
      rw [map_smul, LinearMap.smul_apply, h3zornTraceAdjointLM_apply, smul_add,
        smul_neg, smul_smul,
        show (1 / 2 : ℝ) * (r * strTrace T₀) = r * ((1 / 2 : ℝ) * strTrace T₀) by ring]

/-- Action of grade `-1` (`H3Zorn ℝ`) on `Charge`. -/
def repNeg : H3Zorn ℝ →ₗ[ℝ] Module.End ℝ Charge where
  toFun B :=
    { toFun := fun Q =>
        (1 / 2 : ℝ) •
          { alpha := H3Zorn.traceBilin B Q.y
            beta := 0
            x := Q.beta • B
            y := -H3Zorn.crossProduct B Q.x }
      map_add' Q₁ Q₂ := by
        apply FreudenthalCharge.ext <;>
          simp only [alpha_add, beta_add, x_add, y_add, alpha_smul, beta_smul, x_smul, y_smul,
            H3Zorn.traceBilin_add_right, H3Zorn.crossProduct_add_right]
        · ring
        · ring
        · rw [add_smul, smul_add]
        · module
      map_smul' r Q := by
        apply FreudenthalCharge.ext <;>
          simp only [alpha_smul, beta_smul, x_smul, y_smul, RingHom.id_apply,
            H3Zorn.traceBilin_smul_right, H3Zorn.crossProduct_smul_right]
        · ring
        · ring
        · rw [smul_smul, smul_smul, smul_smul]; congr 1; ring
        · rw [smul_neg, smul_neg, smul_neg, smul_smul, smul_smul, mul_comm r] }
  map_add' B₁ B₂ := by
    apply LinearMap.ext; intro Q
    apply FreudenthalCharge.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        alpha_add, beta_add, x_add, y_add, alpha_smul, beta_smul, x_smul, y_smul,
        H3Zorn.traceBilin_add_left, H3Zorn.crossProduct_add_left]
    · ring
    · ring
    · rw [smul_add, smul_add]
    · module
  map_smul' r B := by
    apply LinearMap.ext; intro Q
    apply FreudenthalCharge.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
        alpha_smul, beta_smul, x_smul, y_smul,
        H3Zorn.traceBilin_smul_left, H3Zorn.crossProduct_smul_left]
    · ring
    · ring
    · rw [smul_smul, smul_smul, smul_smul, smul_smul]; congr 1; ring
    · rw [smul_neg, smul_neg, smul_neg, smul_smul, smul_smul, mul_comm r]

/-- Action of grade `+1` (`H3Zorn ℝ`) on `Charge`. -/
def repPos : H3Zorn ℝ →ₗ[ℝ] Module.End ℝ Charge where
  toFun A :=
    { toFun := fun Q =>
        { alpha := 0
          beta := H3Zorn.traceBilin A Q.x
          x := -H3Zorn.crossProduct A Q.y
          y := Q.alpha • A }
      map_add' Q₁ Q₂ := by
        apply FreudenthalCharge.ext <;>
          simp only [alpha_add, beta_add, x_add, y_add,
            H3Zorn.traceBilin_add_right, H3Zorn.crossProduct_add_right]
        · ring
        · module
        · rw [add_smul]
      map_smul' r Q := by
        apply FreudenthalCharge.ext <;>
          simp only [alpha_smul, beta_smul, x_smul, y_smul, RingHom.id_apply,
            H3Zorn.traceBilin_smul_right, H3Zorn.crossProduct_smul_right]
        · ring
        · module
        · rw [smul_smul] }
  map_add' A₁ A₂ := by
    apply LinearMap.ext; intro Q
    apply FreudenthalCharge.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        alpha_add, beta_add, x_add, y_add,
        H3Zorn.traceBilin_add_left, H3Zorn.crossProduct_add_left]
    · ring
    · module
    · rw [smul_add]
  map_smul' r A := by
    apply LinearMap.ext; intro Q
    apply FreudenthalCharge.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
        alpha_smul, beta_smul, x_smul, y_smul,
        H3Zorn.traceBilin_smul_left, H3Zorn.crossProduct_smul_left]
    · ring
    · module
    · rw [smul_smul, smul_smul, mul_comm r]

/-- Linear map sending `H3ZornTKKLie` into `Module.End ℝ Charge`. -/
def repE7LM : H3ZornTKKLie →ₗ[ℝ] Module.End ℝ Charge :=
  repNeg.comp projNeg + repZero.comp projZero + repPos.comp projPos

private theorem repNeg_lie_repNeg (B₁ B₂ : H3Zorn ℝ) :
    ⁅repNeg B₁, repNeg B₂⁆ = 0 := by
  apply LinearMap.ext; intro Q
  change repNeg B₁ (repNeg B₂ Q) - repNeg B₂ (repNeg B₁ Q) = 0
  apply FreudenthalCharge.ext <;>
    simp only [repNeg, LinearMap.coe_mk, AddHom.coe_mk, charge_sub_alpha, charge_sub_beta,
      charge_sub_x, charge_sub_y, alpha_smul, beta_smul, x_smul, y_smul,
      charge_zero_alpha, charge_zero_beta, charge_zero_x, charge_zero_y,
      h3_traceBilin_neg_right, H3Zorn.traceBilin_smul_right, H3Zorn.crossProduct_smul_right,
      mul_zero, smul_zero, zero_smul, sub_zero]
  · rw [← H3Zorn.traceBilin_crossProduct_assoc B₁ B₂ Q.x,
      ← H3Zorn.traceBilin_crossProduct_assoc B₂ B₁ Q.x,
      H3Zorn.crossProduct_symm B₂ B₁]
    ring
  · rw [H3Zorn.crossProduct_symm B₂ B₁]
    module

private theorem repPos_lie_repPos (A₁ A₂ : H3Zorn ℝ) :
    ⁅repPos A₁, repPos A₂⁆ = 0 := by
  apply LinearMap.ext; intro Q
  change repPos A₁ (repPos A₂ Q) - repPos A₂ (repPos A₁ Q) = 0
  apply FreudenthalCharge.ext <;>
    simp only [repPos, LinearMap.coe_mk, AddHom.coe_mk, charge_sub_alpha, charge_sub_beta,
      charge_sub_x, charge_sub_y, charge_zero_alpha, charge_zero_beta, charge_zero_x,
      charge_zero_y, h3_traceBilin_neg_right, H3Zorn.crossProduct_smul_right,
      zero_smul, sub_zero]
  · rw [← H3Zorn.traceBilin_crossProduct_assoc A₁ A₂ Q.y,
      ← H3Zorn.traceBilin_crossProduct_assoc A₂ A₁ Q.y,
      H3Zorn.crossProduct_symm A₂ A₁]
    ring
  · rw [H3Zorn.crossProduct_symm A₂ A₁]
    module

private theorem repZero_lie_repZero (T₁ T₂ : h3zornTKKDatum.str) :
    ⁅repZero T₁, repZero T₂⁆ =
      repZero ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩ := by
  apply LinearMap.ext; intro Q
  change repZero T₁ (repZero T₂ Q) - repZero T₂ (repZero T₁ Q) = _
  have htr : strTrace ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩ = 0 :=
    strTrace_comm_eq_zero T₁ T₂
  apply FreudenthalCharge.ext <;>
    simp only [repZero, LinearMap.coe_mk, AddHom.coe_mk, htr, mul_zero, zero_mul, zero_smul,
      sub_zero, add_zero, charge_sub_alpha, charge_sub_beta, charge_sub_x, charge_sub_y,
      map_sub, map_add, map_neg, map_smul, LinearMap.sub_apply, LinearMap.comp_apply]
  · ring
  · ring
  · module
  · change -(-(h3zornTraceAdjoint T₁.1 (h3zornTraceAdjoint T₂.1 Q.y)) +
        ((1 / 2 : ℝ) * strTrace T₂) • h3zornTraceAdjoint T₁.1 Q.y) +
      ((1 / 2 : ℝ) * strTrace T₁) • (-(h3zornTraceAdjoint T₂.1 Q.y) +
        ((1 / 2 : ℝ) * strTrace T₂) • Q.y) -
      (-(-(h3zornTraceAdjoint T₂.1 (h3zornTraceAdjoint T₁.1 Q.y)) +
        ((1 / 2 : ℝ) * strTrace T₁) • h3zornTraceAdjoint T₂.1 Q.y) +
      ((1 / 2 : ℝ) * strTrace T₂) • (-(h3zornTraceAdjoint T₁.1 Q.y) +
        ((1 / 2 : ℝ) * strTrace T₁) • Q.y)) =
      -(h3zornTraceAdjointLM (T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1) Q.y)
    rw [map_sub, LinearMap.sub_apply, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjoint_comp T₁.1 T₂.1, h3zornTraceAdjoint_comp T₂.1 T₁.1,
      LinearMap.comp_apply, LinearMap.comp_apply]
    module

private theorem repZero_lie_repNeg (T₀ : h3zornTKKDatum.str) (B : H3Zorn ℝ) :
    ⁅repZero T₀, repNeg B⁆ = repNeg (T₀.1 B) := by
  apply LinearMap.ext; intro Q
  change repZero T₀ (repNeg B Q) - repNeg B (repZero T₀ Q) = repNeg (T₀.1 B) Q
  apply FreudenthalCharge.ext <;>
    simp only [repZero, repNeg, LinearMap.coe_mk, AddHom.coe_mk,
      charge_sub_alpha, charge_sub_beta, charge_sub_x, charge_sub_y,
      alpha_smul, beta_smul, x_smul, y_smul, map_smul, map_neg,
      H3Zorn.traceBilin_add_right, h3_traceBilin_neg_right, H3Zorn.traceBilin_smul_right,
      mul_zero, sub_zero]
  · rw [H3Zorn.traceBilin_symm B (h3zornTraceAdjoint T₀.1 Q.y),
      h3zornTraceAdjoint_pair T₀.1 Q.y B, H3Zorn.traceBilin_symm Q.y (T₀.1 B)]
    ring
  · simp only [smul_sub, smul_smul]
    rw [show (1 / 2 : ℝ) * (1 / 2 * strTrace T₀ * Q.beta) =
        -(1 / 2 * (-(1 / 2 * strTrace T₀) * Q.beta)) by ring]
    module
  · have hcr := congrArg (fun w : H3Zorn ℝ => (1 / 2 : ℝ) • w) (str_crossProduct_rule T₀ B Q.x)
    simp only [smul_add] at hcr
    change (1 / 2 : ℝ) • h3zornTraceAdjoint T₀.1 (H3Zorn.crossProduct B Q.x) +
        (1 / 2 : ℝ) • H3Zorn.crossProduct (T₀.1 B) Q.x +
        (1 / 2 : ℝ) • H3Zorn.crossProduct B (T₀.1 Q.x) =
      (1 / 2 : ℝ) • strTrace T₀ • H3Zorn.crossProduct B Q.x at hcr
    have hcr' :
        (1 / 2 : ℝ) • h3zornTraceAdjoint T₀.1 (H3Zorn.crossProduct B Q.x) +
          (1 / 2 : ℝ) • H3Zorn.crossProduct B (T₀.1 Q.x) -
          (1 / 2 : ℝ) • strTrace T₀ • H3Zorn.crossProduct B Q.x =
        (1 / 2 : ℝ) • (-H3Zorn.crossProduct (T₀.1 B) Q.x) := by
      have h := congrArg (fun w : H3Zorn ℝ =>
        w - (1 / 2 : ℝ) • strTrace T₀ • H3Zorn.crossProduct B Q.x -
          (1 / 2 : ℝ) • H3Zorn.crossProduct (T₀.1 B) Q.x) hcr
      convert h using 1 <;> module
    rw [show T₀.1 Q.x - ((1 / 2 : ℝ) * strTrace T₀) • Q.x =
        T₀.1 Q.x + (-((1 / 2 : ℝ) * strTrace T₀)) • Q.x by module,
      H3Zorn.crossProduct_add_right, H3Zorn.crossProduct_smul_right, ← hcr']
    module

private theorem repZero_lie_repPos (T₀ : h3zornTKKDatum.str) (A : H3Zorn ℝ) :
    ⁅repZero T₀, repPos A⁆ = repPos (-h3zornTraceAdjoint T₀.1 A) := by
  apply LinearMap.ext; intro Q
  change repZero T₀ (repPos A Q) - repPos A (repZero T₀ Q) = repPos (-h3zornTraceAdjoint T₀.1 A) Q
  apply FreudenthalCharge.ext <;>
    simp only [repZero, repPos, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.neg_apply,
      charge_neg_alpha, charge_neg_beta, charge_neg_x, charge_neg_y,
      charge_sub_alpha, charge_sub_beta, charge_sub_x, charge_sub_y,
      map_neg, map_smul, mul_zero, neg_zero, neg_neg,
      H3Zorn.traceBilin_sub_right, H3Zorn.traceBilin_smul_right,
      H3Zorn.crossProduct_add_right, H3Zorn.crossProduct_smul_right, sub_zero]
  · rw [← h3zornTraceAdjoint_pair T₀.1 A Q.x]
    ring
  · have hcr := congrArg (fun w : H3Zorn ℝ => -w) (str_crossProduct_rule_adj T₀ A Q.y)
    change -(T₀.1 (H3Zorn.crossProduct A Q.y) +
        H3Zorn.crossProduct (h3zornTraceAdjoint T₀.1 A) Q.y +
        H3Zorn.crossProduct A (h3zornTraceAdjoint T₀.1 Q.y)) =
      -(strTrace T₀ • H3Zorn.crossProduct A Q.y) at hcr
    have hcr' :
        -(T₀.1 (H3Zorn.crossProduct A Q.y)) -
          H3Zorn.crossProduct A (h3zornTraceAdjoint T₀.1 Q.y) +
          strTrace T₀ • H3Zorn.crossProduct A Q.y =
        H3Zorn.crossProduct (h3zornTraceAdjoint T₀.1 A) Q.y := by
      have h := congrArg (fun w : H3Zorn ℝ =>
        w + strTrace T₀ • H3Zorn.crossProduct A Q.y +
          H3Zorn.crossProduct (h3zornTraceAdjoint T₀.1 A) Q.y) hcr
      convert h using 1 <;> module
    rw [← hcr']
    simp only [h3_crossProduct_neg_right]
    module
  · rw [smul_smul]
    module

private theorem repNeg_lie_repPos (B A : H3Zorn ℝ) :
    ⁅repNeg B, repPos A⁆ =
      repZero ⟨JordanTKK.tripleD ℝ B A, h3zornTKKDatum.tripleD_mem_str B A⟩ := by
  apply LinearMap.ext; intro Q
  change repNeg B (repPos A Q) - repPos A (repNeg B Q) = _
  have htr : strTrace ⟨JordanTKK.tripleD ℝ B A, h3zornTKKDatum.tripleD_mem_str B A⟩ =
      H3Zorn.traceBilin B A :=
    strTrace_tripleD B A
  apply FreudenthalCharge.ext <;>
    simp only [repNeg, repPos, repZero, LinearMap.coe_mk, AddHom.coe_mk, htr,
      charge_sub_alpha, charge_sub_beta, charge_sub_x, charge_sub_y,
      alpha_smul, beta_smul, x_smul, y_smul,
      H3Zorn.traceBilin_smul_right, H3Zorn.crossProduct_smul_right, h3_crossProduct_neg_right,
      mul_zero, zero_sub, sub_zero]
  · rw [H3Zorn.traceBilin_symm B A]
    ring
  · rw [H3Zorn.traceBilin_symm B A]
    ring
  · rw [tripleD_apply_expanded B A Q.x, H3Zorn.crossProduct_symm A (H3Zorn.crossProduct B Q.x),
      H3Zorn.traceBilin_symm Q.x A]
    module
  · have hadj : h3zornTraceAdjoint (JordanTKK.tripleD ℝ B A) Q.y =
        JordanTKK.tripleD ℝ A B Q.y :=
      congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f Q.y) (h3zornTKKDatum.adj_tripleD B A)
    rw [hadj, tripleD_apply_expanded A B Q.y,
      H3Zorn.crossProduct_symm B (H3Zorn.crossProduct A Q.y), H3Zorn.traceBilin_symm A B,
      H3Zorn.traceBilin_symm Q.y B]
    module

/-- Exact 56-dimensional Lie algebra representation `repE7 : H3ZornTKKLie →ₗ⁅ℝ⁆ Module.End ℝ Charge`. -/
def repE7 : H3ZornTKKLie →ₗ⁅ℝ⁆ Module.End ℝ Charge where
  toLinearMap := repE7LM
  map_lie' {X Y} := by
    have hrep_neg : ∀ x : H3Zorn ℝ, repE7LM (negInj x) = repNeg x := fun x => by
      change repNeg (projNeg (negInj x)) + repZero (projZero (negInj x)) +
          repPos (projPos (negInj x)) = repNeg x
      rw [show projNeg (negInj x) = x from rfl, show projZero (negInj x) = 0 from rfl,
        show projPos (negInj x) = 0 from rfl, map_zero, map_zero, add_zero, add_zero]
    have hrep_zero : ∀ T : h3zornTKKDatum.str, repE7LM (zeroInj T) = repZero T := fun T => by
      change repNeg (projNeg (zeroInj T)) + repZero (projZero (zeroInj T)) +
          repPos (projPos (zeroInj T)) = repZero T
      rw [show projNeg (zeroInj T) = 0 from rfl, show projZero (zeroInj T) = T from rfl,
        show projPos (zeroInj T) = 0 from rfl, map_zero, map_zero, zero_add, add_zero]
    have hrep_pos : ∀ y : H3Zorn ℝ, repE7LM (posInj y) = repPos y := fun y => by
      change repNeg (projNeg (posInj y)) + repZero (projZero (posInj y)) +
          repPos (projPos (posInj y)) = repPos y
      rw [show projNeg (posInj y) = 0 from rfl, show projZero (posInj y) = 0 from rfl,
        show projPos (posInj y) = y from rfl, map_zero, map_zero, zero_add, zero_add]
    have hX : X = negInj X.neg + zeroInj X.zero + posInj X.pos :=
      JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X
    have hY : Y = negInj Y.neg + zeroInj Y.zero + posInj Y.pos :=
      JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) Y
    have hneg_zero : ⁅repNeg X.neg, repZero Y.zero⁆ = repNeg (-Y.zero.1 X.neg) := by
      rw [← lie_skew, repZero_lie_repNeg, ← map_neg]
    have hpos_zero : ⁅repPos X.pos, repZero Y.zero⁆ = repPos (h3zornTraceAdjoint Y.zero.1 X.pos) := by
      rw [← lie_skew, repZero_lie_repPos, ← map_neg, neg_neg]
    have hpos_neg : ⁅repPos X.pos, repNeg Y.neg⁆ =
        repZero ⟨-JordanTKK.tripleD ℝ Y.neg X.pos,
          h3zornTKKDatum.str.neg_mem (h3zornTKKDatum.tripleD_mem_str Y.neg X.pos)⟩ := by
      rw [← lie_skew, repNeg_lie_repPos, ← map_neg]
      rfl
    change repE7LM ⁅X, Y⁆ = ⁅repE7LM X, repE7LM Y⁆
    rw [hX, hY]
    simp only [map_add, add_lie, lie_add, hrep_neg, hrep_zero, hrep_pos,
      negInj_bracket_negInj, negInj_bracket_zeroInj, negInj_bracket_posInj,
      zeroInj_bracket_negInj, zeroInj_bracket_zeroInj, zeroInj_bracket_posInj,
      posInj_bracket_negInj, posInj_bracket_zeroInj, posInj_bracket_posInj,
      map_zero, repNeg_lie_repNeg, repPos_lie_repPos, repZero_lie_repZero,
      repZero_lie_repNeg, repZero_lie_repPos, repNeg_lie_repPos,
      hneg_zero, hpos_zero, hpos_neg]

@[simp] theorem repE7_negInj (B : H3Zorn ℝ) : repE7 (negInj B) = repNeg B := by
  change repNeg (projNeg (negInj B)) + repZero (projZero (negInj B)) +
      repPos (projPos (negInj B)) = repNeg B
  rw [show projNeg (negInj B) = B from rfl, show projZero (negInj B) = 0 from rfl,
    show projPos (negInj B) = 0 from rfl, map_zero, map_zero, add_zero, add_zero]

@[simp] theorem repE7_zeroInj (T₀ : h3zornTKKDatum.str) : repE7 (zeroInj T₀) = repZero T₀ := by
  change repNeg (projNeg (zeroInj T₀)) + repZero (projZero (zeroInj T₀)) +
      repPos (projPos (zeroInj T₀)) = repZero T₀
  rw [show projNeg (zeroInj T₀) = 0 from rfl, show projZero (zeroInj T₀) = T₀ from rfl,
    show projPos (zeroInj T₀) = 0 from rfl, map_zero, map_zero, zero_add, add_zero]

@[simp] theorem repE7_posInj (A : H3Zorn ℝ) : repE7 (posInj A) = repPos A := by
  change repNeg (projNeg (posInj A)) + repZero (projZero (posInj A)) +
      repPos (projPos (posInj A)) = repPos A
  rw [show projNeg (posInj A) = 0 from rfl, show projZero (posInj A) = 0 from rfl,
    show projPos (posInj A) = A from rfl, map_zero, map_zero, zero_add, zero_add]

@[simp] theorem repE7_alpha (X : H3ZornTKKLie) (Q : Charge) :
    (repE7 X Q).alpha =
      (1 / 2 : ℝ) * H3Zorn.traceBilin X.neg Q.y +
        ((1 / 2 : ℝ) * strTrace X.zero) * Q.alpha := by
  have hX : X = negInj X.neg + zeroInj X.zero + posInj X.pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X
  nth_rw 1 [hX]
  simp only [map_add, LinearMap.add_apply, repE7_negInj, repE7_zeroInj, repE7_posInj,
    alpha_add]
  simp only [repNeg, repZero, repPos, LinearMap.coe_mk, AddHom.coe_mk, alpha_smul]
  ring

@[simp] theorem repE7_beta (X : H3ZornTKKLie) (Q : Charge) :
    (repE7 X Q).beta =
      H3Zorn.traceBilin X.pos Q.x - ((1 / 2 : ℝ) * strTrace X.zero) * Q.beta := by
  have hX : X = negInj X.neg + zeroInj X.zero + posInj X.pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X
  nth_rw 1 [hX]
  simp only [map_add, LinearMap.add_apply, repE7_negInj, repE7_zeroInj, repE7_posInj,
    beta_add]
  simp only [repNeg, repZero, repPos, LinearMap.coe_mk, AddHom.coe_mk, beta_smul]
  ring

@[simp] theorem repE7_x (X : H3ZornTKKLie) (Q : Charge) :
    (repE7 X Q).x =
      (1 / 2 : ℝ) • (Q.beta • X.neg) +
        (X.zero.1 Q.x - ((1 / 2 : ℝ) * strTrace X.zero) • Q.x) -
        H3Zorn.crossProduct X.pos Q.y := by
  have hX : X = negInj X.neg + zeroInj X.zero + posInj X.pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X
  nth_rw 1 [hX]
  simp only [map_add, LinearMap.add_apply, repE7_negInj, repE7_zeroInj, repE7_posInj,
    x_add]
  simp only [repNeg, repZero, repPos, LinearMap.coe_mk, AddHom.coe_mk, x_smul]
  module

@[simp] theorem repE7_y (X : H3ZornTKKLie) (Q : Charge) :
    (repE7 X Q).y =
      (1 / 2 : ℝ) • (-H3Zorn.crossProduct X.neg Q.x) +
        (-(h3zornTraceAdjoint X.zero.1 Q.y) + ((1 / 2 : ℝ) * strTrace X.zero) • Q.y) +
        Q.alpha • X.pos := by
  have hX : X = negInj X.neg + zeroInj X.zero + posInj X.pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X
  nth_rw 1 [hX]
  simp only [map_add, LinearMap.add_apply, repE7_negInj, repE7_zeroInj, repE7_posInj,
    y_add]
  simp only [repNeg, repZero, repPos, LinearMap.coe_mk, AddHom.coe_mk, y_smul]

/-- Skew-symmetry of `repE7` with respect to `symplecticForm`. -/
theorem repE7_symplecticForm_skew (X : H3ZornTKKLie) (Q₁ Q₂ : Charge) :
    symplecticForm (repE7 X Q₁) Q₂ + symplecticForm Q₁ (repE7 X Q₂) = 0 := by
  rw [symplecticForm_expanded, symplecticForm_expanded]
  simp only [repE7_alpha, repE7_beta, repE7_x, repE7_y,
    H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
    H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_sub_right,
    h3_traceBilin_neg_left, h3_traceBilin_neg_right,
    H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
  rw [H3Zorn.traceBilin_symm Q₁.x (h3zornTraceAdjoint X.zero.1 Q₂.y),
    h3zornTraceAdjoint_pair X.zero.1 Q₁.y Q₂.x,
    h3zornTraceAdjoint_pair X.zero.1 Q₂.y Q₁.x,
    H3Zorn.traceBilin_symm Q₁.y (X.zero.1 Q₂.x),
    H3Zorn.traceBilin_symm Q₂.y (X.zero.1 Q₁.x),
    H3Zorn.traceBilin_symm Q₁.y Q₂.x,
    H3Zorn.traceBilin_symm Q₁.y X.neg,
    H3Zorn.traceBilin_symm Q₁.x X.pos,
    H3Zorn.traceBilin_symm Q₁.x (H3Zorn.crossProduct X.neg Q₂.x),
    H3Zorn.traceBilin_crossProduct_assoc X.neg Q₁.x Q₂.x,
    H3Zorn.traceBilin_crossProduct_assoc X.neg Q₂.x Q₁.x,
    H3Zorn.crossProduct_symm Q₂.x Q₁.x,
    H3Zorn.traceBilin_symm Q₁.y (H3Zorn.crossProduct X.pos Q₂.y),
    H3Zorn.traceBilin_crossProduct_assoc X.pos Q₁.y Q₂.y,
    H3Zorn.traceBilin_crossProduct_assoc X.pos Q₂.y Q₁.y,
    H3Zorn.crossProduct_symm Q₂.y Q₁.y]
  ring

/-- Polynomial directional derivative of `quarticInvariant` at `Q` in direction `V`. -/
def quarticDeriv (Q V : Charge) : ℝ :=
  2 * (Q.alpha * Q.beta - H3Zorn.traceBilin Q.x Q.y) *
      (V.alpha * Q.beta + Q.alpha * V.beta -
        H3Zorn.traceBilin V.x Q.y - H3Zorn.traceBilin Q.x V.y) -
    4 * (V.alpha * H3Zorn.normCubic Q.x +
      Q.alpha * H3Zorn.traceBilin (H3Zorn.adjointQuad Q.x) V.x +
      V.beta * H3Zorn.normCubic Q.y +
      Q.beta * H3Zorn.traceBilin (H3Zorn.adjointQuad Q.y) V.y +
      H3Zorn.traceBilin (H3Zorn.crossProduct Q.x V.x) (H3Zorn.adjointQuad Q.y) +
      H3Zorn.traceBilin (H3Zorn.adjointQuad Q.x) (H3Zorn.crossProduct Q.y V.y))

private theorem normCubic_add_smul_line (x v : H3Zorn ℝ) (t : ℝ) :
    H3Zorn.normCubic (x + t • v) =
      H3Zorn.normCubic x +
        t * H3Zorn.traceBilin (H3Zorn.adjointQuad x) v +
        t ^ 2 * H3Zorn.traceBilin (H3Zorn.adjointQuad v) x +
        t ^ 3 * H3Zorn.normCubic v := by
  rw [H3Zorn.normCubic_add, H3Zorn.adjointQuad_smul, H3Zorn.normCubic_smul,
    H3Zorn.traceBilin_smul_right, H3Zorn.traceBilin_smul_left]
  ring

private theorem adjointQuad_add_smul_line (x v : H3Zorn ℝ) (t : ℝ) :
    H3Zorn.adjointQuad (x + t • v) =
      H3Zorn.adjointQuad x +
        t • H3Zorn.crossProduct x v +
        t ^ 2 • H3Zorn.adjointQuad v := by
  have hadj : H3Zorn.adjointQuad (x + t • v) =
      H3Zorn.adjointQuad x + H3Zorn.crossProduct x (t • v) + H3Zorn.adjointQuad (t • v) := by
    simp only [H3Zorn.crossProduct]; abel
  rw [hadj, H3Zorn.crossProduct_smul_right, H3Zorn.adjointQuad_smul]

private theorem hasDerivAt_poly_at_zero (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) :
    HasDerivAt (fun t : ℝ =>
      c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4 + c₅ * t ^ 5 + c₆ * t ^ 6) c₁ 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℕ) * (0 : ℝ) ^ 1) 0 := hasDerivAt_pow 2 0
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3) ((3 : ℕ) * (0 : ℝ) ^ 2) 0 := hasDerivAt_pow 3 0
  have h4 : HasDerivAt (fun t : ℝ => t ^ 4) ((4 : ℕ) * (0 : ℝ) ^ 3) 0 := hasDerivAt_pow 4 0
  have h5 : HasDerivAt (fun t : ℝ => t ^ 5) ((5 : ℕ) * (0 : ℝ) ^ 4) 0 := hasDerivAt_pow 5 0
  have h6 : HasDerivAt (fun t : ℝ => t ^ 6) ((6 : ℕ) * (0 : ℝ) ^ 5) 0 := hasDerivAt_pow 6 0
  have h := ((((((hasDerivAt_const 0 c₀).add (h1.const_mul c₁)).add
    (h2.const_mul c₂)).add (h3.const_mul c₃)).add (h4.const_mul c₄)).add
    (h5.const_mul c₅)).add (h6.const_mul c₆)
  convert h using 1
  norm_num

private theorem hasDerivAt_t_sq_mul {g : ℝ → ℝ} {dg : ℝ} (hg : HasDerivAt g dg 0) :
    HasDerivAt (fun t : ℝ => t ^ 2 * g t) 0 0 := by
  have ht2 : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℕ) * (0 : ℝ) ^ 1) 0 := hasDerivAt_pow 2 0
  have hmul := ht2.mul hg
  convert hmul using 1
  norm_num

private theorem hasDerivAt_poly4_at_zero (c₀ c₁ c₂ c₃ c₄ : ℝ) :
    HasDerivAt (fun t : ℝ => c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3 + c₄ * t ^ 4) c₁ 0 := by
  convert hasDerivAt_poly_at_zero c₀ c₁ c₂ c₃ c₄ 0 0 using 1
  ext t; ring

private theorem hasDerivAt_quarticInvariant_curve (Q V W2 W3 : Charge) :
    HasDerivAt (fun t : ℝ => quarticInvariant (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3))
      (quarticDeriv Q V) 0 := by
  have hd_alpha : HasDerivAt (fun t : ℝ => (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).alpha)
      V.alpha 0 := by
    have hfun : (fun t : ℝ => (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).alpha) =
        fun t : ℝ => Q.alpha + V.alpha * t + W2.alpha * t ^ 2 + W3.alpha * t ^ 3 +
          0 * t ^ 4 + 0 * t ^ 5 + 0 * t ^ 6 := by
      ext t
      simp only [alpha_add, alpha_smul]
      ring
    rw [hfun]
    exact hasDerivAt_poly_at_zero _ _ _ _ _ _ _
  have hd_beta : HasDerivAt (fun t : ℝ => (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).beta)
      V.beta 0 := by
    have hfun : (fun t : ℝ => (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).beta) =
        fun t : ℝ => Q.beta + V.beta * t + W2.beta * t ^ 2 + W3.beta * t ^ 3 +
          0 * t ^ 4 + 0 * t ^ 5 + 0 * t ^ 6 := by
      ext t
      simp only [beta_add, beta_smul]
      ring
    rw [hfun]
    exact hasDerivAt_poly_at_zero _ _ _ _ _ _ _
  have hd_xy : HasDerivAt
      (fun t : ℝ => H3Zorn.traceBilin
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y)
      (H3Zorn.traceBilin V.x Q.y + H3Zorn.traceBilin Q.x V.y) 0 := by
    have hfun : (fun t : ℝ => H3Zorn.traceBilin
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y) =
        fun t : ℝ => H3Zorn.traceBilin Q.x Q.y +
          (H3Zorn.traceBilin V.x Q.y + H3Zorn.traceBilin Q.x V.y) * t +
          (H3Zorn.traceBilin W2.x Q.y + H3Zorn.traceBilin V.x V.y +
            H3Zorn.traceBilin Q.x W2.y) * t ^ 2 +
          (H3Zorn.traceBilin W3.x Q.y + H3Zorn.traceBilin W2.x V.y +
            H3Zorn.traceBilin V.x W2.y + H3Zorn.traceBilin Q.x W3.y) * t ^ 3 +
          (H3Zorn.traceBilin W3.x V.y + H3Zorn.traceBilin W2.x W2.y +
            H3Zorn.traceBilin V.x W3.y) * t ^ 4 +
          (H3Zorn.traceBilin W3.x W2.y + H3Zorn.traceBilin W2.x W3.y) * t ^ 5 +
          H3Zorn.traceBilin W3.x W3.y * t ^ 6 := by
      ext t
      simp only [x_add, x_smul, y_add, y_smul, H3Zorn.traceBilin_add_left,
        H3Zorn.traceBilin_add_right, H3Zorn.traceBilin_smul_left,
        H3Zorn.traceBilin_smul_right]
      ring
    rw [hfun]
    exact hasDerivAt_poly_at_zero _ _ _ _ _ _ _
  have hd_norm : ∀ x v w2 w3 : H3Zorn ℝ,
      HasDerivAt (fun t : ℝ => H3Zorn.normCubic (x + t • v + t ^ 2 • w2 + t ^ 3 • w3))
        (H3Zorn.traceBilin (H3Zorn.adjointQuad x) v) 0 := by
    intro x v w2 w3
    have hline : ∀ t : ℝ,
        H3Zorn.normCubic (x + t • v + t ^ 2 • w2 + t ^ 3 • w3) =
          H3Zorn.normCubic (x + t • v) +
            t ^ 2 * (H3Zorn.traceBilin (H3Zorn.adjointQuad (x + t • v)) (w2 + t • w3) +
              t ^ 2 * H3Zorn.traceBilin (H3Zorn.adjointQuad (w2 + t • w3)) (x + t • v) +
              t ^ 4 * H3Zorn.normCubic (w2 + t • w3)) := by
      intro t
      have hvec : x + t • v + t ^ 2 • w2 + t ^ 3 • w3 =
          (x + t • v) + (t ^ 2) • (w2 + t • w3) := by
        rw [smul_add, smul_smul, show t ^ 2 * t = t ^ 3 by ring]
        abel
      rw [hvec, normCubic_add_smul_line]
      ring
    have hd_g1 : ∃ dg1 : ℝ, HasDerivAt
        (fun t : ℝ => H3Zorn.traceBilin (H3Zorn.adjointQuad (x + t • v)) (w2 + t • w3)) dg1 0 := by
      refine ⟨H3Zorn.traceBilin (H3Zorn.adjointQuad x) w3 +
          H3Zorn.traceBilin (H3Zorn.crossProduct x v) w2, ?_⟩
      have hp1 : (fun t : ℝ => H3Zorn.traceBilin (H3Zorn.adjointQuad (x + t • v)) (w2 + t • w3)) =
          fun t : ℝ =>
            H3Zorn.traceBilin (H3Zorn.adjointQuad x) w2 +
            (H3Zorn.traceBilin (H3Zorn.adjointQuad x) w3 +
              H3Zorn.traceBilin (H3Zorn.crossProduct x v) w2) * t +
            (H3Zorn.traceBilin (H3Zorn.crossProduct x v) w3 +
              H3Zorn.traceBilin (H3Zorn.adjointQuad v) w2) * t ^ 2 +
            H3Zorn.traceBilin (H3Zorn.adjointQuad v) w3 * t ^ 3 + 0 * t ^ 4 := by
        ext t
        rw [adjointQuad_add_smul_line]
        simp only [H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
          H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
        ring
      rw [hp1]
      exact hasDerivAt_poly4_at_zero _ _ _ _ _
    have hd_g2 : ∃ dg2 : ℝ, HasDerivAt
        (fun t : ℝ => H3Zorn.traceBilin (H3Zorn.adjointQuad (w2 + t • w3)) (x + t • v)) dg2 0 := by
      refine ⟨H3Zorn.traceBilin (H3Zorn.adjointQuad w2) v +
          H3Zorn.traceBilin (H3Zorn.crossProduct w2 w3) x, ?_⟩
      have hp2 : (fun t : ℝ => H3Zorn.traceBilin (H3Zorn.adjointQuad (w2 + t • w3)) (x + t • v)) =
          fun t : ℝ =>
            H3Zorn.traceBilin (H3Zorn.adjointQuad w2) x +
            (H3Zorn.traceBilin (H3Zorn.adjointQuad w2) v +
              H3Zorn.traceBilin (H3Zorn.crossProduct w2 w3) x) * t +
            (H3Zorn.traceBilin (H3Zorn.crossProduct w2 w3) v +
              H3Zorn.traceBilin (H3Zorn.adjointQuad w3) x) * t ^ 2 +
            H3Zorn.traceBilin (H3Zorn.adjointQuad w3) v * t ^ 3 + 0 * t ^ 4 := by
        ext t
        rw [adjointQuad_add_smul_line]
        simp only [H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
          H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
        ring
      rw [hp2]
      exact hasDerivAt_poly4_at_zero _ _ _ _ _
    have hd_g3 : ∃ dg3 : ℝ, HasDerivAt (fun t : ℝ => H3Zorn.normCubic (w2 + t • w3)) dg3 0 := by
      refine ⟨H3Zorn.traceBilin (H3Zorn.adjointQuad w2) w3, ?_⟩
      have hp3 : (fun t : ℝ => H3Zorn.normCubic (w2 + t • w3)) =
          fun t : ℝ =>
            H3Zorn.normCubic w2 + H3Zorn.traceBilin (H3Zorn.adjointQuad w2) w3 * t +
            H3Zorn.traceBilin (H3Zorn.adjointQuad w3) w2 * t ^ 2 +
            H3Zorn.normCubic w3 * t ^ 3 + 0 * t ^ 4 := by
        ext t; rw [normCubic_add_smul_line]; ring
      rw [hp3]
      exact hasDerivAt_poly4_at_zero _ _ _ _ _
    obtain ⟨dg1, hg1⟩ := hd_g1
    obtain ⟨dg2, hg2⟩ := hd_g2
    obtain ⟨dg3, hg3⟩ := hd_g3
    have hd_t4 : HasDerivAt (fun t : ℝ => t ^ 4) 0 0 := by
      simpa using hasDerivAt_pow 4 (0 : ℝ)
    have hd_rem : HasDerivAt (fun t : ℝ => t ^ 2 *
        (H3Zorn.traceBilin (H3Zorn.adjointQuad (x + t • v)) (w2 + t • w3) +
          t ^ 2 * H3Zorn.traceBilin (H3Zorn.adjointQuad (w2 + t • w3)) (x + t • v) +
          t ^ 4 * H3Zorn.normCubic (w2 + t • w3))) 0 0 :=
      hasDerivAt_t_sq_mul ((hg1.add (hasDerivAt_t_sq_mul hg2)).add (hd_t4.mul hg3))
    have hd_line : HasDerivAt (fun t : ℝ => H3Zorn.normCubic (x + t • v))
        (H3Zorn.traceBilin (H3Zorn.adjointQuad x) v) 0 := by
      have hfun : (fun t : ℝ => H3Zorn.normCubic (x + t • v)) =
          fun t : ℝ => H3Zorn.normCubic x +
            H3Zorn.traceBilin (H3Zorn.adjointQuad x) v * t +
            H3Zorn.traceBilin (H3Zorn.adjointQuad v) x * t ^ 2 +
            H3Zorn.normCubic v * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5 + 0 * t ^ 6 := by
        ext t; rw [normCubic_add_smul_line]; ring
      rw [hfun]
      exact hasDerivAt_poly_at_zero _ _ _ _ _ _ _
    have hfun_all : (fun t : ℝ => H3Zorn.normCubic (x + t • v + t ^ 2 • w2 + t ^ 3 • w3)) =
        fun t : ℝ => H3Zorn.normCubic (x + t • v) + t ^ 2 *
          (H3Zorn.traceBilin (H3Zorn.adjointQuad (x + t • v)) (w2 + t • w3) +
            t ^ 2 * H3Zorn.traceBilin (H3Zorn.adjointQuad (w2 + t • w3)) (x + t • v) +
            t ^ 4 * H3Zorn.normCubic (w2 + t • w3)) := by
      ext t; exact hline t
    rw [hfun_all]
    convert hd_line.add hd_rem using 1
    norm_num
  have hd_adj_pair :
      HasDerivAt (fun t : ℝ =>
        H3Zorn.traceBilin
          (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x)
          (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y))
        (H3Zorn.traceBilin (H3Zorn.crossProduct Q.x V.x) (H3Zorn.adjointQuad Q.y) +
          H3Zorn.traceBilin (H3Zorn.adjointQuad Q.x) (H3Zorn.crossProduct Q.y V.y)) 0 := by
    have hexp_adj : ∀ (x v w2 w3 : H3Zorn ℝ) (t : ℝ),
        H3Zorn.adjointQuad (x + t • v + t ^ 2 • w2 + t ^ 3 • w3) =
          H3Zorn.adjointQuad x + t • H3Zorn.crossProduct x v +
            t ^ 2 • (H3Zorn.adjointQuad v + H3Zorn.crossProduct x w2 +
              t • (H3Zorn.crossProduct x w3 + H3Zorn.crossProduct v w2) +
              t ^ 2 • (H3Zorn.crossProduct v w3 + H3Zorn.adjointQuad w2) +
              t ^ 3 • H3Zorn.crossProduct w2 w3 +
              t ^ 4 • H3Zorn.adjointQuad w3) := by
      intro x v w2 w3 t
      have hvec : x + t • v + t ^ 2 • w2 + t ^ 3 • w3 =
          (x + t • v) + (t ^ 2) • (w2 + t • w3) := by
        rw [smul_add, smul_smul, show t ^ 2 * t = t ^ 3 by ring]; abel
      rw [hvec, adjointQuad_add_smul_line, adjointQuad_add_smul_line,
        adjointQuad_add_smul_line]
      simp only [H3Zorn.crossProduct_add_left, H3Zorn.crossProduct_add_right,
        H3Zorn.crossProduct_smul_left, H3Zorn.crossProduct_smul_right, smul_add, smul_smul]
      have hp1 : t ^ 2 * t = t ^ 3 := by ring
      have hp2 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      have hp3 : t ^ 2 * t ^ 3 = t ^ 5 := by ring
      have hp4 : t ^ 2 * t ^ 4 = t ^ 6 := by ring
      have hp5 : (t ^ 2) ^ 2 = t ^ 4 := by ring
      rw [hp1, hp2, hp3, hp4, hp5]
      module
    have hcoeff : ∀ (x v w2 w3 : H3Zorn ℝ),
        ∃ A0 A1 A2 A3 A4 A5 A6 : H3Zorn ℝ,
          A0 = H3Zorn.adjointQuad x ∧ A1 = H3Zorn.crossProduct x v ∧
          ∀ t : ℝ, H3Zorn.adjointQuad (x + t • v + t ^ 2 • w2 + t ^ 3 • w3) =
            A0 + t • A1 + t ^ 2 • A2 + t ^ 3 • A3 + t ^ 4 • A4 + t ^ 5 • A5 + t ^ 6 • A6 := by
      intro x v w2 w3
      refine ⟨H3Zorn.adjointQuad x, H3Zorn.crossProduct x v,
        H3Zorn.adjointQuad v + H3Zorn.crossProduct x w2,
        H3Zorn.crossProduct x w3 + H3Zorn.crossProduct v w2,
        H3Zorn.crossProduct v w3 + H3Zorn.adjointQuad w2,
        H3Zorn.crossProduct w2 w3, H3Zorn.adjointQuad w3, rfl, rfl, fun t => ?_⟩
      rw [hexp_adj]
      simp only [smul_add, smul_smul]
      have hp1 : t ^ 2 * t = t ^ 3 := by ring
      have hp2 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      have hp3 : t ^ 2 * t ^ 3 = t ^ 5 := by ring
      have hp4 : t ^ 2 * t ^ 4 = t ^ 6 := by ring
      rw [hp1, hp2, hp3, hp4]
      module
    obtain ⟨A0, A1, A2, A3, A4, A5, A6, hA0, hA1, hAx⟩ := hcoeff Q.x V.x W2.x W3.x
    obtain ⟨B0, B1, B2, B3, B4, B5, B6, hB0, hB1, hBy⟩ := hcoeff Q.y V.y W2.y W3.y
    let RA : ℝ → H3Zorn ℝ := fun t => A2 + t • A3 + t ^ 2 • A4 + t ^ 3 • A5 + t ^ 4 • A6
    let RB : ℝ → H3Zorn ℝ := fun t => B2 + t • B3 + t ^ 2 • B4 + t ^ 3 • B5 + t ^ 4 • B6
    have hAx' : ∀ t : ℝ,
        H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x =
          A0 + t • A1 + t ^ 2 • RA t := fun t => by
      simp only [x_add, x_smul, hAx t, RA, smul_add, smul_smul]
      have hp1 : t ^ 2 * t = t ^ 3 := by ring
      have hp2 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      have hp3 : t ^ 2 * t ^ 3 = t ^ 5 := by ring
      have hp4 : t ^ 2 * t ^ 4 = t ^ 6 := by ring
      rw [hp1, hp2, hp3, hp4]
      module
    have hBy' : ∀ t : ℝ,
        H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y =
          B0 + t • B1 + t ^ 2 • RB t := fun t => by
      simp only [y_add, y_smul, hBy t, RB, smul_add, smul_smul]
      have hp1 : t ^ 2 * t = t ^ 3 := by ring
      have hp2 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      have hp3 : t ^ 2 * t ^ 3 = t ^ 5 := by ring
      have hp4 : t ^ 2 * t ^ 4 = t ^ 6 := by ring
      rw [hp1, hp2, hp3, hp4]
      module
    have hsplit : ∀ t : ℝ,
        H3Zorn.traceBilin
          (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x)
          (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y) =
          (H3Zorn.traceBilin A0 B0 +
            (H3Zorn.traceBilin A1 B0 + H3Zorn.traceBilin A0 B1) * t +
            H3Zorn.traceBilin A1 B1 * t ^ 2 + 0 * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5 + 0 * t ^ 6) +
            t ^ 2 * (H3Zorn.traceBilin A0 (RB t) + H3Zorn.traceBilin (RA t) B0 +
              t * (H3Zorn.traceBilin A1 (RB t) + H3Zorn.traceBilin (RA t) B1) +
              t ^ 2 * H3Zorn.traceBilin (RA t) (RB t)) := by
      intro t
      rw [hAx' t, hBy' t]
      simp only [H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
        H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right]
      ring
    have hlin_part : HasDerivAt (fun t : ℝ => H3Zorn.traceBilin A0 B0 +
        (H3Zorn.traceBilin A1 B0 + H3Zorn.traceBilin A0 B1) * t +
        H3Zorn.traceBilin A1 B1 * t ^ 2 + 0 * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5 + 0 * t ^ 6)
        (H3Zorn.traceBilin A1 B0 + H3Zorn.traceBilin A0 B1) 0 :=
      hasDerivAt_poly_at_zero _ _ _ _ _ _ _
    have hcA : ∀ C : H3Zorn ℝ, ∃ d, HasDerivAt (fun t : ℝ => H3Zorn.traceBilin (RA t) C) d 0 := by
      intro C
      refine ⟨H3Zorn.traceBilin A3 C, ?_⟩
      have hfun : (fun t : ℝ => H3Zorn.traceBilin (RA t) C) = fun t : ℝ =>
          H3Zorn.traceBilin A2 C + H3Zorn.traceBilin A3 C * t +
          H3Zorn.traceBilin A4 C * t ^ 2 + H3Zorn.traceBilin A5 C * t ^ 3 +
          H3Zorn.traceBilin A6 C * t ^ 4 := by
        ext t
        simp only [RA, H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_smul_left]
        ring
      rw [hfun]; exact hasDerivAt_poly4_at_zero _ _ _ _ _
    have hcB : ∀ C : H3Zorn ℝ, ∃ d, HasDerivAt (fun t : ℝ => H3Zorn.traceBilin C (RB t)) d 0 := by
      intro C
      refine ⟨H3Zorn.traceBilin C B3, ?_⟩
      have hfun : (fun t : ℝ => H3Zorn.traceBilin C (RB t)) = fun t : ℝ =>
          H3Zorn.traceBilin C B2 + H3Zorn.traceBilin C B3 * t +
          H3Zorn.traceBilin C B4 * t ^ 2 + H3Zorn.traceBilin C B5 * t ^ 3 +
          H3Zorn.traceBilin C B6 * t ^ 4 := by
        ext t
        simp only [RB, H3Zorn.traceBilin_add_right, H3Zorn.traceBilin_smul_right]
        ring
      rw [hfun]; exact hasDerivAt_poly4_at_zero _ _ _ _ _
    obtain ⟨dA0, hdA0⟩ := hcB A0
    obtain ⟨dB0, hdB0⟩ := hcA B0
    obtain ⟨dA1, hdA1⟩ := hcB A1
    obtain ⟨dB1, hdB1⟩ := hcA B1
    obtain ⟨d2, hd2⟩ := hcB A2
    obtain ⟨d3, hd3⟩ := hcB A3
    obtain ⟨d4, hd4⟩ := hcB A4
    obtain ⟨d5, hd5⟩ := hcB A5
    obtain ⟨d6, hd6⟩ := hcB A6
    have hfun_AB : (fun t : ℝ => H3Zorn.traceBilin (RA t) (RB t)) = fun t : ℝ =>
        H3Zorn.traceBilin A2 (RB t) + t * H3Zorn.traceBilin A3 (RB t) +
        t ^ 2 * H3Zorn.traceBilin A4 (RB t) + t ^ 3 * H3Zorn.traceBilin A5 (RB t) +
        t ^ 4 * H3Zorn.traceBilin A6 (RB t) := by
      ext t
      simp only [RA, H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_smul_left]
    have hd_AB_val : HasDerivAt (fun t : ℝ =>
        H3Zorn.traceBilin A2 (RB t) + t * H3Zorn.traceBilin A3 (RB t) +
        t ^ 2 * H3Zorn.traceBilin A4 (RB t) + t ^ 3 * H3Zorn.traceBilin A5 (RB t) +
        t ^ 4 * H3Zorn.traceBilin A6 (RB t))
        (d2 + (1 * H3Zorn.traceBilin A3 (RB 0) + 0 * d3) +
          ((2 : ℕ) * (0 : ℝ) ^ (2 - 1) * H3Zorn.traceBilin A4 (RB 0) + 0 ^ 2 * d4) +
          ((3 : ℕ) * (0 : ℝ) ^ (3 - 1) * H3Zorn.traceBilin A5 (RB 0) + 0 ^ 3 * d5) +
          ((4 : ℕ) * (0 : ℝ) ^ (4 - 1) * H3Zorn.traceBilin A6 (RB 0) + 0 ^ 4 * d6)) 0 :=
      (((hd2.add ((hasDerivAt_id 0).mul hd3)).add
        ((hasDerivAt_pow 2 0).mul hd4)).add
        ((hasDerivAt_pow 3 0).mul hd5)).add
        ((hasDerivAt_pow 4 0).mul hd6)
    rw [← hfun_AB] at hd_AB_val
    have hd_rem : HasDerivAt (fun t : ℝ => t ^ 2 *
        (H3Zorn.traceBilin A0 (RB t) + H3Zorn.traceBilin (RA t) B0 +
          t * (H3Zorn.traceBilin A1 (RB t) + H3Zorn.traceBilin (RA t) B1) +
          t ^ 2 * H3Zorn.traceBilin (RA t) (RB t))) 0 0 :=
      hasDerivAt_t_sq_mul
        ((((hdA0.add hdB0).add ((hasDerivAt_id 0).mul (hdA1.add hdB1))).add
          (hasDerivAt_t_sq_mul hd_AB_val)))
    have hfun_eq : (fun t : ℝ => H3Zorn.traceBilin
        (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x)
        (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y)) =
        fun t : ℝ => (H3Zorn.traceBilin A0 B0 +
          (H3Zorn.traceBilin A1 B0 + H3Zorn.traceBilin A0 B1) * t +
          H3Zorn.traceBilin A1 B1 * t ^ 2 + 0 * t ^ 3 + 0 * t ^ 4 + 0 * t ^ 5 + 0 * t ^ 6) +
          t ^ 2 * (H3Zorn.traceBilin A0 (RB t) + H3Zorn.traceBilin (RA t) B0 +
            t * (H3Zorn.traceBilin A1 (RB t) + H3Zorn.traceBilin (RA t) B1) +
            t ^ 2 * H3Zorn.traceBilin (RA t) (RB t)) := by
      ext t; exact hsplit t
    rw [hfun_eq, ← hA0, ← hA1, ← hB0, ← hB1]
    convert hlin_part.add hd_rem using 1
    norm_num
  have hd_t1 : HasDerivAt (fun t : ℝ =>
      (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).alpha *
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).beta -
      H3Zorn.traceBilin (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y)
      (V.alpha * Q.beta + Q.alpha * V.beta -
        H3Zorn.traceBilin V.x Q.y - H3Zorn.traceBilin Q.x V.y) 0 := by
    convert (hd_alpha.mul hd_beta).sub hd_xy using 1
    · simp only [add_zero, zero_smul,
        show (0 : ℝ) ^ 2 = 0 by norm_num, show (0 : ℝ) ^ 3 = 0 by norm_num]
      ring
  have hd_sq : HasDerivAt (fun t : ℝ =>
      ((Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).alpha *
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).beta -
      H3Zorn.traceBilin (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x
        (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y) ^ 2)
      (2 * (Q.alpha * Q.beta - H3Zorn.traceBilin Q.x Q.y) *
        (V.alpha * Q.beta + Q.alpha * V.beta -
          H3Zorn.traceBilin V.x Q.y - H3Zorn.traceBilin Q.x V.y)) 0 := by
    convert hd_t1.pow 2 using 1
    simp only [zero_smul, add_zero,
      show (0 : ℝ) ^ 2 = 0 by norm_num, show (0 : ℝ) ^ 3 = 0 by norm_num]
    ring
  have hd_nx : HasDerivAt (fun t : ℝ =>
      H3Zorn.normCubic (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x)
      (H3Zorn.traceBilin (H3Zorn.adjointQuad Q.x) V.x) 0 := by
    simpa [x_add, x_smul] using hd_norm Q.x V.x W2.x W3.x
  have hd_ny : HasDerivAt (fun t : ℝ =>
      H3Zorn.normCubic (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y)
      (H3Zorn.traceBilin (H3Zorn.adjointQuad Q.y) V.y) 0 := by
    simpa [y_add, y_smul] using hd_norm Q.y V.y W2.y W3.y
  have hd_anx := hd_alpha.mul hd_nx
  have hd_bny := hd_beta.mul hd_ny
  have hd_sum := ((hd_anx.add hd_bny).add hd_adj_pair).const_mul 4
  have hd_total := hd_sq.sub hd_sum
  have hfun_q : (fun t : ℝ => quarticInvariant (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3)) =
      fun t : ℝ =>
        ((Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).alpha *
          (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).beta -
        H3Zorn.traceBilin (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x
          (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y) ^ 2 -
        4 * ((Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).alpha *
            H3Zorn.normCubic (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x +
          (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).beta *
            H3Zorn.normCubic (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y +
          H3Zorn.traceBilin (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).x)
            (H3Zorn.adjointQuad (Q + t • V + t ^ 2 • W2 + t ^ 3 • W3).y)) := by
    ext t; exact quarticInvariant_expanded _
  rw [hfun_q]
  convert hd_total using 1
  simp only [quarticDeriv, zero_smul, add_zero,
    show (0 : ℝ) ^ 2 = 0 by norm_num, show (0 : ℝ) ^ 3 = 0 by norm_num]
  ring

theorem hasDerivAt_quarticInvariant (Q V : Charge) :
    HasDerivAt (fun t : ℝ => quarticInvariant (Q + t • V)) (quarticDeriv Q V) 0 := by
  have h := hasDerivAt_quarticInvariant_curve Q V 0 0
  simpa using h

private theorem quarticDeriv_add (Q V₁ V₂ : Charge) :
    quarticDeriv Q (V₁ + V₂) = quarticDeriv Q V₁ + quarticDeriv Q V₂ := by
  simp only [quarticDeriv, alpha_add, beta_add, x_add, y_add,
    H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
    H3Zorn.crossProduct_add_right]
  ring

private theorem quarticDeriv_repNeg (B : H3Zorn ℝ) (Q : Charge) :
    quarticDeriv Q (repNeg B Q) = 0 := by
  let W2 : Charge :=
    { alpha := -(1 / 4 : ℝ) * H3Zorn.traceBilin (H3Zorn.adjointQuad B) Q.x
      beta := 0
      x := 0
      y := -(1 / 4 : ℝ) • (Q.beta • H3Zorn.adjointQuad B) }
  let W3 : Charge :=
    { alpha := -(1 / 8 : ℝ) * (Q.beta * H3Zorn.normCubic B)
      beta := 0
      x := 0
      y := 0 }
  have hcurve : ∀ t : ℝ,
      freudenthalUpperTrans ((t / 2 : ℝ) • B) Q =
        Q + t • repNeg B Q + t ^ 2 • W2 + t ^ 3 • W3 := by
    intro t
    apply FreudenthalCharge.ext
    · simp only [freudenthalUpperTrans_alpha, alpha_add, alpha_smul,
        repNeg, LinearMap.coe_mk, AddHom.coe_mk, W2, W3,
        H3Zorn.traceBilin_smul_left, H3Zorn.adjointQuad_smul, H3Zorn.normCubic_smul]
      ring
    · simp only [freudenthalUpperTrans_beta, beta_add, beta_smul,
        repNeg, LinearMap.coe_mk, AddHom.coe_mk, W2, W3]
      ring
    · simp only [freudenthalUpperTrans_x, x_add, x_smul,
        repNeg, LinearMap.coe_mk, AddHom.coe_mk, W2, W3]
      module
    · simp only [freudenthalUpperTrans_y, y_add, y_smul,
        repNeg, LinearMap.coe_mk, AddHom.coe_mk, W2, W3,
        H3Zorn.crossProduct_smul_left, H3Zorn.adjointQuad_smul]
      module
  obtain ⟨c₂, c₃, c₄, c₅, c₆, hc⟩ := freudenthalUpperTrans_firstOrder B Q
  have hfun : (fun t : ℝ => quarticInvariant (Q + t • repNeg B Q + t ^ 2 • W2 + t ^ 3 • W3)) =
      fun t : ℝ => quarticInvariant Q +
        ((t / 2) ^ 2 * (c₂ + (t / 2) * c₃ + (t / 2) ^ 2 * c₄ +
          (t / 2) ^ 3 * c₅ + (t / 2) ^ 4 * c₆)) := by
    ext t
    rw [← hcurve t, hc (t / 2)]
  have hd1 := hasDerivAt_quarticInvariant_curve Q (repNeg B Q) W2 W3
  rw [hfun] at hd1
  have hpoly : (fun t : ℝ => quarticInvariant Q +
      ((t / 2) ^ 2 * (c₂ + (t / 2) * c₃ + (t / 2) ^ 2 * c₄ +
        (t / 2) ^ 3 * c₅ + (t / 2) ^ 4 * c₆))) =
      fun t : ℝ => quarticInvariant Q + 0 * t +
        (c₂ / 4) * t ^ 2 + (c₃ / 8) * t ^ 3 + (c₄ / 16) * t ^ 4 +
        (c₅ / 32) * t ^ 5 + (c₆ / 64) * t ^ 6 := by
    ext t; ring
  rw [hpoly] at hd1
  exact hd1.unique (hasDerivAt_poly_at_zero _ _ _ _ _ _ _)

private theorem quarticDeriv_repPos (A : H3Zorn ℝ) (Q : Charge) :
    quarticDeriv Q (repPos A Q) = 0 := by
  let W2 : Charge :=
    { alpha := 0
      beta := -H3Zorn.traceBilin (H3Zorn.adjointQuad A) Q.y
      x := -(Q.alpha • H3Zorn.adjointQuad A)
      y := 0 }
  let W3 : Charge :=
    { alpha := 0
      beta := -(Q.alpha * H3Zorn.normCubic A)
      x := 0
      y := 0 }
  have hcurve : ∀ t : ℝ,
      freudenthalLowerTrans (t • A) Q =
        Q + t • repPos A Q + t ^ 2 • W2 + t ^ 3 • W3 := by
    intro t
    apply FreudenthalCharge.ext
    · simp only [freudenthalLowerTrans_alpha, alpha_add, alpha_smul,
        repPos, LinearMap.coe_mk, AddHom.coe_mk, W2, W3]
      ring
    · simp only [freudenthalLowerTrans_beta, beta_add, beta_smul,
        repPos, LinearMap.coe_mk, AddHom.coe_mk, W2, W3,
        H3Zorn.traceBilin_smul_left, H3Zorn.adjointQuad_smul, H3Zorn.normCubic_smul]
      ring
    · simp only [freudenthalLowerTrans_x, x_add, x_smul,
        repPos, LinearMap.coe_mk, AddHom.coe_mk, W2, W3,
        H3Zorn.crossProduct_smul_left, H3Zorn.adjointQuad_smul]
      module
    · simp only [freudenthalLowerTrans_y, y_add, y_smul,
        repPos, LinearMap.coe_mk, AddHom.coe_mk, W2, W3]
      module
  have hfun : (fun t : ℝ => quarticInvariant (Q + t • repPos A Q + t ^ 2 • W2 + t ^ 3 • W3)) =
      fun _ : ℝ => quarticInvariant Q := by
    ext t
    rw [← hcurve t, freudenthalLowerTrans_preserves_quarticInvariant]
  have hd1 := hasDerivAt_quarticInvariant_curve Q (repPos A Q) W2 W3
  rw [hfun] at hd1
  exact hd1.unique (hasDerivAt_const 0 (quarticInvariant Q))

private theorem quarticDeriv_repZero (T₀ : h3zornTKKDatum.str) (Q : Charge) :
    quarticDeriv Q (repZero T₀ Q) = 0 := by
  rcases h3zornTKKDatum.str_decomp T₀.1 T₀.2 with ⟨D, a, hT⟩
  let E : H3ZornF4Derivations := ⟨D.1, D.2⟩
  let k : ℝ := strTrace T₀ / 3
  let a₀ : H3Zorn ℝ := a - k • (1 : H3Zorn ℝ)
  have htr_1 : H3Zorn.linearTrace (1 : H3Zorn ℝ) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3; norm_num
  have ha0_tr : H3Zorn.linearTrace a₀ = 0 := by
    have hT1 : T₀.1 1 = a := by
      rw [hT, LinearMap.add_apply, jordanLmul_apply]
      change (E : Operator) 1 + candidateJordanMul a 1 = a
      rw [h3ZornF4_derivation_apply_one_eq_zero E, zero_add, candidateJordanMul_one_right]
    have ha0_eq : a₀ = a + (-k) • (1 : H3Zorn ℝ) := by
      dsimp [a₀]; rw [sub_eq_add_neg, neg_smul]
    rw [ha0_eq, H3Zorn.linearTrace_add, H3Zorn.linearTrace_smul, htr_1, ← hT1]
    change strTrace T₀ + (-k) * 3 = 0
    dsimp [k]; ring
  have hT_split : T₀.1 = ((E : Operator) + jordanLmul (R := ℝ) a₀) + k • LinearMap.id := by
    rw [hT]
    apply LinearMap.ext; intro z
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, jordanLmul_apply]
    change (E : Operator) z + a * z =
      ((E : Operator) z + (a - k • (1 : H3Zorn ℝ)) * z) + k • z
    rw [sub_mul, show (k • (1 : H3Zorn ℝ)) * z = k • z by
      change candidateJordanMul (k • 1) z = k • z
      rw [candidateJordanMul_smul_left, candidateJordanMul_one_left]]
    abel
  have hadj_split : h3zornTraceAdjoint T₀.1 =
      (-(E : Operator) + jordanLmul (R := ℝ) a₀) + k • LinearMap.id := by
    have h1 : h3zornTraceAdjoint ((E : Operator) + jordanLmul (R := ℝ) a₀ + k • LinearMap.id) =
        h3zornTraceAdjointLM (E : Operator) + h3zornTraceAdjointLM (jordanLmul (R := ℝ) a₀) +
          k • h3zornTraceAdjointLM LinearMap.id := by
      change h3zornTraceAdjointLM _ = _
      rw [map_add, map_add, map_smul]
    have hE_der : h3zornTraceAdjoint (E : Operator) = -(E : Operator) :=
      h3zornTraceAdjoint_derivation D
    rw [hT_split, h1, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjointLM_apply, hE_der,
      h3zornTraceAdjoint_jordanLmul, h3zornTraceAdjoint_id]
  let T₀' : Operator := (E : Operator) + jordanLmul (R := ℝ) a₀
  let T₀'adj : Operator := -(E : Operator) + jordanLmul (R := ℝ) a₀
  have hT₀'_mem : T₀' ∈ h3zornCubicStabilizer :=
    h3zornCubicStabilizer.add_mem (H3ZornF4Derivations_le_h3zornCubicStabilizer E.2)
      ((jordanLmul_mem_h3zornCubicStabilizer_iff a₀).mpr ha0_tr)
  have hT₀'adj_mem : T₀'adj ∈ h3zornCubicStabilizer :=
    h3zornCubicStabilizer.add_mem
      (h3zornCubicStabilizer.neg_mem (H3ZornF4Derivations_le_h3zornCubicStabilizer E.2))
      ((jordanLmul_mem_h3zornCubicStabilizer_iff a₀).mpr ha0_tr)
  have hx_stab : H3Zorn.traceBilin (H3Zorn.adjointQuad Q.x) (T₀' Q.x) = 0 :=
    (mem_h3zornCubicStabilizer_iff_traceBilin_adjointQuad T₀').mp hT₀'_mem Q.x
  have hy_stab : H3Zorn.traceBilin (H3Zorn.adjointQuad Q.y) (T₀'adj Q.y) = 0 :=
    (mem_h3zornCubicStabilizer_iff_traceBilin_adjointQuad T₀'adj).mp hT₀'adj_mem Q.y
  have hpair_xy : H3Zorn.traceBilin (T₀' Q.x) Q.y - H3Zorn.traceBilin Q.x (T₀'adj Q.y) = 0 := by
    have hD_skew := h3ZornF4_derivation_traceBilin_skew E Q.x Q.y
    have ha_assoc := h3Zorn_traceBilin_jordanLmul_assoc a₀ Q.x Q.y
    simp only [T₀', T₀'adj, LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply,
      H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
      h3_traceBilin_neg_right]
    linarith
  have hcross_E : ∀ w : H3Zorn ℝ,
      H3Zorn.crossProduct w ((E : Operator) w) = (E : Operator) (H3Zorn.adjointQuad w) :=
    fun w => (h3ZornF4_derivation_adjointQuad E w).symm
  have hcross_a0 : ∀ w : H3Zorn ℝ,
      H3Zorn.crossProduct w (a₀ * w) = -(a₀ * H3Zorn.adjointQuad w) := by
    intro w
    have hr := jordanLmul_crossProduct_rule a₀ w w
    rw [H3Zorn.crossProduct_self, ha0_tr, zero_smul, H3Zorn.crossProduct_symm (a₀ * w) w] at hr
    have hr2 : (2 : ℝ) • (a₀ * H3Zorn.adjointQuad w + H3Zorn.crossProduct w (a₀ * w)) = 0 := by
      rw [smul_add, ← h3_mul_smul_right 2 a₀ (H3Zorn.adjointQuad w)]
      convert hr using 1
      module
    have h0 := (smul_eq_zero.mp hr2).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    exact eq_neg_of_add_eq_zero_right h0
  have hcross_pair :
      H3Zorn.traceBilin (H3Zorn.crossProduct Q.x (T₀' Q.x)) (H3Zorn.adjointQuad Q.y) -
        H3Zorn.traceBilin (H3Zorn.adjointQuad Q.x) (H3Zorn.crossProduct Q.y (T₀'adj Q.y)) = 0 := by
    simp only [T₀', T₀'adj, LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply,
      H3Zorn.crossProduct_add_right, h3_crossProduct_neg_right,
      hcross_E, hcross_a0, H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right,
      h3_traceBilin_neg_left, h3_traceBilin_neg_right]
    have hD_skew := h3ZornF4_derivation_traceBilin_skew E (H3Zorn.adjointQuad Q.x) (H3Zorn.adjointQuad Q.y)
    have ha_assoc := h3Zorn_traceBilin_jordanLmul_assoc a₀ (H3Zorn.adjointQuad Q.x) (H3Zorn.adjointQuad Q.y)
    linarith
  have hsplit_V : repZero T₀ Q =
      { alpha := 0, beta := 0, x := T₀' Q.x, y := -(T₀'adj Q.y) } +
        (k / 2 : ℝ) • { alpha := 3 * Q.alpha, beta := -3 * Q.beta, x := -Q.x, y := Q.y } := by
    have hk : (1 / 2 : ℝ) * strTrace T₀ = 3 * (k / 2) := by dsimp [k]; ring
    apply FreudenthalCharge.ext
    · simp only [repZero, LinearMap.coe_mk, AddHom.coe_mk, alpha_add, alpha_smul, hk]; ring
    · simp only [repZero, LinearMap.coe_mk, AddHom.coe_mk, beta_add, beta_smul, hk]; ring
    · simp only [repZero, LinearMap.coe_mk, AddHom.coe_mk, x_add, x_smul, hT_split,
        LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hk]
      change T₀' Q.x + k • Q.x - (3 * (k / 2)) • Q.x = T₀' Q.x + (k / 2) • (-Q.x)
      module
    · simp only [repZero, LinearMap.coe_mk, AddHom.coe_mk, y_add, y_smul, hadj_split,
        LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hk]
      change -(T₀'adj Q.y + k • Q.y) + (3 * (k / 2)) • Q.y = -(T₀'adj Q.y) + (k / 2) • Q.y
      module
  rw [hsplit_V, quarticDeriv_add]
  have h1 : quarticDeriv Q { alpha := 0, beta := 0, x := T₀' Q.x, y := -(T₀'adj Q.y) } = 0 := by
    simp only [quarticDeriv, h3_traceBilin_neg_right, h3_crossProduct_neg_right]
    have hp1 : H3Zorn.traceBilin (T₀' Q.x) Q.y = H3Zorn.traceBilin Q.x (T₀'adj Q.y) :=
      sub_eq_zero.mp hpair_xy
    have hp2 :
        H3Zorn.traceBilin (H3Zorn.crossProduct Q.x (T₀' Q.x)) (H3Zorn.adjointQuad Q.y) =
          H3Zorn.traceBilin (H3Zorn.adjointQuad Q.x) (H3Zorn.crossProduct Q.y (T₀'adj Q.y)) :=
      sub_eq_zero.mp hcross_pair
    rw [hx_stab, hy_stab, hp1, hp2]
    ring
  have h2 : quarticDeriv Q
      ((k / 2 : ℝ) • { alpha := 3 * Q.alpha, beta := -3 * Q.beta, x := -Q.x, y := Q.y }) = 0 := by
    simp only [quarticDeriv, alpha_smul, beta_smul, x_smul, y_smul,
      H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right,
      h3_traceBilin_neg_left, h3_traceBilin_neg_right, H3Zorn.crossProduct_smul_right,
      h3_crossProduct_neg_right, H3Zorn.crossProduct_self]
    rw [H3Zorn.mccrimmon_identity_13 Q.x, H3Zorn.mccrimmon_identity_13 Q.y]
    ring
  rw [h1, h2, add_zero]

/-- Infinitesimal invariance of `quarticInvariant` under `repE7`. -/
theorem repE7_preserves_quarticInvariant_deriv (X : H3ZornTKKLie) (Q : Charge) :
    HasDerivAt (fun t : ℝ => quarticInvariant (Q + t • repE7 X Q)) 0 0 := by
  have hderiv : quarticDeriv Q (repE7 X Q) = 0 := by
    have hdec : repE7 X Q = repNeg X.neg Q + repZero X.zero Q + repPos X.pos Q := by
      conv_lhs => rw [JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X]
      change repE7 (negInj X.neg + zeroInj X.zero + posInj X.pos) Q = _
      simp only [map_add, LinearMap.add_apply, repE7_negInj, repE7_zeroInj, repE7_posInj]
    rw [hdec, quarticDeriv_add, quarticDeriv_add,
      quarticDeriv_repNeg, quarticDeriv_repZero, quarticDeriv_repPos]
    norm_num
  nth_rw 1 [← hderiv]
  exact hasDerivAt_quarticInvariant Q (repE7 X Q)

end RepE7

/-! ## 4. Symmetric `E₇`-Equivariant Map `K`, 248D 5-Graded Bracket, Jacobi Closure & Grading -/

section Bracket5AndGrading

@[simp] private theorem h3zornTraceAdjoint_h3zornStrOne :
    h3zornTraceAdjoint h3zornStrOne.1 = h3zornStrOne.1 := by
  rw [h3zornStrOne_coe_eq_id, h3zornTraceAdjoint_id]

@[simp] private theorem strTrace_h3zornStrOne : strTrace h3zornStrOne = 3 := by
  change H3Zorn.linearTrace (h3zornStrOne.1 1) = 3
  rw [h3zornStrOne_apply]
  change (1 : ℝ) + 1 + 1 = 3
  norm_num

@[simp] private theorem h3_traceBilin_zero_left (y : H3Zorn ℝ) :
    H3Zorn.traceBilin 0 y = 0 := by
  have h := H3Zorn.traceBilin_smul_left (0 : ℝ) 0 y
  simpa using h

@[simp] private theorem h3_traceBilin_zero_right (x : H3Zorn ℝ) :
    H3Zorn.traceBilin x 0 = 0 := by
  have h := H3Zorn.traceBilin_smul_right (0 : ℝ) x 0
  simpa using h

@[simp] private theorem symp_zero_left (Q : Charge) : symplecticForm 0 Q = 0 := by
  rw [symplecticForm_expanded]
  simp only [charge_zero_alpha, charge_zero_beta, charge_zero_x, charge_zero_y,
    h3_traceBilin_zero_left, zero_mul, sub_self, add_zero]

@[simp] private theorem symp_zero_right (Q : Charge) : symplecticForm Q 0 = 0 := by
  rw [symplecticForm_expanded]
  simp only [charge_zero_alpha, charge_zero_beta, charge_zero_x, charge_zero_y,
    h3_traceBilin_zero_right, mul_zero, sub_self, add_zero]

@[simp] private theorem symp_neg_left (Q₁ Q₂ : Charge) :
    symplecticForm (-Q₁) Q₂ = -symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]; simp; ring

@[simp] private theorem symp_neg_right (Q₁ Q₂ : Charge) :
    symplecticForm Q₁ (-Q₂) = -symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]; simp; ring

@[simp] private theorem symp_add_left (Q₁ Q₂ P : Charge) :
    symplecticForm (Q₁ + Q₂) P = symplecticForm Q₁ P + symplecticForm Q₂ P := by
  rw [symplecticForm_expanded, symplecticForm_expanded, symplecticForm_expanded]
  simp only [alpha_add, beta_add, x_add, y_add, H3Zorn.traceBilin_add_left]
  ring

@[simp] private theorem symp_add_right (Q P₁ P₂ : Charge) :
    symplecticForm Q (P₁ + P₂) = symplecticForm Q P₁ + symplecticForm Q P₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded, symplecticForm_expanded]
  simp only [alpha_add, beta_add, x_add, y_add, H3Zorn.traceBilin_add_right]
  ring

@[simp] private theorem symp_smul_left (r : ℝ) (Q₁ Q₂ : Charge) :
    symplecticForm (r • Q₁) Q₂ = r * symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]
  simp only [alpha_smul, beta_smul, x_smul, y_smul, H3Zorn.traceBilin_smul_left]
  ring

@[simp] private theorem symp_smul_right (r : ℝ) (Q₁ Q₂ : Charge) :
    symplecticForm Q₁ (r • Q₂) = r * symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]
  simp only [alpha_smul, beta_smul, x_smul, y_smul, H3Zorn.traceBilin_smul_right]
  ring

@[simp] private theorem tripleD_smul_left (r : ℝ) (x y : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ (r • x) y = r • JordanTKK.tripleD ℝ x y := by
  apply LinearMap.ext; intro z
  simp only [LinearMap.smul_apply, tripleD_apply_expanded,
    H3Zorn.traceBilin_smul_left, H3Zorn.crossProduct_smul_left, smul_smul, smul_add, smul_sub]
  rw [show (1 / 2 : ℝ) * (r * H3Zorn.traceBilin x y) =
      r * ((1 / 2 : ℝ) * H3Zorn.traceBilin x y) by ring,
    show (1 / 2 : ℝ) * (H3Zorn.traceBilin z y * r) =
      r * ((1 / 2 : ℝ) * H3Zorn.traceBilin z y) by ring,
    show (1 / 2 : ℝ) * r = r * (1 / 2 : ℝ) by ring]

@[simp] private theorem tripleD_smul_right (r : ℝ) (x y : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ x (r • y) = r • JordanTKK.tripleD ℝ x y := by
  apply LinearMap.ext; intro z
  simp only [LinearMap.smul_apply, tripleD_apply_expanded,
    H3Zorn.traceBilin_smul_right, H3Zorn.crossProduct_smul_right, smul_smul, smul_add, smul_sub]
  rw [show (1 / 2 : ℝ) * (r * H3Zorn.traceBilin x y) =
      r * ((1 / 2 : ℝ) * H3Zorn.traceBilin x y) by ring,
    show (1 / 2 : ℝ) * (r * H3Zorn.traceBilin z y) =
      r * ((1 / 2 : ℝ) * H3Zorn.traceBilin z y) by ring,
    show (1 / 2 : ℝ) * r = r * (1 / 2 : ℝ) by ring]

@[simp] private theorem tripleD_add_left (x₁ x₂ y : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ (x₁ + x₂) y = JordanTKK.tripleD ℝ x₁ y + JordanTKK.tripleD ℝ x₂ y := by
  apply LinearMap.ext; intro z
  simp only [LinearMap.add_apply, tripleD_apply_expanded,
    H3Zorn.traceBilin_add_left, H3Zorn.crossProduct_add_left, add_smul]
  module

@[simp] private theorem tripleD_add_right (x y₁ y₂ : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ x (y₁ + y₂) = JordanTKK.tripleD ℝ x y₁ + JordanTKK.tripleD ℝ x y₂ := by
  apply LinearMap.ext; intro z
  simp only [LinearMap.add_apply, tripleD_apply_expanded,
    H3Zorn.traceBilin_add_right, H3Zorn.crossProduct_add_right, add_smul]
  module

@[simp] private theorem tripleD_neg_left (x y : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ (-x) y = -JordanTKK.tripleD ℝ x y := by
  rw [show (-x : H3Zorn ℝ) = (-1 : ℝ) • x by module, tripleD_smul_left]
  module

@[simp] private theorem tripleD_neg_right (x y : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ x (-y) = -JordanTKK.tripleD ℝ x y := by
  rw [show (-y : H3Zorn ℝ) = (-1 : ℝ) • y by module, tripleD_smul_right]
  module

@[simp] private theorem h3tkk_add_neg (X Y : H3ZornTKKLie) : (X + Y).neg = X.neg + Y.neg := rfl
@[simp] private theorem h3tkk_add_zero (X Y : H3ZornTKKLie) : (X + Y).zero = X.zero + Y.zero := rfl
@[simp] private theorem h3tkk_add_pos (X Y : H3ZornTKKLie) : (X + Y).pos = X.pos + Y.pos := rfl
@[simp] private theorem h3tkk_smul_neg (r : ℝ) (X : H3ZornTKKLie) :
    (r • X).neg = r • X.neg := rfl
@[simp] private theorem h3tkk_smul_zero (r : ℝ) (X : H3ZornTKKLie) :
    (r • X).zero = r • X.zero := rfl
@[simp] private theorem h3tkk_smul_pos (r : ℝ) (X : H3ZornTKKLie) :
    (r • X).pos = r • X.pos := rfl

private theorem h3zornTKKLie_ext {X Y : H3ZornTKKLie}
    (hneg : X.neg = Y.neg) (hzero : X.zero = Y.zero) (hpos : X.pos = Y.pos) : X = Y := by
  cases X; cases Y; simp only at hneg hzero hpos; subst hneg; subst hzero; subst hpos; rfl

/-- Symmetric `H3ZornTKKLie`-equivariant bilinear pairing `K : Charge →ₗ[ℝ] Charge →ₗ[ℝ] H3ZornTKKLie`
giving the `H3ZornTKKLie`-component of `[g₊₁, g₋₁]`. -/
def K : Charge →ₗ[ℝ] Charge →ₗ[ℝ] H3ZornTKKLie where
  toFun Q₁ :=
    { toFun := fun Q₂ =>
        { neg := (2 : ℝ) • (Q₁.alpha • Q₂.x + Q₂.alpha • Q₁.x + H3Zorn.crossProduct Q₁.y Q₂.y)
          pos := -(Q₁.beta • Q₂.y + Q₂.beta • Q₁.y + H3Zorn.crossProduct Q₁.x Q₂.x)
          zero :=
            (-2 : ℝ) •
              (⟨JordanTKK.tripleD ℝ Q₁.x Q₂.y, h3zornTKKDatum.tripleD_mem_str _ _⟩ +
               ⟨JordanTKK.tripleD ℝ Q₂.x Q₁.y, h3zornTKKDatum.tripleD_mem_str _ _⟩) +
            (-(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
              H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y) • h3zornStrOne }
      map_add' Q₂ Q₃ := by
        apply h3zornTKKLie_ext
        · simp only [h3tkk_add_neg, alpha_add, x_add, y_add, smul_add, add_smul,
            H3Zorn.crossProduct_add_right]
          module
        · apply Subtype.ext
          simp only [h3tkk_add_zero, Submodule.coe_add, Submodule.coe_smul,
            alpha_add, beta_add, x_add, y_add, tripleD_add_left, tripleD_add_right,
            H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_add_right, smul_add, add_smul]
          apply LinearMap.ext; intro w
          simp only [LinearMap.add_apply, LinearMap.smul_apply]
          module
        · simp only [h3tkk_add_pos, beta_add, x_add, y_add, smul_add, add_smul,
            H3Zorn.crossProduct_add_right]
          module
      map_smul' r Q₂ := by
        apply h3zornTKKLie_ext
        · simp only [h3tkk_smul_neg, alpha_smul, x_smul, y_smul, RingHom.id_apply,
            H3Zorn.crossProduct_smul_right, smul_add, smul_smul]
          module
        · apply Subtype.ext
          simp only [h3tkk_smul_zero, Submodule.coe_add, Submodule.coe_smul,
            RingHom.id_apply, alpha_smul, beta_smul, x_smul, y_smul,
            tripleD_smul_left, tripleD_smul_right,
            H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right, smul_add, smul_smul]
          apply LinearMap.ext; intro w
          simp only [LinearMap.add_apply, LinearMap.smul_apply]
          module
        · simp only [h3tkk_smul_pos, beta_smul, x_smul, y_smul, RingHom.id_apply,
            H3Zorn.crossProduct_smul_right, smul_add, smul_neg, smul_smul]
          module }
  map_add' Q₁ Q₂ := by
    apply LinearMap.ext; intro Q₃
    apply h3zornTKKLie_ext
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, h3tkk_add_neg,
        alpha_add, x_add, y_add, smul_add, add_smul, H3Zorn.crossProduct_add_left]
      module
    · apply Subtype.ext
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, h3tkk_add_zero,
        Submodule.coe_add, Submodule.coe_smul, alpha_add, beta_add, x_add, y_add,
        tripleD_add_left, tripleD_add_right, H3Zorn.traceBilin_add_left,
        H3Zorn.traceBilin_add_right, smul_add, add_smul]
      apply LinearMap.ext; intro w
      simp only [LinearMap.add_apply, LinearMap.smul_apply]
      module
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, h3tkk_add_pos,
        beta_add, x_add, y_add, smul_add, add_smul, H3Zorn.crossProduct_add_left]
      module
  map_smul' r Q₁ := by
    apply LinearMap.ext; intro Q₃
    apply h3zornTKKLie_ext
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, h3tkk_smul_neg,
        RingHom.id_apply, alpha_smul, x_smul, y_smul,
        H3Zorn.crossProduct_smul_left, smul_add, smul_smul]
      module
    · apply Subtype.ext
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, h3tkk_smul_zero,
        Submodule.coe_add, Submodule.coe_smul, RingHom.id_apply,
        alpha_smul, beta_smul, x_smul, y_smul,
        tripleD_smul_left, tripleD_smul_right,
        H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right, smul_add, smul_smul]
      apply LinearMap.ext; intro w
      simp only [LinearMap.add_apply, LinearMap.smul_apply]
      module
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, h3tkk_smul_pos,
        RingHom.id_apply, beta_smul, x_smul, y_smul,
        H3Zorn.crossProduct_smul_left, smul_add, smul_neg, smul_smul]
      module

@[simp] theorem K_neg (Q₁ Q₂ : Charge) :
    (K Q₁ Q₂).neg =
      (2 : ℝ) • (Q₁.alpha • Q₂.x + Q₂.alpha • Q₁.x + H3Zorn.crossProduct Q₁.y Q₂.y) := rfl

@[simp] theorem K_pos (Q₁ Q₂ : Charge) :
    (K Q₁ Q₂).pos =
      -(Q₁.beta • Q₂.y + Q₂.beta • Q₁.y + H3Zorn.crossProduct Q₁.x Q₂.x) := rfl

@[simp] theorem K_zero (Q₁ Q₂ : Charge) :
    (K Q₁ Q₂).zero =
      (-2 : ℝ) •
        (⟨JordanTKK.tripleD ℝ Q₁.x Q₂.y, h3zornTKKDatum.tripleD_mem_str _ _⟩ +
         ⟨JordanTKK.tripleD ℝ Q₂.x Q₁.y, h3zornTKKDatum.tripleD_mem_str _ _⟩) +
      (-(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
        H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y) • h3zornStrOne := rfl

@[simp] private theorem K_zero_left (Q : Charge) : K 0 Q = 0 := by
  rw [map_zero, LinearMap.zero_apply]
@[simp] private theorem K_zero_right (Q : Charge) : K Q 0 = 0 :=
  map_zero (K Q)
@[simp] private theorem K_neg_left (Q₁ Q₂ : Charge) : K (-Q₁) Q₂ = -K Q₁ Q₂ := by
  rw [map_neg, LinearMap.neg_apply]
@[simp] private theorem K_neg_right (Q₁ Q₂ : Charge) : K Q₁ (-Q₂) = -K Q₁ Q₂ :=
  map_neg (K Q₁) Q₂
@[simp] private theorem K_smul_left (r : ℝ) (Q₁ Q₂ : Charge) :
    K (r • Q₁) Q₂ = r • K Q₁ Q₂ := by
  rw [map_smul, LinearMap.smul_apply]
@[simp] private theorem K_smul_right (r : ℝ) (Q₁ Q₂ : Charge) :
    K Q₁ (r • Q₂) = r • K Q₁ Q₂ :=
  map_smul (K Q₁) r Q₂

theorem K_symm (Q₁ Q₂ : Charge) : K Q₁ Q₂ = K Q₂ Q₁ := by
  apply h3zornTKKLie_ext
  · simp only [K_neg, H3Zorn.crossProduct_symm Q₁.y Q₂.y]
    abel
  · apply Subtype.ext
    simp only [K_zero, Submodule.coe_add, Submodule.coe_smul]
    rw [add_comm (JordanTKK.tripleD ℝ Q₁.x Q₂.y) (JordanTKK.tripleD ℝ Q₂.x Q₁.y),
      show -(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) + H3Zorn.traceBilin Q₁.x Q₂.y +
          H3Zorn.traceBilin Q₂.x Q₁.y =
        -(Q₂.alpha * Q₁.beta + Q₂.beta * Q₁.alpha) + H3Zorn.traceBilin Q₂.x Q₁.y +
          H3Zorn.traceBilin Q₁.x Q₂.y by ring]
  · simp only [K_pos, H3Zorn.crossProduct_symm Q₁.x Q₂.x]
    abel

theorem K_zero_strTrace (Q₁ Q₂ : Charge) :
    strTrace (K Q₁ Q₂).zero =
      -3 * (Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
        H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y := by
  change H3Zorn.linearTrace ((K Q₁ Q₂).zero.1 1) = _
  simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply,
    LinearMap.smul_apply, h3zornStrOne_apply, H3Zorn.linearTrace_add, H3Zorn.linearTrace_smul,
    linearTrace_tripleD_apply_one]
  have h1 : H3Zorn.linearTrace (1 : H3Zorn ℝ) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3; norm_num
  rw [h1]
  ring

@[simp] private theorem h3tkk_negInj_neg (x : H3Zorn ℝ) : (negInj x).neg = x := rfl
@[simp] private theorem h3tkk_negInj_zero (x : H3Zorn ℝ) : (negInj x).zero = 0 := rfl
@[simp] private theorem h3tkk_negInj_pos (x : H3Zorn ℝ) : (negInj x).pos = 0 := rfl
@[simp] private theorem h3tkk_zeroInj_neg (T : h3zornTKKDatum.str) : (zeroInj T).neg = 0 := rfl
@[simp] private theorem h3tkk_zeroInj_zero (T : h3zornTKKDatum.str) : (zeroInj T).zero = T := rfl
@[simp] private theorem h3tkk_zeroInj_pos (T : h3zornTKKDatum.str) : (zeroInj T).pos = 0 := rfl
@[simp] private theorem h3tkk_posInj_neg (y : H3Zorn ℝ) : (posInj y).neg = 0 := rfl
@[simp] private theorem h3tkk_posInj_zero (y : H3Zorn ℝ) : (posInj y).zero = 0 := rfl
@[simp] private theorem h3tkk_posInj_pos (y : H3Zorn ℝ) : (posInj y).pos = y := rfl

private theorem K_equivariant_neg (B : H3Zorn ℝ) (Q₁ Q₂ : Charge) :
    ⁅negInj B, K Q₁ Q₂⁆ = K (repNeg B Q₁) Q₂ + K Q₁ (repNeg B Q₂) := by
  have hK : K Q₁ Q₂ =
      negInj (K Q₁ Q₂).neg + zeroInj (K Q₁ Q₂).zero + posInj (K Q₁ Q₂).pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) (K Q₁ Q₂)
  have hL : ⁅negInj B, K Q₁ Q₂⁆ =
      negInj (-(K Q₁ Q₂).zero.1 B) +
        zeroInj ⟨JordanTKK.tripleD ℝ B (K Q₁ Q₂).pos,
          h3zornTKKDatum.tripleD_mem_str B (K Q₁ Q₂).pos⟩ := by
    nth_rw 1 [hK]
    simp only [lie_add, negInj_bracket_negInj, negInj_bracket_zeroInj, negInj_bracket_posInj,
      zero_add]
  rw [hL]
  apply h3zornTKKLie_ext
  · simp only [h3tkk_add_neg, h3tkk_negInj_neg, h3tkk_zeroInj_neg, add_zero, K_neg,
      repNeg, LinearMap.coe_mk, AddHom.coe_mk, alpha_smul, x_smul, y_smul, K_zero,
      Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h3zornStrOne_apply, tripleD_apply_expanded,
      H3Zorn.crossProduct_smul_left, H3Zorn.crossProduct_smul_right,
      h3_crossProduct_neg_left, h3_crossProduct_neg_right, smul_add, smul_sub, smul_smul]
    rw [H3Zorn.crossProduct_symm B Q₁.x, H3Zorn.crossProduct_symm Q₁.y (H3Zorn.crossProduct B Q₂.x),
      H3Zorn.crossProduct_symm B Q₂.x]
    norm_num
    module
  · apply Subtype.ext
    apply LinearMap.ext; intro w
    have hpol := polarized_mccrimmon_12_tripleD_right Q₁.x Q₂.x B w
    have htr1 : H3Zorn.traceBilin Q₂.x (H3Zorn.crossProduct B Q₁.x) =
        H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.x Q₂.x) B := by
      rw [H3Zorn.crossProduct_symm B Q₁.x, ← H3Zorn.traceBilin_crossProduct_assoc Q₂.x Q₁.x B,
        H3Zorn.crossProduct_symm Q₂.x Q₁.x]
    have htr2 : H3Zorn.traceBilin Q₁.x (H3Zorn.crossProduct B Q₂.x) =
        H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.x Q₂.x) B := by
      rw [H3Zorn.crossProduct_symm B Q₂.x, ← H3Zorn.traceBilin_crossProduct_assoc Q₁.x Q₂.x B]
    have hpol' : -JordanTKK.tripleD ℝ B (H3Zorn.crossProduct Q₁.x Q₂.x) w =
        JordanTKK.tripleD ℝ Q₁.x (H3Zorn.crossProduct Q₂.x B) w +
          JordanTKK.tripleD ℝ Q₂.x (H3Zorn.crossProduct Q₁.x B) w -
          H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.x Q₂.x) B • w := by
      have h0 : JordanTKK.tripleD ℝ B (H3Zorn.crossProduct Q₁.x Q₂.x) w =
          H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.x Q₂.x) B • w -
            (JordanTKK.tripleD ℝ Q₁.x (H3Zorn.crossProduct Q₂.x B) w +
              JordanTKK.tripleD ℝ Q₂.x (H3Zorn.crossProduct Q₁.x B) w) :=
        eq_sub_of_add_eq (by rw [← hpol]; abel)
      rw [h0]
      module
    simp only [h3tkk_add_zero, h3tkk_negInj_zero, h3tkk_zeroInj_zero, zero_add,
      Submodule.coe_add, Submodule.coe_smul, Subtype.coe_mk,
      LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, neg_add, K_zero, K_pos,
      repNeg, LinearMap.coe_mk, AddHom.coe_mk, alpha_smul, beta_smul, x_smul, y_smul,
      tripleD_neg_right, tripleD_add_right, tripleD_smul_right, tripleD_smul_left,
      H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right,
      h3_traceBilin_neg_right, h3zornStrOne_apply, htr1, htr2]
    rw [H3Zorn.crossProduct_symm B Q₁.x, H3Zorn.crossProduct_symm B Q₂.x, hpol']
    module
  · simp only [h3tkk_add_pos, h3tkk_negInj_pos, h3tkk_zeroInj_pos, add_zero, K_pos, repNeg,
      LinearMap.coe_mk, AddHom.coe_mk, beta_smul, x_smul, y_smul,
      H3Zorn.crossProduct_smul_left, H3Zorn.crossProduct_smul_right,
      H3Zorn.crossProduct_symm Q₁.x B, H3Zorn.crossProduct_symm B Q₂.x]
    module

private theorem K_equivariant_pos (A : H3Zorn ℝ) (Q₁ Q₂ : Charge) :
    ⁅posInj A, K Q₁ Q₂⁆ = K (repPos A Q₁) Q₂ + K Q₁ (repPos A Q₂) := by
  have hK : K Q₁ Q₂ =
      negInj (K Q₁ Q₂).neg + zeroInj (K Q₁ Q₂).zero + posInj (K Q₁ Q₂).pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) (K Q₁ Q₂)
  have hL : ⁅posInj A, K Q₁ Q₂⁆ =
      zeroInj ⟨-JordanTKK.tripleD ℝ (K Q₁ Q₂).neg A,
          h3zornTKKDatum.str.neg_mem (h3zornTKKDatum.tripleD_mem_str (K Q₁ Q₂).neg A)⟩ +
        posInj (h3zornTraceAdjoint (K Q₁ Q₂).zero.1 A) := by
    nth_rw 1 [hK]
    simp only [lie_add, posInj_bracket_negInj, posInj_bracket_zeroInj, posInj_bracket_posInj,
      add_zero]
  rw [hL]
  apply h3zornTKKLie_ext
  · simp only [h3tkk_add_neg, h3tkk_zeroInj_neg, h3tkk_posInj_neg, K_neg, repPos,
      LinearMap.coe_mk, AddHom.coe_mk, add_zero,
      H3Zorn.crossProduct_smul_left, H3Zorn.crossProduct_smul_right,
      H3Zorn.crossProduct_symm A Q₂.y, H3Zorn.crossProduct_symm A Q₁.y,
      smul_add, smul_neg, smul_smul]
    module
  · apply Subtype.ext
    apply LinearMap.ext; intro w
    have hpol := polarized_mccrimmon_12_tripleD Q₁.y Q₂.y A w
    have htr1 : H3Zorn.traceBilin (H3Zorn.crossProduct A Q₁.y) Q₂.y =
        H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.y Q₂.y) A := by
      rw [H3Zorn.crossProduct_symm A Q₁.y, H3Zorn.traceBilin_crossProduct_assoc Q₁.y A Q₂.y,
        H3Zorn.crossProduct_symm A Q₂.y, ← H3Zorn.traceBilin_crossProduct_assoc Q₁.y Q₂.y A]
    have htr2 : H3Zorn.traceBilin (H3Zorn.crossProduct A Q₂.y) Q₁.y =
        H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.y Q₂.y) A := by
      rw [H3Zorn.crossProduct_symm A Q₂.y, H3Zorn.traceBilin_crossProduct_assoc Q₂.y A Q₁.y,
        H3Zorn.crossProduct_symm A Q₁.y, ← H3Zorn.traceBilin_crossProduct_assoc Q₂.y Q₁.y A,
        H3Zorn.crossProduct_symm Q₂.y Q₁.y]
    have hpol0 : JordanTKK.tripleD ℝ (H3Zorn.crossProduct Q₁.y Q₂.y) A w =
        H3Zorn.traceBilin (H3Zorn.crossProduct Q₁.y Q₂.y) A • w -
          (JordanTKK.tripleD ℝ (H3Zorn.crossProduct Q₁.y A) Q₂.y w +
            JordanTKK.tripleD ℝ (H3Zorn.crossProduct Q₂.y A) Q₁.y w) :=
      eq_sub_of_add_eq (by rw [← hpol]; abel)
    simp only [h3tkk_add_zero, h3tkk_zeroInj_zero, h3tkk_posInj_zero, add_zero,
      Submodule.coe_add, Submodule.coe_smul, Subtype.coe_mk,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, neg_add,
      K_zero, K_neg, repPos, LinearMap.coe_mk, AddHom.coe_mk,
      tripleD_smul_left, tripleD_add_left, tripleD_neg_left, tripleD_smul_right,
      H3Zorn.traceBilin_smul_right, h3_traceBilin_neg_left, h3zornStrOne_apply,
      htr1, htr2, smul_add]
    rw [H3Zorn.crossProduct_symm A Q₁.y, H3Zorn.crossProduct_symm A Q₂.y, hpol0,
      H3Zorn.traceBilin_symm A Q₁.x, H3Zorn.traceBilin_symm A Q₂.x]
    module
  · have hadj1 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₁.x Q₂.y) A =
        JordanTKK.tripleD ℝ Q₂.y Q₁.x A :=
      congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f A) (h3zornTKKDatum.adj_tripleD Q₁.x Q₂.y)
    have hadj2 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₂.x Q₁.y) A =
        JordanTKK.tripleD ℝ Q₁.y Q₂.x A :=
      congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f A) (h3zornTKKDatum.adj_tripleD Q₂.x Q₁.y)
    have hadj_K : h3zornTraceAdjoint (K Q₁ Q₂).zero.1 A =
        (-2 : ℝ) • (JordanTKK.tripleD ℝ Q₂.y Q₁.x A + JordanTKK.tripleD ℝ Q₁.y Q₂.x A) +
        (-(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
          H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y) • A := by
      change h3zornTraceAdjointLM (K Q₁ Q₂).zero.1 A = _
      simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, h3zornTraceAdjointLM_apply,
        hadj1, hadj2, h3zornTraceAdjoint_h3zornStrOne, h3zornStrOne_apply]
    simp only [h3tkk_add_pos, h3tkk_zeroInj_pos, h3tkk_posInj_pos,
      zero_add, hadj_K, K_pos, repPos, LinearMap.coe_mk, AddHom.coe_mk,
      tripleD_apply_expanded, h3_crossProduct_neg_left, h3_crossProduct_neg_right,
      H3Zorn.crossProduct_symm A Q₂.y, H3Zorn.crossProduct_symm A Q₁.y,
      H3Zorn.crossProduct_symm Q₁.x (H3Zorn.crossProduct Q₂.y A),
      H3Zorn.traceBilin_symm Q₂.y Q₁.x, H3Zorn.traceBilin_symm Q₁.y Q₂.x,
      H3Zorn.traceBilin_symm A Q₁.x, H3Zorn.traceBilin_symm A Q₂.x,
      smul_add, smul_sub, smul_smul]
    norm_num
    module

private theorem K_equivariant_zero (T₀ : h3zornTKKDatum.str) (Q₁ Q₂ : Charge) :
    ⁅zeroInj T₀, K Q₁ Q₂⁆ = K (repZero T₀ Q₁) Q₂ + K Q₁ (repZero T₀ Q₂) := by
  have hK : K Q₁ Q₂ =
      negInj (K Q₁ Q₂).neg + zeroInj (K Q₁ Q₂).zero + posInj (K Q₁ Q₂).pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) (K Q₁ Q₂)
  have hL : ⁅zeroInj T₀, K Q₁ Q₂⁆ =
      negInj (T₀.1 (K Q₁ Q₂).neg) +
        zeroInj ⟨T₀.1 ∘ₗ (K Q₁ Q₂).zero.1 - (K Q₁ Q₂).zero.1 ∘ₗ T₀.1,
          h3zornTKKDatum.str_lie_mem T₀.2 (K Q₁ Q₂).zero.2⟩ +
        posInj (-h3zornTraceAdjoint T₀.1 (K Q₁ Q₂).pos) := by
    nth_rw 1 [hK]
    simp only [lie_add, zeroInj_bracket_negInj, zeroInj_bracket_zeroInj, zeroInj_bracket_posInj]
  rw [hL]
  apply h3zornTKKLie_ext
  · have hcr := str_crossProduct_rule_adj T₀ Q₁.y Q₂.y
    have hcr0 : H3Zorn.linearTrace (T₀.1 1) = strTrace T₀ := rfl
    rw [hcr0] at hcr
    have hcr' : T₀.1 (H3Zorn.crossProduct Q₁.y Q₂.y) =
        strTrace T₀ • H3Zorn.crossProduct Q₁.y Q₂.y -
          (H3Zorn.crossProduct (h3zornTraceAdjoint T₀.1 Q₁.y) Q₂.y +
            H3Zorn.crossProduct Q₁.y (h3zornTraceAdjoint T₀.1 Q₂.y)) :=
      eq_sub_of_add_eq (by rw [← hcr]; abel)
    simp only [h3tkk_add_neg, h3tkk_negInj_neg, h3tkk_zeroInj_neg, h3tkk_posInj_neg,
      h3tkk_smul_neg, add_zero, K_neg, map_smul, map_add, hcr', repZero,
      LinearMap.coe_mk, AddHom.coe_mk, H3Zorn.crossProduct_add_left,
      H3Zorn.crossProduct_add_right, h3_crossProduct_neg_left, h3_crossProduct_neg_right,
      H3Zorn.crossProduct_smul_left, H3Zorn.crossProduct_smul_right,
      smul_add, smul_sub, smul_neg, smul_smul]
    norm_num
    module
  · apply Subtype.ext
    have hc1 := h3zornTKKDatum.str_comm_tripleD T₀ Q₁.x Q₂.y
    have hc2 := h3zornTKKDatum.str_comm_tripleD T₀ Q₂.x Q₁.y
    have hpair1 := h3zornTraceAdjoint_pair T₀.1 Q₂.y Q₁.x
    have hpair2 := h3zornTraceAdjoint_pair T₀.1 Q₁.y Q₂.x
    rw [H3Zorn.traceBilin_symm (h3zornTraceAdjoint T₀.1 Q₂.y) Q₁.x,
      H3Zorn.traceBilin_symm Q₂.y (T₀.1 Q₁.x)] at hpair1
    rw [H3Zorn.traceBilin_symm (h3zornTraceAdjoint T₀.1 Q₁.y) Q₂.x,
      H3Zorn.traceBilin_symm Q₁.y (T₀.1 Q₂.x)] at hpair2
    simp only [h3tkk_add_zero, h3tkk_negInj_zero, h3tkk_zeroInj_zero, h3tkk_posInj_zero,
      zero_add, add_zero, Subtype.coe_mk, Submodule.coe_add, repZero,
      LinearMap.coe_mk, AddHom.coe_mk]
    apply LinearMap.ext; intro w
    have hc1w : T₀.1 (JordanTKK.tripleD ℝ Q₁.x Q₂.y w) -
          JordanTKK.tripleD ℝ Q₁.x Q₂.y (T₀.1 w) =
        JordanTKK.tripleD ℝ (T₀.1 Q₁.x) Q₂.y w -
          JordanTKK.tripleD ℝ Q₁.x (h3zornTraceAdjoint T₀.1 Q₂.y) w :=
      congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f w) hc1
    have hc2w : T₀.1 (JordanTKK.tripleD ℝ Q₂.x Q₁.y w) -
          JordanTKK.tripleD ℝ Q₂.x Q₁.y (T₀.1 w) =
        JordanTKK.tripleD ℝ (T₀.1 Q₂.x) Q₁.y w -
          JordanTKK.tripleD ℝ Q₂.x (h3zornTraceAdjoint T₀.1 Q₁.y) w :=
      congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f w) hc2
    have hc1w' : T₀.1 (JordanTKK.tripleD ℝ Q₁.x Q₂.y w) =
        JordanTKK.tripleD ℝ Q₁.x Q₂.y (T₀.1 w) +
          (JordanTKK.tripleD ℝ (T₀.1 Q₁.x) Q₂.y w -
            JordanTKK.tripleD ℝ Q₁.x (h3zornTraceAdjoint T₀.1 Q₂.y) w) := by
      rw [← hc1w]; abel
    have hc2w' : T₀.1 (JordanTKK.tripleD ℝ Q₂.x Q₁.y w) =
        JordanTKK.tripleD ℝ Q₂.x Q₁.y (T₀.1 w) +
          (JordanTKK.tripleD ℝ (T₀.1 Q₂.x) Q₁.y w -
            JordanTKK.tripleD ℝ Q₂.x (h3zornTraceAdjoint T₀.1 Q₁.y) w) := by
      rw [← hc2w]; abel
    have hstr_comm :
        T₀.1 ((K Q₁ Q₂).zero.1 w) - (K Q₁ Q₂).zero.1 (T₀.1 w) =
          (-2 : ℝ) • ((JordanTKK.tripleD ℝ (T₀.1 Q₁.x) Q₂.y w -
              JordanTKK.tripleD ℝ Q₁.x (h3zornTraceAdjoint T₀.1 Q₂.y) w) +
            (JordanTKK.tripleD ℝ (T₀.1 Q₂.x) Q₁.y w -
              JordanTKK.tripleD ℝ Q₂.x (h3zornTraceAdjoint T₀.1 Q₁.y) w)) := by
      simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply,
        LinearMap.smul_apply, h3zornStrOne_apply, map_add, map_smul, hc1w', hc2w']
      module
    have hL0 : (T₀.1 ∘ₗ (K Q₁ Q₂).zero.1 - (K Q₁ Q₂).zero.1 ∘ₗ T₀.1) w =
        T₀.1 ((K Q₁ Q₂).zero.1 w) - (K Q₁ Q₂).zero.1 (T₀.1 w) := rfl
    rw [hL0, hstr_comm]
    simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.neg_apply, h3zornStrOne_apply,
      tripleD_add_right, tripleD_neg_right, tripleD_smul_right,
      H3Zorn.traceBilin_add_right, H3Zorn.traceBilin_sub_left,
      H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right,
      h3_traceBilin_neg_right]
    rw [show JordanTKK.tripleD ℝ (T₀.1 Q₁.x - ((1 / 2 : ℝ) * strTrace T₀) • Q₁.x) Q₂.y w =
        JordanTKK.tripleD ℝ (T₀.1 Q₁.x) Q₂.y w -
          ((1 / 2 : ℝ) * strTrace T₀) • JordanTKK.tripleD ℝ Q₁.x Q₂.y w by
        rw [sub_eq_add_neg, tripleD_add_left, tripleD_neg_left, tripleD_smul_left]; rfl,
      show JordanTKK.tripleD ℝ (T₀.1 Q₂.x - ((1 / 2 : ℝ) * strTrace T₀) • Q₂.x) Q₁.y w =
        JordanTKK.tripleD ℝ (T₀.1 Q₂.x) Q₁.y w -
          ((1 / 2 : ℝ) * strTrace T₀) • JordanTKK.tripleD ℝ Q₂.x Q₁.y w by
        rw [sub_eq_add_neg, tripleD_add_left, tripleD_neg_left, tripleD_smul_left]; rfl,
      hpair1, hpair2]
    module
  · have hcr := str_crossProduct_rule T₀ Q₁.x Q₂.x
    have hcr0 : H3Zorn.linearTrace (T₀.1 1) = strTrace T₀ := rfl
    rw [hcr0] at hcr
    have hcr' : h3zornTraceAdjoint T₀.1 (H3Zorn.crossProduct Q₁.x Q₂.x) =
        strTrace T₀ • H3Zorn.crossProduct Q₁.x Q₂.x -
          (H3Zorn.crossProduct (T₀.1 Q₁.x) Q₂.x + H3Zorn.crossProduct Q₁.x (T₀.1 Q₂.x)) :=
      eq_sub_of_add_eq (by rw [← hcr]; abel)
    simp only [h3tkk_add_pos, h3tkk_negInj_pos, h3tkk_zeroInj_pos, h3tkk_posInj_pos,
      zero_add, K_pos, map_neg, map_add, map_smul, neg_neg, hcr', repZero,
      LinearMap.coe_mk, AddHom.coe_mk,
      show H3Zorn.crossProduct (T₀.1 Q₁.x - ((1 / 2 : ℝ) * strTrace T₀) • Q₁.x) Q₂.x =
        H3Zorn.crossProduct (T₀.1 Q₁.x) Q₂.x -
          ((1 / 2 : ℝ) * strTrace T₀) • H3Zorn.crossProduct Q₁.x Q₂.x by
        rw [sub_eq_add_neg, H3Zorn.crossProduct_add_left, h3_crossProduct_neg_left,
          H3Zorn.crossProduct_smul_left]; module,
      show H3Zorn.crossProduct Q₁.x (T₀.1 Q₂.x - ((1 / 2 : ℝ) * strTrace T₀) • Q₂.x) =
        H3Zorn.crossProduct Q₁.x (T₀.1 Q₂.x) -
          ((1 / 2 : ℝ) * strTrace T₀) • H3Zorn.crossProduct Q₁.x Q₂.x by
        rw [sub_eq_add_neg, H3Zorn.crossProduct_add_right, h3_crossProduct_neg_right,
          H3Zorn.crossProduct_smul_right]; module,
      smul_add, smul_smul]
    norm_num
    module

/-- `H3ZornTKKLie`-equivariance of `K : Charge →ₗ[ℝ] Charge →ₗ[ℝ] H3ZornTKKLie`. -/
theorem K_equivariant (X : H3ZornTKKLie) (Q₁ Q₂ : Charge) :
    ⁅X, K Q₁ Q₂⁆ = K (repE7 X Q₁) Q₂ + K Q₁ (repE7 X Q₂) := by
  have hX : X = negInj X.neg + zeroInj X.zero + posInj X.pos :=
    JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X
  rw [hX, add_lie, add_lie, K_equivariant_neg, K_equivariant_zero, K_equivariant_pos]
  simp only [map_add, LinearMap.add_apply, repE7_negInj, repE7_zeroInj, repE7_posInj]
  abel

/-- Fundamental cubic Freudenthal triple identity on `(g₊₁, g₋₁, g₊₁)`. -/
theorem triple_identity_p1_m1_p1 (Q₁ Q₂ Q₃ : Charge) :
    repE7 (K Q₁ Q₂) Q₃ - repE7 (K Q₃ Q₂) Q₁ =
      (1 / 2 : ℝ) • (symplecticForm Q₁ Q₂ • Q₃ - symplecticForm Q₃ Q₂ • Q₁) +
        symplecticForm Q₁ Q₃ • Q₂ := by
  have hst12 := K_zero_strTrace Q₁ Q₂
  have hst32 := K_zero_strTrace Q₃ Q₂
  apply FreudenthalCharge.ext
  · simp only [charge_sub_alpha, alpha_add, alpha_smul, repE7_alpha, K_neg, hst12, hst32,
      symplecticForm_expanded, H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_smul_left,
      H3Zorn.traceBilin_symm Q₂.x Q₁.y, H3Zorn.traceBilin_symm Q₂.x Q₃.y,
      H3Zorn.traceBilin_symm Q₃.x Q₂.y, H3Zorn.traceBilin_symm Q₁.x Q₂.y,
      H3Zorn.traceBilin_symm Q₃.x Q₁.y,
      H3Zorn.traceBilin_crossProduct_assoc]
    rw [H3Zorn.crossProduct_symm Q₂.y Q₁.y,
      H3Zorn.traceBilin_symm Q₃.y (H3Zorn.crossProduct Q₁.y Q₂.y),
      H3Zorn.traceBilin_crossProduct_assoc Q₁.y Q₂.y Q₃.y]
    ring
  · simp only [charge_sub_beta, beta_add, beta_smul, repE7_beta, K_pos, hst12, hst32,
      symplecticForm_expanded, h3_traceBilin_neg_left, H3Zorn.traceBilin_add_left,
      H3Zorn.traceBilin_smul_left,
      H3Zorn.traceBilin_symm Q₁.y Q₃.x, H3Zorn.traceBilin_symm Q₂.y Q₃.x,
      H3Zorn.traceBilin_symm Q₃.y Q₁.x, H3Zorn.traceBilin_symm Q₂.y Q₁.x,
      H3Zorn.traceBilin_symm Q₁.y Q₂.x, H3Zorn.traceBilin_symm Q₃.y Q₂.x,
      H3Zorn.traceBilin_crossProduct_assoc]
    rw [H3Zorn.crossProduct_symm Q₂.x Q₁.x,
      H3Zorn.traceBilin_symm Q₃.x (H3Zorn.crossProduct Q₁.x Q₂.x),
      H3Zorn.traceBilin_crossProduct_assoc Q₁.x Q₂.x Q₃.x]
    ring
  · simp only [charge_sub_x, x_add, x_smul, repE7_x]
    rw [hst12, hst32]
    simp only [K_neg, K_pos, K_zero, Submodule.coe_add, Submodule.coe_smul,
      LinearMap.add_apply, LinearMap.smul_apply, h3zornStrOne_apply, tripleD_apply_expanded,
      symplecticForm_expanded, h3_crossProduct_neg_left, H3Zorn.crossProduct_add_left,
      H3Zorn.crossProduct_smul_left,
      H3Zorn.crossProduct_symm Q₂.y Q₁.y, H3Zorn.crossProduct_symm Q₃.y Q₂.y,
      H3Zorn.crossProduct_symm Q₃.y Q₁.y,
      H3Zorn.crossProduct_symm Q₃.x Q₁.x, H3Zorn.crossProduct_symm Q₃.x Q₂.x,
      H3Zorn.crossProduct_symm Q₂.x Q₁.x,
      H3Zorn.traceBilin_symm Q₁.y Q₃.x, H3Zorn.traceBilin_symm Q₁.y Q₂.x,
      H3Zorn.traceBilin_symm Q₃.y Q₂.x]
    module
  · have hadj12 : h3zornTraceAdjoint (K Q₁ Q₂).zero.1 Q₃.y =
        (-2 : ℝ) • (JordanTKK.tripleD ℝ Q₂.y Q₁.x Q₃.y + JordanTKK.tripleD ℝ Q₁.y Q₂.x Q₃.y) +
        (-(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
          H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y) • Q₃.y := by
      have ha1 : (h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₁.x Q₂.y)) Q₃.y =
          JordanTKK.tripleD ℝ Q₂.y Q₁.x Q₃.y :=
        congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f Q₃.y)
          (h3zornTKKDatum.adj_tripleD Q₁.x Q₂.y)
      have ha2 : (h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₂.x Q₁.y)) Q₃.y =
          JordanTKK.tripleD ℝ Q₁.y Q₂.x Q₃.y :=
        congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f Q₃.y)
          (h3zornTKKDatum.adj_tripleD Q₂.x Q₁.y)
      change h3zornTraceAdjointLM (K Q₁ Q₂).zero.1 Q₃.y = _
      simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, h3zornTraceAdjointLM_apply,
        ha1, ha2, h3zornTraceAdjoint_h3zornStrOne, h3zornStrOne_apply]
    have hadj32 : h3zornTraceAdjoint (K Q₃ Q₂).zero.1 Q₁.y =
        (-2 : ℝ) • (JordanTKK.tripleD ℝ Q₂.y Q₃.x Q₁.y + JordanTKK.tripleD ℝ Q₃.y Q₂.x Q₁.y) +
        (-(Q₃.alpha * Q₂.beta + Q₃.beta * Q₂.alpha) +
          H3Zorn.traceBilin Q₃.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₃.y) • Q₁.y := by
      have ha1 : (h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₃.x Q₂.y)) Q₁.y =
          JordanTKK.tripleD ℝ Q₂.y Q₃.x Q₁.y :=
        congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f Q₁.y)
          (h3zornTKKDatum.adj_tripleD Q₃.x Q₂.y)
      have ha2 : (h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₂.x Q₃.y)) Q₁.y =
          JordanTKK.tripleD ℝ Q₃.y Q₂.x Q₁.y :=
        congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f Q₁.y)
          (h3zornTKKDatum.adj_tripleD Q₂.x Q₃.y)
      change h3zornTraceAdjointLM (K Q₃ Q₂).zero.1 Q₁.y = _
      simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, h3zornTraceAdjointLM_apply,
        ha1, ha2, h3zornTraceAdjoint_h3zornStrOne, h3zornStrOne_apply]
    simp only [charge_sub_y, y_add, y_smul, repE7_y, hst12, hst32, hadj12, hadj32, K_neg, K_pos,
      tripleD_apply_expanded, symplecticForm_expanded,
      H3Zorn.crossProduct_add_left, H3Zorn.crossProduct_smul_left,
      H3Zorn.crossProduct_symm Q₂.x Q₁.x, H3Zorn.crossProduct_symm Q₃.x Q₂.x,
      H3Zorn.crossProduct_symm Q₃.x Q₁.x,
      H3Zorn.crossProduct_symm Q₃.y Q₁.y, H3Zorn.crossProduct_symm Q₃.y Q₂.y,
      H3Zorn.crossProduct_symm Q₂.y Q₁.y,
      H3Zorn.traceBilin_symm Q₃.y Q₁.x, H3Zorn.traceBilin_symm Q₃.y Q₂.x,
      H3Zorn.traceBilin_symm Q₂.y Q₁.x, H3Zorn.traceBilin_symm Q₂.y Q₃.x,
      H3Zorn.traceBilin_symm Q₁.y Q₂.x, H3Zorn.traceBilin_symm Q₁.y Q₃.x]
    module

/-- The full 248-dimensional 5-graded Lie bracket on `FreudenthalTKK5E8` as a bilinear map. -/
def bracket5LM : FreudenthalTKK5E8 →ₗ[ℝ] FreudenthalTKK5E8 →ₗ[ℝ] FreudenthalTKK5E8 where
  toFun U :=
    { toFun := fun V =>
        { gMinus2 := -2 * U.gZeroCenter * V.gMinus2 + 2 * V.gZeroCenter * U.gMinus2 -
            symplecticForm U.gMinus1 V.gMinus1
          gMinus1 := repE7 U.gZeroE7 V.gMinus1 - repE7 V.gZeroE7 U.gMinus1 -
            U.gZeroCenter • V.gMinus1 + V.gZeroCenter • U.gMinus1 +
            U.gMinus2 • V.gPlus1 - V.gMinus2 • U.gPlus1
          gZeroE7 := ⁅U.gZeroE7, V.gZeroE7⁆ + K U.gPlus1 V.gMinus1 - K V.gPlus1 U.gMinus1
          gZeroCenter := (U.gPlus2 * V.gMinus2 - V.gPlus2 * U.gMinus2) -
            (1 / 2 : ℝ) * (symplecticForm U.gPlus1 V.gMinus1 - symplecticForm V.gPlus1 U.gMinus1)
          gPlus1 := repE7 U.gZeroE7 V.gPlus1 - repE7 V.gZeroE7 U.gPlus1 +
            U.gZeroCenter • V.gPlus1 - V.gZeroCenter • U.gPlus1 +
            U.gPlus2 • V.gMinus1 - V.gPlus2 • U.gMinus1
          gPlus2 := 2 * U.gZeroCenter * V.gPlus2 - 2 * V.gZeroCenter * U.gPlus2 +
            symplecticForm U.gPlus1 V.gPlus1 }
      map_add' V₁ V₂ := by
        apply FreudenthalTKK5E8.ext <;>
          simp only [add_gMinus2, add_gMinus1, add_gZeroE7, add_gZeroCenter, add_gPlus1,
            add_gPlus2, map_add, LinearMap.add_apply, lie_add, smul_add, add_smul,
            symp_add_left, symp_add_right]
        · ring
        · module
        · abel
        · ring
        · module
        · ring
      map_smul' r V := by
        apply FreudenthalTKK5E8.ext <;>
          simp only [smul_gMinus2, smul_gMinus1, smul_gZeroE7, smul_gZeroCenter, smul_gPlus1,
            smul_gPlus2, RingHom.id_apply, map_smul, LinearMap.smul_apply, lie_smul,
            symp_smul_right, symp_smul_left, smul_smul]
        · ring
        · rw [show U.gZeroCenter * r = r * U.gZeroCenter by ring,
            show U.gMinus2 * r = r * U.gMinus2 by ring]
          module
        · rw [smul_sub, smul_add]
        · ring
        · rw [show U.gZeroCenter * r = r * U.gZeroCenter by ring,
            show U.gPlus2 * r = r * U.gPlus2 by ring]
          module
        · ring }
  map_add' U₁ U₂ := by
    apply LinearMap.ext; intro V
    apply FreudenthalTKK5E8.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        add_gMinus2, add_gMinus1, add_gZeroE7, add_gZeroCenter, add_gPlus1, add_gPlus2,
        map_add, LinearMap.add_apply, add_lie, smul_add, add_smul,
        symp_add_left, symp_add_right]
    · ring
    · module
    · abel
    · ring
    · module
    · ring
  map_smul' r U := by
    apply LinearMap.ext; intro V
    apply FreudenthalTKK5E8.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
        smul_gMinus2, smul_gMinus1, smul_gZeroE7, smul_gZeroCenter, smul_gPlus1, smul_gPlus2,
        map_smul, LinearMap.smul_apply, smul_lie, symp_smul_left, symp_smul_right, smul_smul]
    · ring
    · rw [show V.gZeroCenter * r = r * V.gZeroCenter by ring,
        show V.gMinus2 * r = r * V.gMinus2 by ring]
      module
    · rw [smul_sub, smul_add]
    · ring
    · rw [show V.gZeroCenter * r = r * V.gZeroCenter by ring,
        show V.gPlus2 * r = r * V.gPlus2 by ring]
      module
    · ring

@[simp] theorem bracket5LM_gMinus2 (U V : FreudenthalTKK5E8) :
    (bracket5LM U V).gMinus2 =
      -2 * U.gZeroCenter * V.gMinus2 + 2 * V.gZeroCenter * U.gMinus2 -
        symplecticForm U.gMinus1 V.gMinus1 := rfl

@[simp] theorem bracket5LM_gMinus1 (U V : FreudenthalTKK5E8) :
    (bracket5LM U V).gMinus1 =
      repE7 U.gZeroE7 V.gMinus1 - repE7 V.gZeroE7 U.gMinus1 -
        U.gZeroCenter • V.gMinus1 + V.gZeroCenter • U.gMinus1 +
        U.gMinus2 • V.gPlus1 - V.gMinus2 • U.gPlus1 := rfl

@[simp] theorem bracket5LM_gZeroE7 (U V : FreudenthalTKK5E8) :
    (bracket5LM U V).gZeroE7 =
      ⁅U.gZeroE7, V.gZeroE7⁆ + K U.gPlus1 V.gMinus1 - K V.gPlus1 U.gMinus1 := rfl

@[simp] theorem bracket5LM_gZeroCenter (U V : FreudenthalTKK5E8) :
    (bracket5LM U V).gZeroCenter =
      (U.gPlus2 * V.gMinus2 - V.gPlus2 * U.gMinus2) -
        (1 / 2 : ℝ) * (symplecticForm U.gPlus1 V.gMinus1 - symplecticForm V.gPlus1 U.gMinus1) := rfl

@[simp] theorem bracket5LM_gPlus1 (U V : FreudenthalTKK5E8) :
    (bracket5LM U V).gPlus1 =
      repE7 U.gZeroE7 V.gPlus1 - repE7 V.gZeroE7 U.gPlus1 +
        U.gZeroCenter • V.gPlus1 - V.gZeroCenter • U.gPlus1 +
        U.gPlus2 • V.gMinus1 - V.gPlus2 • U.gMinus1 := rfl

@[simp] theorem bracket5LM_gPlus2 (U V : FreudenthalTKK5E8) :
    (bracket5LM U V).gPlus2 =
      2 * U.gZeroCenter * V.gPlus2 - 2 * V.gZeroCenter * U.gPlus2 +
        symplecticForm U.gPlus1 V.gPlus1 := rfl

theorem bracket5LM_self (U : FreudenthalTKK5E8) : bracket5LM U U = 0 := by
  apply FreudenthalTKK5E8.ext <;>
    simp only [bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
      bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2,
      zero_gMinus2, zero_gMinus1, zero_gZeroE7, zero_gZeroCenter, zero_gPlus1, zero_gPlus2,
      symplecticForm_self, lie_self]
  · ring
  · module
  · abel
  · ring
  · module
  · ring

theorem bracket5LM_antisymm (U V : FreudenthalTKK5E8) :
    bracket5LM U V = -bracket5LM V U := by
  apply FreudenthalTKK5E8.ext <;>
    simp only [bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
      bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2,
      neg_gMinus2, neg_gMinus1, neg_gZeroE7, neg_gZeroCenter, neg_gPlus1, neg_gPlus2,
      symplecticForm_skew U.gMinus1 V.gMinus1, symplecticForm_skew U.gPlus1 V.gPlus1]
  · ring
  · module
  · rw [← lie_skew V.gZeroE7 U.gZeroE7]; abel
  · ring
  · module
  · ring

/-- Canonical grade `-2` embedding `ℝ →ₗ[ℝ] FreudenthalTKK5E8`. -/
def injMinus2 : ℝ →ₗ[ℝ] FreudenthalTKK5E8 where
  toFun a := ⟨a, 0, 0, 0, 0, 0⟩
  map_add' a b := by apply FreudenthalTKK5E8.ext <;> simp
  map_smul' r a := by apply FreudenthalTKK5E8.ext <;> simp

/-- Canonical grade `-1` embedding `Charge →ₗ[ℝ] FreudenthalTKK5E8`. -/
def injMinus1 : Charge →ₗ[ℝ] FreudenthalTKK5E8 where
  toFun Q := ⟨0, Q, 0, 0, 0, 0⟩
  map_add' _ _ := by apply FreudenthalTKK5E8.ext <;> simp
  map_smul' _ _ := by apply FreudenthalTKK5E8.ext <;> simp

/-- Canonical grade `0` `E₇` embedding `H3ZornTKKLie →ₗ[ℝ] FreudenthalTKK5E8`. -/
def injZeroE7 : H3ZornTKKLie →ₗ[ℝ] FreudenthalTKK5E8 where
  toFun X := ⟨0, 0, X, 0, 0, 0⟩
  map_add' _ _ := by apply FreudenthalTKK5E8.ext <;> simp
  map_smul' _ _ := by apply FreudenthalTKK5E8.ext <;> simp

/-- Canonical grade `0` central embedding `ℝ →ₗ[ℝ] FreudenthalTKK5E8`. -/
def injZeroCenter : ℝ →ₗ[ℝ] FreudenthalTKK5E8 where
  toFun c := ⟨0, 0, 0, c, 0, 0⟩
  map_add' a b := by apply FreudenthalTKK5E8.ext <;> simp
  map_smul' r a := by apply FreudenthalTKK5E8.ext <;> simp

/-- Canonical grade `+1` embedding `Charge →ₗ[ℝ] FreudenthalTKK5E8`. -/
def injPlus1 : Charge →ₗ[ℝ] FreudenthalTKK5E8 where
  toFun Q := ⟨0, 0, 0, 0, Q, 0⟩
  map_add' _ _ := by apply FreudenthalTKK5E8.ext <;> simp
  map_smul' _ _ := by apply FreudenthalTKK5E8.ext <;> simp

/-- Canonical grade `+2` embedding `ℝ →ₗ[ℝ] FreudenthalTKK5E8`. -/
def injPlus2 : ℝ →ₗ[ℝ] FreudenthalTKK5E8 where
  toFun b := ⟨0, 0, 0, 0, 0, b⟩
  map_add' a b := by apply FreudenthalTKK5E8.ext <;> simp
  map_smul' r a := by apply FreudenthalTKK5E8.ext <;> simp

/-- Distinguished grading element `Z = injZeroCenter 1` (`ad(Z)` has eigenvalues `-2, -1, 0, +1, +2`). -/
def gradeCenterZ : FreudenthalTKK5E8 := injZeroCenter 1

/-- Distinguished grade `+2` root vector `e₊₂ = injPlus2 1`. -/
def ePlus2 : FreudenthalTKK5E8 := injPlus2 1

/-- Distinguished grade `-2` root vector `e₋₂ = injMinus2 1`. -/
def eMinus2 : FreudenthalTKK5E8 := injMinus2 1

private def proj6 : Fin 6 → FreudenthalTKK5E8 →ₗ[ℝ] FreudenthalTKK5E8
  | ⟨0, _⟩ => { toFun := fun U => injMinus2 U.gMinus2, map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by apply FreudenthalTKK5E8.ext <;> simp [injMinus2] }
  | ⟨1, _⟩ => { toFun := fun U => injMinus1 U.gMinus1, map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by simp }
  | ⟨2, _⟩ => { toFun := fun U => injZeroE7 U.gZeroE7, map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by simp }
  | ⟨3, _⟩ => { toFun := fun U => injZeroCenter U.gZeroCenter, map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by apply FreudenthalTKK5E8.ext <;> simp [injZeroCenter] }
  | ⟨4, _⟩ => { toFun := fun U => injPlus1 U.gPlus1, map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by simp }
  | ⟨5, _⟩ => { toFun := fun U => injPlus2 U.gPlus2, map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by apply FreudenthalTKK5E8.ext <;> simp [injPlus2] }

private theorem sum_proj6 (U : FreudenthalTKK5E8) : ∑ i : Fin 6, proj6 i U = U := by
  rw [Fin.sum_univ_six]
  apply FreudenthalTKK5E8.ext <;>
    simp [proj6, injMinus2, injMinus1, injZeroE7, injZeroCenter, injPlus1, injPlus2]

@[simp] private theorem injMinus2_eq (a : ℝ) : injMinus2 a = ⟨a, 0, 0, 0, 0, 0⟩ := rfl
@[simp] private theorem injMinus1_eq (Q : Charge) : injMinus1 Q = ⟨0, Q, 0, 0, 0, 0⟩ := rfl
@[simp] private theorem injZeroE7_eq (X : H3ZornTKKLie) : injZeroE7 X = ⟨0, 0, X, 0, 0, 0⟩ := rfl
@[simp] private theorem injZeroCenter_eq (c : ℝ) : injZeroCenter c = ⟨0, 0, 0, c, 0, 0⟩ := rfl
@[simp] private theorem injPlus1_eq (Q : Charge) : injPlus1 Q = ⟨0, 0, 0, 0, Q, 0⟩ := rfl
@[simp] private theorem injPlus2_eq (b : ℝ) : injPlus2 b = ⟨0, 0, 0, 0, 0, b⟩ := rfl

private theorem leibnizDefect_eq_jacobi (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM x y z =
      bracket5LM x (bracket5LM y z) + bracket5LM y (bracket5LM z x) +
        bracket5LM z (bracket5LM x y) := by
  dsimp [InfoGeometry.Exceptional.leibnizDefect]
  rw [bracket5LM_antisymm (bracket5LM x y) z, bracket5LM_antisymm x z, map_neg]
  abel

private theorem leibnizDefect_swap₁₂ (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM x y z =
      -InfoGeometry.Exceptional.leibnizDefect bracket5LM y x z := by
  rw [leibnizDefect_eq_jacobi, leibnizDefect_eq_jacobi,
    bracket5LM_antisymm x z, bracket5LM_antisymm y z, bracket5LM_antisymm x y]
  simp only [map_neg]
  abel

private theorem leibnizDefect_cycle (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM x y z =
      InfoGeometry.Exceptional.leibnizDefect bracket5LM y z x := by
  rw [leibnizDefect_eq_jacobi, leibnizDefect_eq_jacobi]
  abel

private theorem leibnizDefect_swap₂₃ (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM x y z =
      -InfoGeometry.Exceptional.leibnizDefect bracket5LM x z y := by
  rw [leibnizDefect_cycle, leibnizDefect_swap₁₂, ← leibnizDefect_cycle]

private theorem leibnizDefect_bracket5LM_eq_zero_of_abs_gt_two (i j k : Fin 6)
    (hi : ∀ x y z : FreudenthalTKK5E8,
      InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 i x) (proj6 j y) (proj6 k z) = 0) :
    ∀ x y z, InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 i x) (proj6 j y) (proj6 k z) = 0 :=
  hi

-- Helper evaluating `bracket5LM` on each pair of pure grade summands
@[simp] private theorem br_m2_m2 (a b : ℝ) : bracket5LM (injMinus2 a) (injMinus2 b) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m2_m1 (a : ℝ) (Q : Charge) : bracket5LM (injMinus2 a) (injMinus1 Q) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m2_zE7 (a : ℝ) (X : H3ZornTKKLie) : bracket5LM (injMinus2 a) (injZeroE7 X) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m2_zC (a c : ℝ) : bracket5LM (injMinus2 a) (injZeroCenter c) = injMinus2 (2 * c * a) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m2_p1 (a : ℝ) (Q : Charge) : bracket5LM (injMinus2 a) (injPlus1 Q) = injMinus1 (a • Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m2_p2 (a b : ℝ) : bracket5LM (injMinus2 a) (injPlus2 b) = injZeroCenter (-(b * a)) := by
  apply FreudenthalTKK5E8.ext <;> simp

@[simp] private theorem br_m1_m2 (Q : Charge) (a : ℝ) : bracket5LM (injMinus1 Q) (injMinus2 a) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m1_m1 (Q₁ Q₂ : Charge) :
    bracket5LM (injMinus1 Q₁) (injMinus1 Q₂) = injMinus2 (-symplecticForm Q₁ Q₂) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m1_zE7 (Q : Charge) (X : H3ZornTKKLie) :
    bracket5LM (injMinus1 Q) (injZeroE7 X) = injMinus1 (-repE7 X Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m1_zC (Q : Charge) (c : ℝ) :
    bracket5LM (injMinus1 Q) (injZeroCenter c) = injMinus1 (c • Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m1_p1 (Q₁ Q₂ : Charge) :
    bracket5LM (injMinus1 Q₁) (injPlus1 Q₂) =
      injZeroE7 (-K Q₂ Q₁) + injZeroCenter ((1 / 2 : ℝ) * symplecticForm Q₂ Q₁) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_m1_p2 (Q : Charge) (b : ℝ) :
    bracket5LM (injMinus1 Q) (injPlus2 b) = injPlus1 (-(b • Q)) := by
  apply FreudenthalTKK5E8.ext <;> simp

@[simp] private theorem br_zE7_m2 (X : H3ZornTKKLie) (a : ℝ) : bracket5LM (injZeroE7 X) (injMinus2 a) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zE7_m1 (X : H3ZornTKKLie) (Q : Charge) :
    bracket5LM (injZeroE7 X) (injMinus1 Q) = injMinus1 (repE7 X Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zE7_zE7 (X Y : H3ZornTKKLie) :
    bracket5LM (injZeroE7 X) (injZeroE7 Y) = injZeroE7 ⁅X, Y⁆ := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zE7_zC (X : H3ZornTKKLie) (c : ℝ) : bracket5LM (injZeroE7 X) (injZeroCenter c) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zE7_p1 (X : H3ZornTKKLie) (Q : Charge) :
    bracket5LM (injZeroE7 X) (injPlus1 Q) = injPlus1 (repE7 X Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zE7_p2 (X : H3ZornTKKLie) (b : ℝ) : bracket5LM (injZeroE7 X) (injPlus2 b) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp

@[simp] private theorem br_zC_m2 (c a : ℝ) : bracket5LM (injZeroCenter c) (injMinus2 a) = injMinus2 (-2 * c * a) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zC_m1 (c : ℝ) (Q : Charge) :
    bracket5LM (injZeroCenter c) (injMinus1 Q) = injMinus1 (-(c • Q)) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zC_zE7 (c : ℝ) (X : H3ZornTKKLie) : bracket5LM (injZeroCenter c) (injZeroE7 X) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zC_zC (c₁ c₂ : ℝ) : bracket5LM (injZeroCenter c₁) (injZeroCenter c₂) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zC_p1 (c : ℝ) (Q : Charge) :
    bracket5LM (injZeroCenter c) (injPlus1 Q) = injPlus1 (c • Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_zC_p2 (c b : ℝ) : bracket5LM (injZeroCenter c) (injPlus2 b) = injPlus2 (2 * c * b) := by
  apply FreudenthalTKK5E8.ext <;> simp

@[simp] private theorem br_p1_m2 (Q : Charge) (a : ℝ) :
    bracket5LM (injPlus1 Q) (injMinus2 a) = injMinus1 (-(a • Q)) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p1_m1 (Q₁ Q₂ : Charge) :
    bracket5LM (injPlus1 Q₁) (injMinus1 Q₂) =
      injZeroE7 (K Q₁ Q₂) + injZeroCenter (-(1 / 2 : ℝ) * symplecticForm Q₁ Q₂) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p1_zE7 (Q : Charge) (X : H3ZornTKKLie) :
    bracket5LM (injPlus1 Q) (injZeroE7 X) = injPlus1 (-repE7 X Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p1_zC (Q : Charge) (c : ℝ) :
    bracket5LM (injPlus1 Q) (injZeroCenter c) = injPlus1 (-(c • Q)) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p1_p1 (Q₁ Q₂ : Charge) :
    bracket5LM (injPlus1 Q₁) (injPlus1 Q₂) = injPlus2 (symplecticForm Q₁ Q₂) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p1_p2 (Q : Charge) (b : ℝ) : bracket5LM (injPlus1 Q) (injPlus2 b) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp

@[simp] private theorem br_p2_m2 (b a : ℝ) : bracket5LM (injPlus2 b) (injMinus2 a) = injZeroCenter (b * a) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p2_m1 (b : ℝ) (Q : Charge) :
    bracket5LM (injPlus2 b) (injMinus1 Q) = injPlus1 (b • Q) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p2_zE7 (b : ℝ) (X : H3ZornTKKLie) : bracket5LM (injPlus2 b) (injZeroE7 X) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p2_zC (b c : ℝ) : bracket5LM (injPlus2 b) (injZeroCenter c) = injPlus2 (-2 * c * b) := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p2_p1 (b : ℝ) (Q : Charge) : bracket5LM (injPlus2 b) (injPlus1 Q) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp
@[simp] private theorem br_p2_p2 (b₁ b₂ : ℝ) : bracket5LM (injPlus2 b₁) (injPlus2 b₂) = 0 := by
  apply FreudenthalTKK5E8.ext <;> simp

private theorem leibniz_sorted_0 (j k : Fin 6) (hjk : j ≤ k)
    (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 0 x) (proj6 j y) (proj6 k z) = 0 := by
  fin_cases j <;> fin_cases k <;>
    first | exact absurd hjk (by decide) | all_goals
      simp only [InfoGeometry.Exceptional.leibnizDefect, proj6, LinearMap.coe_mk, AddHom.coe_mk]
  all_goals
    try simp only [LinearMap.zero_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      map_add, map_zero, map_neg, map_smul,
      smul_zero, neg_zero, zero_add, sub_self, sub_zero, zero_sub, neg_neg,
      br_m2_m2, br_m2_m1, br_m2_zE7, br_m2_zC, br_m2_p1, br_m2_p2,
      br_m1_m2, br_zE7_m2, br_zC_m2,
      br_m1_m1, br_m1_zE7, br_m1_zC, br_m1_p1, br_m1_p2,
      br_zE7_m1, br_zE7_zE7, br_zE7_zC, br_zE7_p1, br_zE7_p2,
      br_zC_m1, br_zC_zC, br_zC_p1, br_zC_p2,
      br_p1_m1, br_p1_zC, br_p1_p1, br_p1_p2, br_p2_zC, br_p2_p2]
  · -- (0, 5)
    apply FreudenthalTKK5E8.ext <;> simp; ring
  · -- (1, 4)
    apply FreudenthalTKK5E8.ext <;> simp; rw [symplecticForm_skew y.gMinus1 z.gPlus1]; ring
  · -- (1, 5)
    apply FreudenthalTKK5E8.ext <;> simp; rw [smul_smul]; module
  · -- (3, 3)
    apply FreudenthalTKK5E8.ext <;> simp; ring
  · -- (3, 4)
    apply FreudenthalTKK5E8.ext <;> simp; module
  · -- (3, 5)
    apply FreudenthalTKK5E8.ext <;> simp; ring
  · -- (4, 4)
    rw [K_symm z.gPlus1 y.gPlus1, symplecticForm_skew z.gPlus1 y.gPlus1]
    apply FreudenthalTKK5E8.ext <;> simp [-K_neg, -K_zero, -K_pos]
    ring
  · -- (4, 5)
    apply FreudenthalTKK5E8.ext <;> simp; rw [smul_smul]; module
  · -- (5, 5)
    apply FreudenthalTKK5E8.ext <;> simp; ring

private theorem leibniz_sorted_1 (j k : Fin 6) (hij : (1 : Fin 6) ≤ j) (hjk : j ≤ k)
    (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 1 x) (proj6 j y) (proj6 k z) = 0 := by
  fin_cases j <;> fin_cases k <;>
    first | exact absurd hij (by decide) | exact absurd hjk (by decide) | all_goals
      simp only [InfoGeometry.Exceptional.leibnizDefect, proj6, LinearMap.coe_mk, AddHom.coe_mk]
  all_goals
    try simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_zero, map_neg, map_smul,
      smul_zero, neg_zero, add_zero, zero_add, sub_self, sub_zero, zero_sub, neg_neg,
      br_m2_m1, br_m2_zE7, br_m2_zC, br_m2_p1, br_m2_p2,
      br_m1_m2, br_m1_m1, br_m1_zE7, br_m1_zC, br_m1_p1, br_m1_p2,
      br_zE7_m1, br_zE7_zE7, br_zE7_zC, br_zE7_p1, br_zE7_p2,
      br_zC_m1, br_zC_zE7, br_zC_zC, br_zC_p1, br_zC_p2,
      br_p1_zE7, br_p1_zC, br_p1_p1, br_p1_p2, br_p2_p1, br_p2_p2]
  · -- (1, 2)
    have hs := repE7_symplecticForm_skew z.gZeroE7 x.gMinus1 y.gMinus1
    apply FreudenthalTKK5E8.ext <;> simp
    rw [symplecticForm_skew (repE7 z.gZeroE7 x.gMinus1) y.gMinus1]
    linarith
  · -- (1, 3)
    apply FreudenthalTKK5E8.ext <;> simp
    rw [symplecticForm_skew y.gMinus1 x.gMinus1]; ring
  · -- (1, 4)
    have htri := triple_identity_p1_m1_p1 x.gMinus1 z.gPlus1 y.gMinus1
    rw [K_symm z.gPlus1 y.gMinus1, K_symm z.gPlus1 x.gMinus1]
    apply FreudenthalTKK5E8.ext <;>
      simp [-K_neg, -K_zero, -K_pos, -repE7_alpha, -repE7_beta, -repE7_x, -repE7_y]
    rw [symplecticForm_skew y.gMinus1 z.gPlus1, symplecticForm_skew x.gMinus1 z.gPlus1]
    have hneg : repE7 (K y.gMinus1 z.gPlus1) x.gMinus1 - repE7 (K x.gMinus1 z.gPlus1) y.gMinus1 =
        -((1 / 2 : ℝ) • (symplecticForm x.gMinus1 z.gPlus1 • y.gMinus1 -
            symplecticForm y.gMinus1 z.gPlus1 • x.gMinus1) +
          symplecticForm x.gMinus1 y.gMinus1 • z.gPlus1) := by
      rw [← htri]; module
    have hsum : (repE7 (K y.gMinus1 z.gPlus1) x.gMinus1 - repE7 (K x.gMinus1 z.gPlus1) y.gMinus1) +
          ((1 / 2 * -symplecticForm y.gMinus1 z.gPlus1) • x.gMinus1 -
            (1 / 2 * -symplecticForm x.gMinus1 z.gPlus1) • y.gMinus1 +
            symplecticForm x.gMinus1 y.gMinus1 • z.gPlus1) = 0 := by
      rw [hneg]; module
    rw [← hsum]; module
  · -- (1, 5)
    rw [K_symm y.gMinus1 x.gMinus1, symplecticForm_skew y.gMinus1 x.gMinus1]
    apply FreudenthalTKK5E8.ext <;> simp [-K_neg, -K_zero, -K_pos]
    ring
  · -- (2, 2)
    apply FreudenthalTKK5E8.ext <;>
      simp [-repE7_alpha, -repE7_beta, -repE7_x, -repE7_y]
  · -- (2, 4)
    have heq := K_equivariant y.gZeroE7 z.gPlus1 x.gMinus1
    have hs := repE7_symplecticForm_skew y.gZeroE7 z.gPlus1 x.gMinus1
    apply FreudenthalTKK5E8.ext <;>
      simp [-K_neg, -K_zero, -K_pos, -repE7_alpha, -repE7_beta, -repE7_x, -repE7_y]
    · rw [heq]; module
    · linarith
  · -- (3, 3)
    apply FreudenthalTKK5E8.ext <;> simp; module
  · -- (3, 5)
    apply FreudenthalTKK5E8.ext <;> simp; rw [smul_smul]; module
  · -- (4, 4)
    have htri := triple_identity_p1_m1_p1 y.gPlus1 x.gMinus1 z.gPlus1
    apply FreudenthalTKK5E8.ext <;>
      simp [-K_neg, -K_zero, -K_pos, -repE7_alpha, -repE7_beta, -repE7_x, -repE7_y]
    have hrep : repE7 (K y.gPlus1 x.gMinus1) z.gPlus1 =
        repE7 (K z.gPlus1 x.gMinus1) y.gPlus1 +
          ((1 / 2 : ℝ) • (symplecticForm y.gPlus1 x.gMinus1 • z.gPlus1 -
              symplecticForm z.gPlus1 x.gMinus1 • y.gPlus1) +
            symplecticForm y.gPlus1 z.gPlus1 • x.gMinus1) := by
      rw [← htri]; module
    rw [hrep]
    module
  · -- (4, 5)
    apply FreudenthalTKK5E8.ext <;> simp; ring

private theorem leibniz_sorted_2 (j k : Fin 6) (hij : (2 : Fin 6) ≤ j) (hjk : j ≤ k)
    (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 2 x) (proj6 j y) (proj6 k z) = 0 := by
  fin_cases j <;> fin_cases k <;>
    first | exact absurd hij (by decide) | exact absurd hjk (by decide) | all_goals
      simp only [InfoGeometry.Exceptional.leibnizDefect, proj6, LinearMap.coe_mk, AddHom.coe_mk]
  all_goals
    try simp only [LinearMap.zero_apply, map_zero, map_smul, sub_self, sub_zero, zero_sub,
      br_zE7_zE7, br_zE7_zC, br_zE7_p1, br_zE7_p2,
      br_zC_zC, br_zC_p1, br_zC_p2, br_p1_p1, br_p1_p2, br_p2_p2]
  · -- (2, 2)
    apply FreudenthalTKK5E8.ext <;> simp
  · -- (2, 4)
    apply FreudenthalTKK5E8.ext <;>
      simp [-repE7_alpha, -repE7_beta, -repE7_x, -repE7_y]
  · -- (4, 4)
    have hs := repE7_symplecticForm_skew x.gZeroE7 y.gPlus1 z.gPlus1
    apply FreudenthalTKK5E8.ext <;> simp [-repE7_alpha, -repE7_beta, -repE7_x, -repE7_y]
    linarith

private theorem leibniz_sorted_3 (j k : Fin 6) (hij : (3 : Fin 6) ≤ j) (hjk : j ≤ k)
    (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 3 x) (proj6 j y) (proj6 k z) = 0 := by
  fin_cases j <;> fin_cases k <;>
    first | exact absurd hij (by decide) | exact absurd hjk (by decide) | all_goals
      simp only [InfoGeometry.Exceptional.leibnizDefect, proj6, LinearMap.coe_mk, AddHom.coe_mk]
  all_goals
    try simp only [LinearMap.zero_apply, LinearMap.smul_apply, map_zero, map_smul,
      smul_zero, sub_self, sub_zero, br_zC_zC, br_zC_p1, br_zC_p2, br_p1_p1, br_p1_p2, br_p2_p2]
  · -- (3, 4)
    apply FreudenthalTKK5E8.ext <;> simp
    rw [smul_smul, smul_smul, mul_comm y.gZeroCenter x.gZeroCenter]; module
  · -- (3, 5)
    apply FreudenthalTKK5E8.ext <;> simp; ring
  · -- (4, 4)
    apply FreudenthalTKK5E8.ext <;> simp; ring

private theorem leibniz_sorted_45 (i j k : Fin 6) (hi : i = 4 ∨ i = 5) (hij : i ≤ j) (hjk : j ≤ k)
    (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 i x) (proj6 j y) (proj6 k z) = 0 := by
  rcases hi with rfl | rfl <;> fin_cases j <;> fin_cases k <;>
    first | exact absurd hij (by decide) | exact absurd hjk (by decide) | all_goals
      simp only [InfoGeometry.Exceptional.leibnizDefect, proj6, LinearMap.coe_mk, AddHom.coe_mk]
  all_goals
    try simp only [LinearMap.zero_apply, map_zero, sub_self,
      br_p1_p1, br_p1_p2, br_p2_p1, br_p2_p2]

private theorem leibniz_sorted_fin6 (i j k : Fin 6) (hij : i ≤ j) (hjk : j ≤ k)
    (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM (proj6 i x) (proj6 j y) (proj6 k z) = 0 := by
  fin_cases i
  · exact leibniz_sorted_0 j k hjk x y z
  · exact leibniz_sorted_1 j k hij hjk x y z
  · exact leibniz_sorted_2 j k hij hjk x y z
  · exact leibniz_sorted_3 j k hij hjk x y z
  · exact leibniz_sorted_45 4 j k (Or.inl rfl) hij hjk x y z
  · exact leibniz_sorted_45 5 j k (Or.inr rfl) hij hjk x y z

private theorem bracket5LM_jacobi (x y z : FreudenthalTKK5E8) :
    InfoGeometry.Exceptional.leibnizDefect bracket5LM x y z = 0 := by
  refine InfoGeometry.Exceptional.global_leibniz_of_homogeneous bracket5LM proj6 sum_proj6 ?_ x y z
  intro i j k u v w
  rcases le_total i j with hij | hji
  · rcases le_total j k with hjk | hkj
    · exact leibniz_sorted_fin6 i j k hij hjk u v w
    · rcases le_total i k with hik | hki
      · rw [leibnizDefect_swap₂₃, leibniz_sorted_fin6 i k j hik hkj u w v, neg_zero]
      · rw [leibnizDefect_cycle, leibnizDefect_cycle,
          leibniz_sorted_fin6 k i j hki hij w u v]
  · rcases le_total i k with hik | hki
    · rw [leibnizDefect_swap₁₂, leibniz_sorted_fin6 j i k hji hik v u w, neg_zero]
    · rcases le_total j k with hjk | hkj
      · rw [leibnizDefect_cycle, leibniz_sorted_fin6 j k i hjk hki v w u]
      · rw [leibnizDefect_swap₁₂, leibnizDefect_cycle, leibnizDefect_cycle,
          leibniz_sorted_fin6 k j i hkj hji w v u, neg_zero]

instance instLieRingFreudenthalTKK5E8 : LieRing FreudenthalTKK5E8 where
  bracket U V := bracket5LM U V
  add_lie U₁ U₂ V := (bracket5LM.map_add U₁ U₂).symm ▸ rfl
  lie_add U V₁ V₂ := (bracket5LM U).map_add V₁ V₂
  lie_self U := bracket5LM_self U
  leibniz_lie x y z := by
    have hj := bracket5LM_jacobi x y z
    dsimp [InfoGeometry.Exceptional.leibnizDefect] at hj
    have h1 := eq_add_of_sub_eq hj
    rw [zero_add] at h1
    change bracket5LM x (bracket5LM y z) =
      bracket5LM (bracket5LM x y) z + bracket5LM y (bracket5LM x z)
    exact (eq_add_of_sub_eq h1).trans (add_comm _ _)

instance instLieAlgebraFreudenthalTKK5E8 : LieAlgebra ℝ FreudenthalTKK5E8 where
  lie_smul r U V := (bracket5LM U).map_smul r V

/-- `H3ZornTKKLie` embeds as the semisimple Levi factor of grade `0` inside `FreudenthalTKK5E8`. -/
def zeroE7Hom : H3ZornTKKLie →ₗ⁅ℝ⁆ FreudenthalTKK5E8 where
  toLinearMap := injZeroE7
  map_lie' {X Y} := by
    change injZeroE7 ⁅X, Y⁆ = bracket5LM (injZeroE7 X) (injZeroE7 Y)
    rw [br_zE7_zE7]

theorem zeroE7Hom_injective : Function.Injective zeroE7Hom := by
  intro X Y h
  exact congrArg FreudenthalTKK5E8.gZeroE7 h

/-- The 5-grading `gGrade : ℤ → Submodule ℝ FreudenthalTKK5E8` (`⊥` for `|k| > 2`). -/
def gGrade : ℤ → Submodule ℝ FreudenthalTKK5E8
  | -2 => LinearMap.range injMinus2
  | -1 => LinearMap.range injMinus1
  | 0 => LinearMap.range injZeroE7 ⊔ LinearMap.range injZeroCenter
  | 1 => LinearMap.range injPlus1
  | 2 => LinearMap.range injPlus2
  | _ => ⊥

theorem mem_gGrade_neg_two_iff (U : FreudenthalTKK5E8) :
    U ∈ gGrade (-2) ↔
      U.gMinus1 = 0 ∧ U.gZeroE7 = 0 ∧ U.gZeroCenter = 0 ∧ U.gPlus1 = 0 ∧ U.gPlus2 = 0 := by
  constructor
  · rintro ⟨a, rfl⟩; simp
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨U.gMinus2, ?_⟩
    apply FreudenthalTKK5E8.ext <;> simp [h1, h2, h3, h4, h5]

theorem mem_gGrade_neg_one_iff (U : FreudenthalTKK5E8) :
    U ∈ gGrade (-1) ↔
      U.gMinus2 = 0 ∧ U.gZeroE7 = 0 ∧ U.gZeroCenter = 0 ∧ U.gPlus1 = 0 ∧ U.gPlus2 = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩; simp
  · rintro ⟨h0, h2, h3, h4, h5⟩
    refine ⟨U.gMinus1, ?_⟩
    apply FreudenthalTKK5E8.ext <;> simp [h0, h2, h3, h4, h5]

theorem mem_gGrade_zero_iff (U : FreudenthalTKK5E8) :
    U ∈ gGrade 0 ↔
      U.gMinus2 = 0 ∧ U.gMinus1 = 0 ∧ U.gPlus1 = 0 ∧ U.gPlus2 = 0 := by
  constructor
  · intro hU
    rw [gGrade, Submodule.mem_sup] at hU
    rcases hU with ⟨u1, ⟨X, rfl⟩, u2, ⟨c, rfl⟩, rfl⟩
    simp
  · rintro ⟨h0, h1, h4, h5⟩
    rw [gGrade, Submodule.mem_sup]
    refine ⟨injZeroE7 U.gZeroE7, ⟨U.gZeroE7, rfl⟩, injZeroCenter U.gZeroCenter, ⟨U.gZeroCenter, rfl⟩, ?_⟩
    apply FreudenthalTKK5E8.ext <;> simp [h0, h1, h4, h5]

theorem mem_gGrade_pos_one_iff (U : FreudenthalTKK5E8) :
    U ∈ gGrade 1 ↔
      U.gMinus2 = 0 ∧ U.gMinus1 = 0 ∧ U.gZeroE7 = 0 ∧ U.gZeroCenter = 0 ∧ U.gPlus2 = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩; simp
  · rintro ⟨h0, h1, h2, h3, h5⟩
    refine ⟨U.gPlus1, ?_⟩
    apply FreudenthalTKK5E8.ext <;> simp [h0, h1, h2, h3, h5]

theorem mem_gGrade_pos_two_iff (U : FreudenthalTKK5E8) :
    U ∈ gGrade 2 ↔
      U.gMinus2 = 0 ∧ U.gMinus1 = 0 ∧ U.gZeroE7 = 0 ∧ U.gZeroCenter = 0 ∧ U.gPlus1 = 0 := by
  constructor
  · rintro ⟨b, rfl⟩; simp
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨U.gPlus2, ?_⟩
    apply FreudenthalTKK5E8.ext <;> simp [h0, h1, h2, h3, h4]

theorem gGrade_eq_bot_of_abs_gt_two (k : ℤ) (hk : 2 < |k|) : gGrade k = ⊥ := by
  match k with
  | -2 => norm_num at hk
  | -1 => norm_num at hk
  | 0 => norm_num at hk
  | 1 => norm_num at hk
  | 2 => norm_num at hk
  | Int.ofNat (_ + 3) => rfl
  | Int.negSucc (_ + 2) => rfl

theorem finrank_gGrade_neg_two : Module.finrank ℝ (gGrade (-2)) = 1 := by
  have hinj : Function.Injective injMinus2 := fun a b h => congrArg FreudenthalTKK5E8.gMinus2 h
  rw [gGrade, LinearMap.finrank_range_of_inj hinj, Module.finrank_self]

theorem finrank_gGrade_neg_one : Module.finrank ℝ (gGrade (-1)) = 56 := by
  have hinj : Function.Injective injMinus1 := fun a b h => congrArg FreudenthalTKK5E8.gMinus1 h
  rw [gGrade, LinearMap.finrank_range_of_inj hinj, finrank_charge]

theorem finrank_gGrade_zero : Module.finrank ℝ (gGrade 0) = 134 := by
  have hinjE : Function.Injective injZeroE7 := fun a b h => congrArg FreudenthalTKK5E8.gZeroE7 h
  have hinjC : Function.Injective injZeroCenter := fun a b h => congrArg FreudenthalTKK5E8.gZeroCenter h
  have hdisj : Disjoint (LinearMap.range injZeroE7) (LinearMap.range injZeroCenter) := by
    rw [Submodule.disjoint_def]
    rintro U ⟨X, rfl⟩ ⟨c, hc⟩
    have hc0 : c = 0 := congrArg FreudenthalTKK5E8.gZeroCenter hc
    have hX0 : X = 0 := congrArg FreudenthalTKK5E8.gZeroE7 hc.symm
    subst hc0; subst hX0; apply FreudenthalTKK5E8.ext <;> simp
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range injZeroE7) (LinearMap.range injZeroCenter)
  rw [hdisj.eq_bot, finrank_bot, add_zero,
    LinearMap.finrank_range_of_inj hinjE, LinearMap.finrank_range_of_inj hinjC,
    finrank_H3ZornTKKLie, Module.finrank_self] at hsum
  exact hsum

theorem finrank_gGrade_pos_one : Module.finrank ℝ (gGrade 1) = 56 := by
  have hinj : Function.Injective injPlus1 := fun a b h => congrArg FreudenthalTKK5E8.gPlus1 h
  rw [gGrade, LinearMap.finrank_range_of_inj hinj, finrank_charge]

theorem finrank_gGrade_pos_two : Module.finrank ℝ (gGrade 2) = 1 := by
  have hinj : Function.Injective injPlus2 := fun a b h => congrArg FreudenthalTKK5E8.gPlus2 h
  rw [gGrade, LinearMap.finrank_range_of_inj hinj, Module.finrank_self]

/-- **5-grading compatibility** of the 248-dimensional Lie bracket: `[𝔤ᵢ, 𝔤ⱼ] ⊆ 𝔤ᵢ₊ⱼ`. -/
theorem gGrade_bracket_mem {i j : ℤ} {U V : FreudenthalTKK5E8}
    (hU : U ∈ gGrade i) (hV : V ∈ gGrade j) :
    ⁅U, V⁆ ∈ gGrade (i + j) := by
  change bracket5LM U V ∈ gGrade (i + j)
  by_cases hi : 2 < |i|
  · rw [gGrade_eq_bot_of_abs_gt_two i hi, Submodule.mem_bot] at hU
    subst hU; simp
  · by_cases hj : 2 < |j|
    · rw [gGrade_eq_bot_of_abs_gt_two j hj, Submodule.mem_bot] at hV
      subst hV; simp
    · have hi0 : -2 ≤ i ∧ i ≤ 2 := abs_le.mp (not_lt.mp hi)
      have hj0 : -2 ≤ j ∧ j ≤ 2 := abs_le.mp (not_lt.mp hj)
      have hi' : i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 := by omega
      have hj' : j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
        rcases hj' with rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [mem_gGrade_neg_two_iff, mem_gGrade_neg_one_iff, mem_gGrade_zero_iff,
          mem_gGrade_pos_one_iff, mem_gGrade_pos_two_iff] at hU hV
        simp only [Int.reduceAdd, Int.reduceNeg]
      all_goals
        first
        | (rw [mem_gGrade_neg_two_iff]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp [hU, hV]; try first | ring | module | abel))
        | (rw [mem_gGrade_neg_one_iff]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp [hU, hV]; try first | ring | module | abel))
        | (rw [mem_gGrade_zero_iff]; refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp [hU, hV]; try first | ring | module | abel))
        | (rw [mem_gGrade_pos_one_iff]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp [hU, hV]; try first | ring | module | abel))
        | (rw [mem_gGrade_pos_two_iff]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp [hU, hV]; try first | ring | module | abel))
        | (rw [gGrade_eq_bot_of_abs_gt_two _ (by norm_num)]
           have h0 : bracket5LM U V = 0 := by
             apply FreudenthalTKK5E8.ext <;> (simp [hU, hV]; try first | ring | module | abel)
           rw [h0]; exact Submodule.zero_mem ⊥)

end Bracket5AndGrading

/-! ## Section 5: Unconditional Simplicity of `FreudenthalTKK5E8` -/

section Simplicity5E8

private theorem symplecticForm_eq_zero_of_forall (Q : Charge)
    (h : ∀ P : Charge, symplecticForm Q P = 0) : Q = 0 := by
  apply FreudenthalCharge.ext
  · let P : Charge := { alpha := 0, beta := 1, x := 0, y := 0 }
    have h1 := h P
    rw [symplecticForm_expanded] at h1
    have hPa : P.alpha = 0 := rfl
    have hPb : P.beta = 1 := rfl
    have hPx : P.x = 0 := rfl
    have hPy : P.y = 0 := rfl
    rw [hPa, hPb, hPx, hPy, h3_traceBilin_zero_right, h3_traceBilin_zero_right] at h1
    rw [charge_zero_alpha]; linarith
  · let P : Charge := { alpha := 1, beta := 0, x := 0, y := 0 }
    have h1 := h P
    rw [symplecticForm_expanded] at h1
    have hPa : P.alpha = 1 := rfl
    have hPb : P.beta = 0 := rfl
    have hPx : P.x = 0 := rfl
    have hPy : P.y = 0 := rfl
    rw [hPa, hPb, hPx, hPy, h3_traceBilin_zero_right, h3_traceBilin_zero_right] at h1
    rw [charge_zero_beta]; linarith
  · apply H3Zorn.eq_zero_of_traceBilin_left Q.x
    intro Y
    let P : Charge := { alpha := 0, beta := 0, x := 0, y := Y }
    have h1 := h P
    rw [symplecticForm_expanded] at h1
    have hPa : P.alpha = 0 := rfl
    have hPb : P.beta = 0 := rfl
    have hPx : P.x = 0 := rfl
    have hPy : P.y = Y := rfl
    rw [hPa, hPb, hPx, hPy, h3_traceBilin_zero_right] at h1
    linarith
  · apply H3Zorn.eq_zero_of_traceBilin_right Q.y
    intro X
    let P : Charge := { alpha := 0, beta := 0, x := X, y := 0 }
    have h1 := h P
    rw [symplecticForm_expanded] at h1
    have hPa : P.alpha = 0 := rfl
    have hPb : P.beta = 0 := rfl
    have hPx : P.x = X := rfl
    have hPy : P.y = 0 := rfl
    rw [hPa, hPb, hPx, hPy, h3_traceBilin_zero_right, H3Zorn.traceBilin_symm] at h1
    linarith

theorem symplecticForm_nondegenerate (Q : Charge) (hQ : Q ≠ 0) :
    ∃ P : Charge, symplecticForm Q P ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hQ (symplecticForm_eq_zero_of_forall Q hall)

private def adZ (U : FreudenthalTKK5E8) : FreudenthalTKK5E8 :=
  ⁅gradeCenterZ, U⁆

@[simp] private theorem adZ_gMinus2 (U : FreudenthalTKK5E8) : (adZ U).gMinus2 = -2 * U.gMinus2 := by
  change (bracket5LM (injZeroCenter 1) U).gMinus2 = -2 * U.gMinus2
  simp [injZeroCenter]

@[simp] private theorem adZ_gMinus1 (U : FreudenthalTKK5E8) : (adZ U).gMinus1 = -U.gMinus1 := by
  change (bracket5LM (injZeroCenter 1) U).gMinus1 = -U.gMinus1
  simp [injZeroCenter]

@[simp] private theorem adZ_gZeroE7 (U : FreudenthalTKK5E8) : (adZ U).gZeroE7 = 0 := by
  change (bracket5LM (injZeroCenter 1) U).gZeroE7 = 0
  simp [injZeroCenter]

@[simp] private theorem adZ_gZeroCenter (U : FreudenthalTKK5E8) : (adZ U).gZeroCenter = 0 := by
  change (bracket5LM (injZeroCenter 1) U).gZeroCenter = 0
  simp [injZeroCenter]

@[simp] private theorem adZ_gPlus1 (U : FreudenthalTKK5E8) : (adZ U).gPlus1 = U.gPlus1 := by
  change (bracket5LM (injZeroCenter 1) U).gPlus1 = U.gPlus1
  simp [injZeroCenter]

@[simp] private theorem adZ_gPlus2 (U : FreudenthalTKK5E8) : (adZ U).gPlus2 = 2 * U.gPlus2 := by
  change (bracket5LM (injZeroCenter 1) U).gPlus2 = 2 * U.gPlus2
  simp [injZeroCenter]

private theorem adZ_mem_ideal (I : LieIdeal ℝ FreudenthalTKK5E8) {U : FreudenthalTKK5E8}
    (hU : U ∈ I) : adZ U ∈ I :=
  I.lie_mem hU

private theorem proj_minus2_eq_adZ (U : FreudenthalTKK5E8) :
    (1 / 24 : ℝ) •
        (adZ (adZ (adZ (adZ U))) - (2 : ℝ) • adZ (adZ (adZ U)) -
          adZ (adZ U) + (2 : ℝ) • adZ U) =
      injMinus2 U.gMinus2 := by
  apply FreudenthalTKK5E8.ext <;> simp [injMinus2]; ring

private theorem proj_minus1_eq_adZ (U : FreudenthalTKK5E8) :
    (-1 / 6 : ℝ) •
        (adZ (adZ (adZ (adZ U))) - adZ (adZ (adZ U)) -
          (4 : ℝ) • adZ (adZ U) + (4 : ℝ) • adZ U) =
      injMinus1 U.gMinus1 := by
  apply FreudenthalTKK5E8.ext <;> (simp [injMinus1]; try (ring; done))
  rw [smul_sub, smul_add, smul_smul, ← neg_smul, ← add_smul, ← sub_smul, ← add_smul]
  rw [show (-1 / 6 : ℝ) + -1 / 6 - -1 / 6 * 4 + -(-1 / 6 * 4) = 1 by norm_num, one_smul]

private theorem proj_plus1_eq_adZ (U : FreudenthalTKK5E8) :
    (1 / 6 : ℝ) •
        (-(adZ (adZ (adZ (adZ U)))) - adZ (adZ (adZ U)) +
          (4 : ℝ) • adZ (adZ U) + (4 : ℝ) • adZ U) =
      injPlus1 U.gPlus1 := by
  apply FreudenthalTKK5E8.ext <;> (simp [injPlus1]; try (ring; done))
  rw [smul_sub, smul_neg, ← neg_smul, smul_smul, ← sub_smul, ← add_smul, ← add_smul]
  rw [show -(6 : ℝ)⁻¹ - (6 : ℝ)⁻¹ + (6 : ℝ)⁻¹ * 4 + (6 : ℝ)⁻¹ * 4 = 1 by norm_num, one_smul]

private theorem proj_plus2_eq_adZ (U : FreudenthalTKK5E8) :
    (1 / 24 : ℝ) •
        (adZ (adZ (adZ (adZ U))) + (2 : ℝ) • adZ (adZ (adZ U)) -
          adZ (adZ U) - (2 : ℝ) • adZ U) =
      injPlus2 U.gPlus2 := by
  apply FreudenthalTKK5E8.ext <;> simp [injPlus2]; ring

private theorem ideal_grade_components_mem (I : LieIdeal ℝ FreudenthalTKK5E8)
    {U : FreudenthalTKK5E8} (hU : U ∈ I) :
    injMinus2 U.gMinus2 ∈ I ∧ injMinus1 U.gMinus1 ∈ I ∧
      injZeroE7 U.gZeroE7 + injZeroCenter U.gZeroCenter ∈ I ∧
      injPlus1 U.gPlus1 ∈ I ∧ injPlus2 U.gPlus2 ∈ I := by
  have h1 : adZ U ∈ I := adZ_mem_ideal I hU
  have h2 : adZ (adZ U) ∈ I := adZ_mem_ideal I h1
  have h3 : adZ (adZ (adZ U)) ∈ I := adZ_mem_ideal I h2
  have h4 : adZ (adZ (adZ (adZ U))) ∈ I := adZ_mem_ideal I h3
  have hm2 : injMinus2 U.gMinus2 ∈ I := by
    rw [← proj_minus2_eq_adZ U]
    exact I.smul_mem _ (I.add_mem (I.sub_mem (I.sub_mem h4 (I.smul_mem 2 h3)) h2) (I.smul_mem 2 h1))
  have hm1 : injMinus1 U.gMinus1 ∈ I := by
    rw [← proj_minus1_eq_adZ U]
    exact I.smul_mem _ (I.add_mem (I.sub_mem (I.sub_mem h4 h3) (I.smul_mem 4 h2)) (I.smul_mem 4 h1))
  have hp1 : injPlus1 U.gPlus1 ∈ I := by
    rw [← proj_plus1_eq_adZ U]
    exact I.smul_mem _ (I.add_mem (I.add_mem (I.sub_mem (I.neg_mem h4) h3) (I.smul_mem 4 h2))
      (I.smul_mem 4 h1))
  have hp2 : injPlus2 U.gPlus2 ∈ I := by
    rw [← proj_plus2_eq_adZ U]
    exact I.smul_mem _ (I.sub_mem (I.sub_mem (I.add_mem h4 (I.smul_mem 2 h3)) h2) (I.smul_mem 2 h1))
  have hz : injZeroE7 U.gZeroE7 + injZeroCenter U.gZeroCenter ∈ I := by
    have hdec : injZeroE7 U.gZeroE7 + injZeroCenter U.gZeroCenter =
        U - injMinus2 U.gMinus2 - injMinus1 U.gMinus1 - injPlus1 U.gPlus1 - injPlus2 U.gPlus2 := by
      apply FreudenthalTKK5E8.ext <;> simp [injMinus2, injMinus1, injZeroE7, injZeroCenter,
        injPlus1, injPlus2]
    rw [hdec]
    exact I.sub_mem (I.sub_mem (I.sub_mem (I.sub_mem hU hm2) hm1) hp1) hp2
  exact ⟨hm2, hm1, hz, hp1, hp2⟩

private def idealZeroE7Preimage (I : LieIdeal ℝ FreudenthalTKK5E8) : LieIdeal ℝ H3ZornTKKLie where
  carrier := {X : H3ZornTKKLie | injZeroE7 X ∈ I}
  add_mem' {X Y} hX hY := by
    change injZeroE7 (X + Y) ∈ I
    rw [map_add]
    exact I.add_mem hX hY
  zero_mem' := by
    change injZeroE7 0 ∈ I
    rw [map_zero]
    exact I.zero_mem
  smul_mem' r {X} hX := by
    change injZeroE7 (r • X) ∈ I
    rw [map_smul]
    exact I.smul_mem r hX
  lie_mem {X Y} hY := by
    have hbr : injZeroE7 ⁅X, Y⁆ = ⁅injZeroE7 X, injZeroE7 Y⁆ :=
      (br_zE7_zE7 X Y).symm
    change injZeroE7 ⁅X, Y⁆ ∈ I
    rw [hbr]
    exact I.lie_mem hY

private theorem K_witness_ne_zero :
    K { alpha := 1, beta := 0, x := 0, y := 0 }
      { alpha := 0, beta := 1, x := 0, y := 0 } ≠ 0 := by
  intro h
  have hz := congrArg (fun T : H3ZornTKKLie => (T.zero.1 (1 : H3Zorn ℝ)).α₁) h
  simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply,
    LinearMap.smul_apply, JordanTKK.tripleD_zero_right, H3Zorn.traceBilin_zero_left,
    h3zornStrOne_apply, LinearMap.zero_apply] at hz
  change (-2 : ℝ) * (0 + 0) + (-(1 * 1 + 0 * 0) + 0 + 0) * 1 = 0 at hz
  norm_num at hz

private theorem ideal_top_of_gradeCenterZ (I : LieIdeal ℝ FreudenthalTKK5E8)
    (hZ : gradeCenterZ ∈ I) : I = ⊤ := by
  have hep2 : ePlus2 ∈ I := by
    have h1 : ⁅ePlus2, gradeCenterZ⁆ ∈ I := I.lie_mem hZ
    have h2 : ⁅ePlus2, gradeCenterZ⁆ = (-2 : ℝ) • ePlus2 := by
      change bracket5LM (injPlus2 1) (injZeroCenter 1) = _
      rw [br_p2_zC]
      apply FreudenthalTKK5E8.ext <;> simp [ePlus2, injPlus2]
    rw [h2] at h1
    have h3 := I.smul_mem (-1 / 2 : ℝ) h1
    rw [smul_smul, show (-1 / 2 : ℝ) * -2 = 1 by norm_num, one_smul] at h3
    exact h3
  have hem2 : eMinus2 ∈ I := by
    have h1 : ⁅eMinus2, gradeCenterZ⁆ ∈ I := I.lie_mem hZ
    have h2 : ⁅eMinus2, gradeCenterZ⁆ = (2 : ℝ) • eMinus2 := by
      change bracket5LM (injMinus2 1) (injZeroCenter 1) = _
      rw [br_m2_zC]
      apply FreudenthalTKK5E8.ext <;> simp [eMinus2, injMinus2]
    rw [h2] at h1
    have h3 := I.smul_mem (1 / 2 : ℝ) h1
    rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h3
    exact h3
  have hm1 : ∀ Q : Charge, injMinus1 Q ∈ I := by
    intro Q
    have h1 : ⁅injPlus1 Q, eMinus2⁆ ∈ I := I.lie_mem hem2
    have h2 : ⁅injPlus1 Q, eMinus2⁆ = injMinus1 (-Q) := by
      change bracket5LM (injPlus1 Q) (injMinus2 1) = injMinus1 (-Q)
      rw [br_p1_m2, one_smul]
    rw [h2] at h1
    simpa [map_neg] using I.neg_mem h1
  have hp1 : ∀ Q : Charge, injPlus1 Q ∈ I := by
    intro Q
    have h1 : ⁅injMinus1 (-Q), ePlus2⁆ ∈ I := I.lie_mem hep2
    have h2 : ⁅injMinus1 (-Q), ePlus2⁆ = injPlus1 Q := by
      change bracket5LM (injMinus1 (-Q)) (injPlus2 1) = injPlus1 Q
      rw [br_m1_p2, one_smul, neg_neg]
    rw [h2] at h1
    exact h1
  have hE7 : ∀ X : H3ZornTKKLie, injZeroE7 X ∈ I := by
    let J := idealZeroE7Preimage I
    have hJne : J ≠ ⊥ := by
      intro hbot
      let Q₁ : Charge := { alpha := 1, beta := 0, x := 0, y := 0 }
      let Q₂ : Charge := { alpha := 0, beta := 1, x := 0, y := 0 }
      have hbr : ⁅injPlus1 Q₁, injMinus1 Q₂⁆ ∈ I := I.lie_mem (hm1 Q₂)
      have hbr' : ⁅injPlus1 Q₁, injMinus1 Q₂⁆ =
          injZeroE7 (K Q₁ Q₂) + (-(1 / 2 : ℝ) * symplecticForm Q₁ Q₂) • gradeCenterZ := by
        change bracket5LM (injPlus1 Q₁) (injMinus1 Q₂) = _
        rw [br_p1_m1]
        congr 1
        apply FreudenthalTKK5E8.ext <;> simp [gradeCenterZ, injZeroCenter]
      rw [hbr'] at hbr
      have hKmem : injZeroE7 (K Q₁ Q₂) ∈ I := by
        have hsub := I.sub_mem hbr (I.smul_mem (-(1 / 2 : ℝ) * symplecticForm Q₁ Q₂) hZ)
        simpa using hsub
      have hmemJ : K Q₁ Q₂ ∈ J := hKmem
      rw [hbot, LieSubmodule.mem_bot] at hmemJ
      exact K_witness_ne_zero hmemJ
    have hJtop : J = ⊤ :=
      (h3zornTKKLie_isSimple.eq_bot_or_eq_top J).resolve_left hJne
    intro X
    have hmem : X ∈ J := hJtop ▸ Submodule.mem_top
    exact hmem
  rw [eq_top_iff]
  intro U _
  have hdec : U = U.gMinus2 • eMinus2 + injMinus1 U.gMinus1 + injZeroE7 U.gZeroE7 +
      U.gZeroCenter • gradeCenterZ + injPlus1 U.gPlus1 + U.gPlus2 • ePlus2 := by
    apply FreudenthalTKK5E8.ext <;>
      simp [eMinus2, ePlus2, gradeCenterZ, injMinus2, injMinus1, injZeroE7, injZeroCenter,
        injPlus1, injPlus2]
  rw [hdec]
  exact I.add_mem (I.add_mem (I.add_mem (I.add_mem (I.add_mem
    (I.smul_mem _ hem2) (hm1 U.gMinus1)) (hE7 U.gZeroE7)) (I.smul_mem _ hZ))
    (hp1 U.gPlus1)) (I.smul_mem _ hep2)

private theorem ideal_top_of_ePlus2 (I : LieIdeal ℝ FreudenthalTKK5E8)
    {b : ℝ} (hb : b ≠ 0) (hm : injPlus2 b ∈ I) : I = ⊤ := by
  have hbr' : ⁅eMinus2, injPlus2 b⁆ ∈ I := I.lie_mem hm
  have hZ : ⁅eMinus2, injPlus2 b⁆ = (-b) • gradeCenterZ := by
    change bracket5LM (injMinus2 1) (injPlus2 b) = _
    rw [br_m2_p2, mul_one]
    apply FreudenthalTKK5E8.ext <;> simp [gradeCenterZ, injZeroCenter]
  rw [hZ] at hbr'
  have hZmem : gradeCenterZ ∈ I := by
    have hs := I.smul_mem (-b)⁻¹ hbr'
    rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hb), one_smul] at hs
    exact hs
  exact ideal_top_of_gradeCenterZ I hZmem

private theorem ideal_top_of_eMinus2 (I : LieIdeal ℝ FreudenthalTKK5E8)
    {a : ℝ} (ha : a ≠ 0) (hm : injMinus2 a ∈ I) : I = ⊤ := by
  have hbr' : ⁅ePlus2, injMinus2 a⁆ ∈ I := I.lie_mem hm
  have hZ : ⁅ePlus2, injMinus2 a⁆ = a • gradeCenterZ := by
    change bracket5LM (injPlus2 1) (injMinus2 a) = _
    rw [br_p2_m2, one_mul]
    apply FreudenthalTKK5E8.ext <;> simp [gradeCenterZ, injZeroCenter]
  rw [hZ] at hbr'
  have hZmem : gradeCenterZ ∈ I := by
    have hs := I.smul_mem a⁻¹ hbr'
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at hs
    exact hs
  exact ideal_top_of_gradeCenterZ I hZmem

private theorem ideal_top_of_injPlus1 (I : LieIdeal ℝ FreudenthalTKK5E8)
    {Q : Charge} (hQ : Q ≠ 0) (hm : injPlus1 Q ∈ I) : I = ⊤ := by
  obtain ⟨P, hP⟩ := symplecticForm_nondegenerate Q hQ
  have hbr : ⁅injPlus1 P, injPlus1 Q⁆ ∈ I := I.lie_mem hm
  have hbr' : ⁅injPlus1 P, injPlus1 Q⁆ = injPlus2 (-symplecticForm Q P) := by
    change bracket5LM (injPlus1 P) (injPlus1 Q) = _
    rw [br_p1_p1, symplecticForm_skew Q P]
  rw [hbr'] at hbr
  exact ideal_top_of_ePlus2 I (neg_ne_zero.mpr hP) hbr

private theorem ideal_top_of_injMinus1 (I : LieIdeal ℝ FreudenthalTKK5E8)
    {Q : Charge} (hQ : Q ≠ 0) (hm : injMinus1 Q ∈ I) : I = ⊤ := by
  obtain ⟨P, hP⟩ := symplecticForm_nondegenerate Q hQ
  have hbr : ⁅injMinus1 P, injMinus1 Q⁆ ∈ I := I.lie_mem hm
  have hbr' : ⁅injMinus1 P, injMinus1 Q⁆ = injMinus2 (symplecticForm Q P) := by
    change bracket5LM (injMinus1 P) (injMinus1 Q) = _
    rw [br_m1_m1, symplecticForm_skew Q P, neg_neg]
  rw [hbr'] at hbr
  exact ideal_top_of_eMinus2 I hP hbr

private theorem ideal_top_of_injZeroE7 (I : LieIdeal ℝ FreudenthalTKK5E8)
    {X : H3ZornTKKLie} (hX : X ≠ 0) (hm : injZeroE7 X ∈ I) : I = ⊤ := by
  let J := idealZeroE7Preimage I
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hmem : X ∈ J := hm
    rw [hbot, LieSubmodule.mem_bot] at hmem
    exact hX hmem
  have hJtop : J = ⊤ := (h3zornTKKLie_isSimple.eq_bot_or_eq_top J).resolve_left hJne
  have h1mem : injZeroE7 (zeroInj h3zornStrOne) ∈ I := by
    change zeroInj h3zornStrOne ∈ J
    rw [hJtop]
    exact LieSubmodule.mem_top _
  let Q₀ : Charge := { alpha := 1, beta := 0, x := 0, y := 0 }
  have hbr : ⁅injPlus1 Q₀, injZeroE7 (zeroInj h3zornStrOne)⁆ ∈ I := I.lie_mem h1mem
  have hbr' : ⁅injPlus1 Q₀, injZeroE7 (zeroInj h3zornStrOne)⁆ =
      injPlus1 (-repE7 (zeroInj h3zornStrOne) Q₀) := by
    change bracket5LM (injPlus1 Q₀) (injZeroE7 (zeroInj h3zornStrOne)) = _
    rw [br_p1_zE7]
  rw [hbr'] at hbr
  have hne : -repE7 (zeroInj h3zornStrOne) Q₀ ≠ 0 := by
    intro h0
    have ha := congrArg FreudenthalCharge.alpha h0
    simp only [charge_neg_alpha, repE7_alpha, h3tkk_zeroInj_neg, h3tkk_zeroInj_zero,
      h3_traceBilin_zero_left, mul_zero, zero_add, charge_zero_alpha] at ha
    have hstr1 : strTrace h3zornStrOne = 3 := by
      change H3Zorn.linearTrace (h3zornStrOne.1 (1 : H3Zorn ℝ)) = 3
      rw [h3zornStrOne_apply]
      change (1 : ℝ) + 1 + 1 = 3; norm_num
    rw [hstr1] at ha
    simp only [Q₀] at ha
    norm_num at ha
  exact ideal_top_of_injPlus1 I hne hbr

/-- **Unconditional Simplicity of `𝔈₈(8)`**: `FreudenthalTKK5E8` is a simple
248-dimensional real Lie algebra. -/
instance freudenthalTKK5E8_isSimple : LieAlgebra.IsSimple ℝ FreudenthalTKK5E8 where
  eq_bot_or_eq_top I := by
    by_cases hbot : I = ⊥
    · exact Or.inl hbot
    · right
      have hne : ∃ U ∈ I, U ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        rw [eq_bot_iff]
        intro U hU
        exact hall U hU
      obtain ⟨U, hUI, hUne⟩ := hne
      obtain ⟨hm2, hm1, hz, hp1, hp2⟩ := ideal_grade_components_mem I hUI
      by_cases hg2 : U.gPlus2 ≠ 0
      · exact ideal_top_of_ePlus2 I hg2 hp2
      · by_cases hg1 : U.gPlus1 ≠ 0
        · exact ideal_top_of_injPlus1 I hg1 hp1
        · by_cases hgm2 : U.gMinus2 ≠ 0
          · exact ideal_top_of_eMinus2 I hgm2 hm2
          · by_cases hgm1 : U.gMinus1 ≠ 0
            · exact ideal_top_of_injMinus1 I hgm1 hm1
            · by_cases hE7 : U.gZeroE7 ≠ 0
              · have hcenter := center_h3zornTKKLie_eq_bot
                have hnotmem : U.gZeroE7 ∉ LieAlgebra.center ℝ H3ZornTKKLie := by
                  rw [hcenter, LieSubmodule.mem_bot]
                  exact hE7
                rw [LieModule.mem_maxTrivSubmodule] at hnotmem
                push Not at hnotmem
                obtain ⟨Y, hY⟩ := hnotmem
                have hbr : ⁅injZeroE7 Y, injZeroE7 U.gZeroE7 + injZeroCenter U.gZeroCenter⁆ ∈ I :=
                  I.lie_mem hz
                have hbr' : ⁅injZeroE7 Y, injZeroE7 U.gZeroE7 + injZeroCenter U.gZeroCenter⁆ =
                    injZeroE7 ⁅Y, U.gZeroE7⁆ := by
                  rw [lie_add]
                  change bracket5LM (injZeroE7 Y) (injZeroE7 U.gZeroE7) +
                      bracket5LM (injZeroE7 Y) (injZeroCenter U.gZeroCenter) = _
                  rw [br_zE7_zE7, br_zE7_zC, add_zero]
                rw [hbr'] at hbr
                exact ideal_top_of_injZeroE7 I hY hbr
              · have hE70 : U.gZeroE7 = 0 := not_ne_iff.mp hE7
                have hC : U.gZeroCenter ≠ 0 := by
                  intro h0
                  apply hUne
                  apply FreudenthalTKK5E8.ext
                  · exact not_ne_iff.mp hgm2
                  · exact not_ne_iff.mp hgm1
                  · exact hE70
                  · exact h0
                  · exact not_ne_iff.mp hg1
                  · exact not_ne_iff.mp hg2
                rw [hE70, map_zero, zero_add] at hz
                have hZ : gradeCenterZ ∈ I := by
                  have hs := I.smul_mem U.gZeroCenter⁻¹ hz
                  have hcs : U.gZeroCenter⁻¹ • injZeroCenter U.gZeroCenter = gradeCenterZ := by
                    rw [← LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hC]
                    rfl
                  rwa [hcs] at hs
                exact ideal_top_of_gradeCenterZ I hZ
  non_abelian := by
    intro hab
    have h0 := hab.trivial gradeCenterZ ePlus2
    have h2 : ⁅gradeCenterZ, ePlus2⁆ = (2 : ℝ) • ePlus2 := by
      change bracket5LM (injZeroCenter 1) (injPlus2 1) = _
      rw [br_zC_p2]
      apply FreudenthalTKK5E8.ext <;> simp [ePlus2, injPlus2]
    rw [h0] at h2
    have h2' := congrArg FreudenthalTKK5E8.gPlus2 h2
    change (0 : FreudenthalTKK5E8).gPlus2 = ((2 : ℝ) • injPlus2 1).gPlus2 at h2'
    simp [injPlus2] at h2'

end Simplicity5E8

/-! ## Section 6: Cartan Involution (`+8` Signature), Invariant Form `B₅`, and `IsKilling` -/

section Cartan5E8

/-- Split-octonion Cartan involution `σ_Zorn (a, v, w, b) = (b, -w, -v, a)` on
`ZornVectorMatrix ℝ`, negating the 4D hyperbolic-skew direction and fixing the 4D compact `ℍ`
subalgebra. -/
def σZorn : ZornVectorMatrix ℝ ≃ₗ[ℝ] ZornVectorMatrix ℝ where
  toFun X := ⟨X.b, fun i => -X.w i, fun i => -X.v i, X.a⟩
  invFun X := ⟨X.b, fun i => -X.w i, fun i => -X.v i, X.a⟩
  left_inv X := by ext i <;> simp
  right_inv X := by ext i <;> simp
  map_add' X Y := by ext i <;> simp [ZornVectorMatrix.add] <;> abel
  map_smul' r X := by ext i <;> simp [ZornVectorMatrix.smul]

@[simp] theorem σZorn_a (X : ZornVectorMatrix ℝ) : (σZorn X).a = X.b := rfl
@[simp] theorem σZorn_v (X : ZornVectorMatrix ℝ) (i : Fin 3) : (σZorn X).v i = -X.w i := rfl
@[simp] theorem σZorn_w (X : ZornVectorMatrix ℝ) (i : Fin 3) : (σZorn X).w i = -X.v i := rfl
@[simp] theorem σZorn_b (X : ZornVectorMatrix ℝ) : (σZorn X).b = X.a := rfl

@[simp] theorem σZorn_involutive (X : ZornVectorMatrix ℝ) : σZorn (σZorn X) = X :=
  σZorn.left_inv X

@[simp] theorem σZorn_zero : σZorn 0 = 0 := σZorn.map_zero

@[simp] theorem σZorn_one : σZorn ZornVectorMatrix.one = ZornVectorMatrix.one := by
  ext i <;> simp [ZornVectorMatrix.one]

theorem σZorn_mul (X Y : ZornVectorMatrix ℝ) :
    σZorn (ZornVectorMatrix.mul X Y) = ZornVectorMatrix.mul (σZorn X) (σZorn Y) := by
  ext i <;>
    simp [ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross] <;>
    ring

theorem σZorn_conj (X : ZornVectorMatrix ℝ) :
    σZorn (ZornVectorMatrix.conj X) = ZornVectorMatrix.conj (σZorn X) := by
  ext i <;> simp [ZornVectorMatrix.conj]

theorem σZorn_trace (X : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.trace (σZorn X) = ZornVectorMatrix.trace X := by
  simp [ZornVectorMatrix.trace]; ring

theorem σZorn_norm (X : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.norm (σZorn X) = ZornVectorMatrix.norm X := by
  simp only [ZornVectorMatrix.norm, ZornVec3.dot, σZorn_a, σZorn_b, σZorn_v, σZorn_w,
    neg_mul, mul_neg, neg_neg]
  rw [mul_comm X.b X.a]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact mul_comm (X.w i) (X.v i)

theorem zornBilin_σZorn (X Y : ZornVectorMatrix ℝ) :
    zornBilin (σZorn X) (σZorn Y) = zornBilin X Y := by
  rw [zornBilin, zornBilin, ← σZorn_conj, ← σZorn_mul, σZorn_trace]

theorem zornBilin_σZorn_right (X Y : ZornVectorMatrix ℝ) :
    zornBilin X (σZorn Y) = zornBilin (σZorn X) Y := by
  calc zornBilin X (σZorn Y) = zornBilin (σZorn X) (σZorn (σZorn Y)) := (zornBilin_σZorn _ _).symm
    _ = zornBilin (σZorn X) Y := by rw [σZorn_involutive]

theorem zornBilin_σZorn_self_eq (X : ZornVectorMatrix ℝ) :
    zornBilin X (σZorn X) =
      X.a ^ 2 + X.b ^ 2 + ZornVec3.dot X.v X.v + ZornVec3.dot X.w X.w := by
  simp [zornBilin, ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVec3.dot]
  ring

theorem zornBilin_σZorn_self_nonneg (X : ZornVectorMatrix ℝ) :
    0 ≤ zornBilin X (σZorn X) := by
  rw [zornBilin_σZorn_self_eq, ZornVec3.dot_eq_sum_coords, ZornVec3.dot_eq_sum_coords]
  have hv0 : 0 ≤ X.v 0 * X.v 0 := mul_self_nonneg (X.v 0)
  have hv1 : 0 ≤ X.v 1 * X.v 1 := mul_self_nonneg (X.v 1)
  have hv2 : 0 ≤ X.v 2 * X.v 2 := mul_self_nonneg (X.v 2)
  have hw0 : 0 ≤ X.w 0 * X.w 0 := mul_self_nonneg (X.w 0)
  have hw1 : 0 ≤ X.w 1 * X.w 1 := mul_self_nonneg (X.w 1)
  have hw2 : 0 ≤ X.w 2 * X.w 2 := mul_self_nonneg (X.w 2)
  nlinarith [sq_nonneg X.a, sq_nonneg X.b]

theorem zornBilin_σZorn_self_eq_zero_iff (X : ZornVectorMatrix ℝ) :
    zornBilin X (σZorn X) = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [zornBilin_σZorn_self_eq, ZornVec3.dot_eq_sum_coords, ZornVec3.dot_eq_sum_coords] at h
    have hv0 : 0 ≤ X.v 0 * X.v 0 := mul_self_nonneg (X.v 0)
    have hv1 : 0 ≤ X.v 1 * X.v 1 := mul_self_nonneg (X.v 1)
    have hv2 : 0 ≤ X.v 2 * X.v 2 := mul_self_nonneg (X.v 2)
    have hw0 : 0 ≤ X.w 0 * X.w 0 := mul_self_nonneg (X.w 0)
    have hw1 : 0 ≤ X.w 1 * X.w 1 := mul_self_nonneg (X.w 1)
    have hw2 : 0 ≤ X.w 2 * X.w 2 := mul_self_nonneg (X.w 2)
    have ha : X.a = 0 := by nlinarith [sq_nonneg X.b]
    have hb : X.b = 0 := by nlinarith [sq_nonneg X.a]
    have h0v : X.v 0 = 0 := mul_self_eq_zero.mp (le_antisymm (by nlinarith [sq_nonneg X.a, sq_nonneg X.b]) hv0)
    have h1v : X.v 1 = 0 := mul_self_eq_zero.mp (le_antisymm (by nlinarith [sq_nonneg X.a, sq_nonneg X.b]) hv1)
    have h2v : X.v 2 = 0 := mul_self_eq_zero.mp (le_antisymm (by nlinarith [sq_nonneg X.a, sq_nonneg X.b]) hv2)
    have h0w : X.w 0 = 0 := mul_self_eq_zero.mp (le_antisymm (by nlinarith [sq_nonneg X.a, sq_nonneg X.b]) hw0)
    have h1w : X.w 1 = 0 := mul_self_eq_zero.mp (le_antisymm (by nlinarith [sq_nonneg X.a, sq_nonneg X.b]) hw1)
    have h2w : X.w 2 = 0 := mul_self_eq_zero.mp (le_antisymm (by nlinarith [sq_nonneg X.a, sq_nonneg X.b]) hw2)
    ext i
    · exact ha
    · fin_cases i <;> assumption
    · fin_cases i <;> assumption
    · exact hb
  · rintro rfl
    rw [map_zero]
    simp [zornBilin, ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace]

/-- Split-Albert Jordan involution `σ_H3` induced entrywise by `σZorn`. -/
def σH3 : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ where
  toFun X := ⟨X.α₁, X.α₂, X.α₃, σZorn X.a, σZorn X.b, σZorn X.c⟩
  invFun X := ⟨X.α₁, X.α₂, X.α₃, σZorn X.a, σZorn X.b, σZorn X.c⟩
  left_inv X := by apply H3Zorn.ext_h3 <;> simp
  right_inv X := by apply H3Zorn.ext_h3 <;> simp
  map_add' X Y := by
    apply H3Zorn.ext_h3 <;> simp [H3Zorn.add_readback]
    all_goals exact σZorn.map_add _ _
  map_smul' r X := by
    apply H3Zorn.ext_h3 <;> simp [H3Zorn.smul_readback]
    all_goals exact σZorn.map_smul _ _

@[simp] theorem σH3_α₁ (X : H3Zorn ℝ) : (σH3 X).α₁ = X.α₁ := rfl
@[simp] theorem σH3_α₂ (X : H3Zorn ℝ) : (σH3 X).α₂ = X.α₂ := rfl
@[simp] theorem σH3_α₃ (X : H3Zorn ℝ) : (σH3 X).α₃ = X.α₃ := rfl
@[simp] theorem σH3_a (X : H3Zorn ℝ) : (σH3 X).a = σZorn X.a := rfl
@[simp] theorem σH3_b (X : H3Zorn ℝ) : (σH3 X).b = σZorn X.b := rfl
@[simp] theorem σH3_c (X : H3Zorn ℝ) : (σH3 X).c = σZorn X.c := rfl

@[simp] theorem σH3_involutive (X : H3Zorn ℝ) : σH3 (σH3 X) = X := σH3.left_inv X

@[simp] theorem σH3_one : σH3 (1 : H3Zorn ℝ) = 1 := by
  have hz : σZorn ZornVectorMatrix.zero = ZornVectorMatrix.zero := by
    change σZorn (0 : ZornVectorMatrix ℝ) = 0
    exact σZorn_zero
  apply H3Zorn.ext_h3 <;> simp [H3Zorn.one_readback, hz]

theorem σH3_linearTrace (X : H3Zorn ℝ) :
    H3Zorn.linearTrace (σH3 X) = H3Zorn.linearTrace X := rfl

theorem σH3_traceBilin (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin (σH3 X) (σH3 Y) = H3Zorn.traceBilin X Y := by
  change (X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
      zornBilin (σZorn X.a) (σZorn Y.a) + zornBilin (σZorn X.b) (σZorn Y.b) +
      zornBilin (σZorn X.c) (σZorn Y.c)) =
    (X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
      zornBilin X.a Y.a + zornBilin X.b Y.b + zornBilin X.c Y.c)
  rw [zornBilin_σZorn, zornBilin_σZorn, zornBilin_σZorn]

theorem σH3_traceBilin_right (X Y : H3Zorn ℝ) :
    H3Zorn.traceBilin X (σH3 Y) = H3Zorn.traceBilin (σH3 X) Y := by
  calc H3Zorn.traceBilin X (σH3 Y) = H3Zorn.traceBilin (σH3 X) (σH3 (σH3 Y)) := (σH3_traceBilin _ _).symm
    _ = H3Zorn.traceBilin (σH3 X) Y := by rw [σH3_involutive]

theorem traceBilin_σH3_self_nonneg (X : H3Zorn ℝ) :
    0 ≤ H3Zorn.traceBilin X (σH3 X) := by
  change 0 ≤ X.α₁ * X.α₁ + X.α₂ * X.α₂ + X.α₃ * X.α₃ +
    zornBilin X.a (σZorn X.a) + zornBilin X.b (σZorn X.b) + zornBilin X.c (σZorn X.c)
  have ha := zornBilin_σZorn_self_nonneg X.a
  have hb := zornBilin_σZorn_self_nonneg X.b
  have hc := zornBilin_σZorn_self_nonneg X.c
  nlinarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃]

theorem traceBilin_σH3_self_eq_zero_iff (X : H3Zorn ℝ) :
    H3Zorn.traceBilin X (σH3 X) = 0 ↔ X = 0 := by
  constructor
  · intro h
    change X.α₁ * X.α₁ + X.α₂ * X.α₂ + X.α₃ * X.α₃ +
      zornBilin X.a (σZorn X.a) + zornBilin X.b (σZorn X.b) + zornBilin X.c (σZorn X.c) = 0 at h
    have ha := zornBilin_σZorn_self_nonneg X.a
    have hb := zornBilin_σZorn_self_nonneg X.b
    have hc := zornBilin_σZorn_self_nonneg X.c
    have h1 : X.α₁ = 0 := by nlinarith [sq_nonneg X.α₂, sq_nonneg X.α₃]
    have h2 : X.α₂ = 0 := by nlinarith [sq_nonneg X.α₁, sq_nonneg X.α₃]
    have h3 : X.α₃ = 0 := by nlinarith [sq_nonneg X.α₁, sq_nonneg X.α₂]
    have hza : X.a = 0 := (zornBilin_σZorn_self_eq_zero_iff X.a).mp (by linarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃])
    have hzb : X.b = 0 := (zornBilin_σZorn_self_eq_zero_iff X.b).mp (by linarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃])
    have hzc : X.c = 0 := (zornBilin_σZorn_self_eq_zero_iff X.c).mp (by linarith [sq_nonneg X.α₁, sq_nonneg X.α₂, sq_nonneg X.α₃])
    exact H3Zorn.ext_h3 X 0 h1 h2 h3 hza hzb hzc
  · rintro rfl
    rw [map_zero]
    exact H3Zorn.traceBilin_zero_right 0

theorem σH3_adjointQuad (X : H3Zorn ℝ) :
    σH3 (H3Zorn.adjointQuad X) = H3Zorn.adjointQuad (σH3 X) := by
  apply H3Zorn.ext_h3
  · simp [H3Zorn.adjointQuad, σZorn_norm]
  · simp [H3Zorn.adjointQuad, σZorn_norm]
  · simp [H3Zorn.adjointQuad, σZorn_norm]
  · change σZorn (ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.c)
        (ZornVectorMatrix.conj X.b)) (ZornVectorMatrix.smul X.α₃ X.a)) =
      ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn X.c))
        (ZornVectorMatrix.conj (σZorn X.b))) (ZornVectorMatrix.smul X.α₃ (σZorn X.a))
    rw [show ∀ u v : ZornVectorMatrix ℝ, ZornVectorMatrix.sub u v = u - v from fun _ _ => rfl,
      map_sub, σZorn_mul, σZorn_conj, σZorn_conj,
      show ∀ r (u : ZornVectorMatrix ℝ), ZornVectorMatrix.smul r u = r • u from fun _ _ => rfl,
      map_smul]
    rfl
  · change σZorn (ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.a)
        (ZornVectorMatrix.conj X.c)) (ZornVectorMatrix.smul X.α₁ X.b)) =
      ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn X.a))
        (ZornVectorMatrix.conj (σZorn X.c))) (ZornVectorMatrix.smul X.α₁ (σZorn X.b))
    rw [show ∀ u v : ZornVectorMatrix ℝ, ZornVectorMatrix.sub u v = u - v from fun _ _ => rfl,
      map_sub, σZorn_mul, σZorn_conj, σZorn_conj,
      show ∀ r (u : ZornVectorMatrix ℝ), ZornVectorMatrix.smul r u = r • u from fun _ _ => rfl,
      map_smul]
    rfl
  · change σZorn (ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.b)
        (ZornVectorMatrix.conj X.a)) (ZornVectorMatrix.smul X.α₂ X.c)) =
      ZornVectorMatrix.sub (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn X.b))
        (ZornVectorMatrix.conj (σZorn X.a))) (ZornVectorMatrix.smul X.α₂ (σZorn X.c))
    rw [show ∀ u v : ZornVectorMatrix ℝ, ZornVectorMatrix.sub u v = u - v from fun _ _ => rfl,
      map_sub, σZorn_mul, σZorn_conj, σZorn_conj,
      show ∀ r (u : ZornVectorMatrix ℝ), ZornVectorMatrix.smul r u = r • u from fun _ _ => rfl,
      map_smul]
    rfl

theorem σH3_crossProduct (X Y : H3Zorn ℝ) :
    σH3 (H3Zorn.crossProduct X Y) = H3Zorn.crossProduct (σH3 X) (σH3 Y) := by
  simp only [H3Zorn.crossProduct, map_sub, map_add, σH3_adjointQuad]

theorem σH3_U (X Y : H3Zorn ℝ) :
    σH3 (H3Zorn.U X Y) = H3Zorn.U (σH3 X) (σH3 Y) := by
  simp only [H3Zorn.U, map_sub, map_smul, σH3_traceBilin, σH3_crossProduct, σH3_adjointQuad]

theorem σH3_T (X Y Z : H3Zorn ℝ) :
    σH3 (H3Zorn.T X Y Z) = H3Zorn.T (σH3 X) (σH3 Y) (σH3 Z) := by
  simp only [H3Zorn.T, map_sub, ← map_add, σH3_U]

theorem σH3_mul (X Y : H3Zorn ℝ) : σH3 (X * Y) = σH3 X * σH3 Y := by
  change σH3 (candidateJordanMul X Y) = candidateJordanMul (σH3 X) (σH3 Y)
  simp only [candidateJordanMul, map_smul, σH3_T, σH3_one]

/-- Package `σH3` as a split-Albert Jordan automorphism `H3ZornJordanAut`. -/
def σH3Aut : H3ZornJordanAut :=
  ⟨σH3, σH3_one, σH3_mul⟩

@[simp] theorem σH3Aut_apply (X : H3Zorn ℝ) : σH3Aut X = σH3 X := rfl

theorem σH3_tripleD (x y z : H3Zorn ℝ) :
    σH3 (JordanTKK.tripleD ℝ x y z) = JordanTKK.tripleD ℝ (σH3 x) (σH3 y) (σH3 z) := by
  simp only [tripleD_apply_expanded, map_add, map_sub, map_smul,
    σH3_traceBilin, σH3_crossProduct]

/-- Conjugation by `σH3` on `Module.End ℝ (H3Zorn ℝ)`. -/
def σConjEnd : Module.End ℝ (H3Zorn ℝ) ≃ₗ[ℝ] Module.End ℝ (H3Zorn ℝ) :=
  σH3.conj

@[simp] theorem σConjEnd_apply (T : Module.End ℝ (H3Zorn ℝ)) (x : H3Zorn ℝ) :
    σConjEnd T x = σH3 (T (σH3 x)) := by
  change (σH3.toLinearMap ∘ₗ T ∘ₗ σH3.symm.toLinearMap) x = _
  rfl

@[simp] theorem σConjEnd_involutive (T : Module.End ℝ (H3Zorn ℝ)) :
    σConjEnd (σConjEnd T) = T := by
  apply LinearMap.ext; intro x; simp

theorem σConjEnd_comp (T₁ T₂ : Module.End ℝ (H3Zorn ℝ)) :
    σConjEnd (T₁ ∘ₗ T₂) = σConjEnd T₁ ∘ₗ σConjEnd T₂ := by
  apply LinearMap.ext; intro x; simp

theorem σConjEnd_h3zornTraceAdjoint (T : Module.End ℝ (H3Zorn ℝ)) :
    σConjEnd (h3zornTraceAdjoint T) = h3zornTraceAdjoint (σConjEnd T) := by
  apply LinearMap.ext; intro x
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro y
  calc H3Zorn.traceBilin (σConjEnd (h3zornTraceAdjoint T) x) y
      = H3Zorn.traceBilin (σH3 (h3zornTraceAdjoint T (σH3 x))) y := rfl
    _ = H3Zorn.traceBilin (h3zornTraceAdjoint T (σH3 x)) (σH3 y) :=
        (σH3_traceBilin_right _ _).symm
    _ = H3Zorn.traceBilin (σH3 x) (T (σH3 y)) := h3zornTraceAdjoint_pair T (σH3 x) (σH3 y)
    _ = H3Zorn.traceBilin x (σH3 (T (σH3 y))) := (σH3_traceBilin_right x (T (σH3 y))).symm
    _ = H3Zorn.traceBilin x (σConjEnd T y) := rfl
    _ = H3Zorn.traceBilin (h3zornTraceAdjoint (σConjEnd T) x) y :=
        (h3zornTraceAdjoint_pair (σConjEnd T) x y).symm

theorem σConjEnd_mem_str {T : Module.End ℝ (H3Zorn ℝ)} (hT : T ∈ h3zornTKKDatum.str) :
    σConjEnd T ∈ h3zornTKKDatum.str := by
  rcases h3zornTKKDatum.str_decomp T hT with ⟨D, a, rfl⟩
  have hD' : σConjEnd (D : Module.End ℝ (H3Zorn ℝ)) ∈ H3ZornF4Derivations := by
    have hcon : σConjEnd (D : Module.End ℝ (H3Zorn ℝ)) = σH3Aut.toLinearEquiv.lieConj D.1 := by
      apply LinearMap.ext; intro x; rfl
    rw [hcon]
    exact H3ZornJordanAut.lieConj_mem_F4 σH3Aut D.2
  have hDstr : σConjEnd (D : Module.End ℝ (H3Zorn ℝ)) ∈ h3zornTKKDatum.str :=
    ⟨⟨_, hD'⟩, 0, by
      change σConjEnd (D : Module.End ℝ (H3Zorn ℝ)) =
        σConjEnd (D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) (0 : H3Zorn ℝ)
      have h0 : jordanLmul (R := ℝ) (0 : H3Zorn ℝ) = 0 := by
        apply LinearMap.ext; intro z; change (0 : H3Zorn ℝ) * z = 0; exact zero_mul z
      rw [h0, add_zero]⟩
  have ha' : σConjEnd (jordanLmul (R := ℝ) a) = jordanLmul (R := ℝ) (σH3 a) := by
    apply LinearMap.ext; intro x
    change σH3 (a * σH3 x) = σH3 a * x
    rw [σH3_mul, σH3_involutive]
  rw [map_add, ha']
  exact h3zornTKKDatum.str.add_mem hDstr (h3zornTKKDatum.jordanLmul_mem_str (σH3 a))

@[simp] theorem σConjEnd_tripleD (x y : H3Zorn ℝ) :
    σConjEnd (JordanTKK.tripleD ℝ x y) = JordanTKK.tripleD ℝ (σH3 x) (σH3 y) := by
  apply LinearMap.ext; intro z
  simp only [σConjEnd_apply, σH3_tripleD, σH3_involutive]

/-- Cartan involution `θ_E7` on 133-dimensional split `𝔈₇(7)` (`H3ZornTKKLie`):
`θ_E7 (B, T₀, A) = (-σH3 A, -σConjEnd (T₀*), -σH3 B)`. -/
def θE7 : H3ZornTKKLie ≃ₗ⁅ℝ⁆ H3ZornTKKLie where
  toFun X :=
    { neg := -σH3 X.pos
      zero := ⟨-σConjEnd (h3zornTraceAdjoint X.zero.1),
        h3zornTKKDatum.str.neg_mem (σConjEnd_mem_str (h3zornTKKDatum.adj_mem_str X.zero.2))⟩
      pos := -σH3 X.neg }
  invFun X :=
    { neg := -σH3 X.pos
      zero := ⟨-σConjEnd (h3zornTraceAdjoint X.zero.1),
        h3zornTKKDatum.str.neg_mem (σConjEnd_mem_str (h3zornTKKDatum.adj_mem_str X.zero.2))⟩
      pos := -σH3 X.neg }
  left_inv X := by
    apply h3zornTKKLie_ext
    · simp
    · apply Subtype.ext
      change -σConjEnd (h3zornTraceAdjoint (-σConjEnd (h3zornTraceAdjoint X.zero.1))) = X.zero.1
      rw [← h3zornTraceAdjointLM_apply, map_neg, h3zornTraceAdjointLM_apply, map_neg, neg_neg,
        σConjEnd_h3zornTraceAdjoint, σConjEnd_involutive, h3zornTraceAdjoint_involutive]
    · simp
  right_inv X := by
    apply h3zornTKKLie_ext
    · simp
    · apply Subtype.ext
      change -σConjEnd (h3zornTraceAdjoint (-σConjEnd (h3zornTraceAdjoint X.zero.1))) = X.zero.1
      rw [← h3zornTraceAdjointLM_apply, map_neg, h3zornTraceAdjointLM_apply, map_neg, neg_neg,
        σConjEnd_h3zornTraceAdjoint, σConjEnd_involutive, h3zornTraceAdjoint_involutive]
    · simp
  map_add' X Y := by
    apply h3zornTKKLie_ext
    · simp; abel
    · apply Subtype.ext
      change -σConjEnd (h3zornTraceAdjoint (X.zero.1 + Y.zero.1)) =
        -σConjEnd (h3zornTraceAdjoint X.zero.1) + -σConjEnd (h3zornTraceAdjoint Y.zero.1)
      rw [← h3zornTraceAdjointLM_apply, map_add, map_add, h3zornTraceAdjointLM_apply,
        h3zornTraceAdjointLM_apply]
      abel
    · simp; abel
  map_smul' r X := by
    apply h3zornTKKLie_ext
    · simp
    · apply Subtype.ext
      change -σConjEnd (h3zornTraceAdjoint (r • X.zero.1)) =
        r • (-σConjEnd (h3zornTraceAdjoint X.zero.1))
      rw [← h3zornTraceAdjointLM_apply, map_smul, map_smul, h3zornTraceAdjointLM_apply, smul_neg]
    · simp
  map_lie' {X Y} := by
    apply h3zornTKKLie_ext
    · change -σH3 (-h3zornTraceAdjoint X.zero.1 Y.pos + h3zornTraceAdjoint Y.zero.1 X.pos) =
        (-σConjEnd (h3zornTraceAdjoint X.zero.1)) (-σH3 Y.pos) -
          (-σConjEnd (h3zornTraceAdjoint Y.zero.1)) (-σH3 X.pos)
      simp only [LinearMap.neg_apply, σConjEnd_apply, map_neg, map_add, σH3_involutive, neg_neg]
      abel
    · apply Subtype.ext
      change -σConjEnd (h3zornTraceAdjoint ((X.zero.1 ∘ₗ Y.zero.1 - Y.zero.1 ∘ₗ X.zero.1) +
          (JordanTKK.tripleD ℝ X.neg Y.pos - JordanTKK.tripleD ℝ Y.neg X.pos))) =
        ((-σConjEnd (h3zornTraceAdjoint X.zero.1)) ∘ₗ (-σConjEnd (h3zornTraceAdjoint Y.zero.1)) -
          (-σConjEnd (h3zornTraceAdjoint Y.zero.1)) ∘ₗ (-σConjEnd (h3zornTraceAdjoint X.zero.1))) +
        (JordanTKK.tripleD ℝ (-σH3 X.pos) (-σH3 Y.neg) -
          JordanTKK.tripleD ℝ (-σH3 Y.pos) (-σH3 X.neg))
      rw [← h3zornTraceAdjointLM_apply, map_add, map_sub, map_sub,
        h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
        h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
        h3zornTraceAdjoint_comp, h3zornTraceAdjoint_comp]
      have hadj_tri : ∀ u v : H3Zorn ℝ,
          h3zornTraceAdjoint (JordanTKK.tripleD ℝ u v) = JordanTKK.tripleD ℝ v u :=
        h3zornTKKDatum.adj_tripleD
      rw [hadj_tri X.neg Y.pos, hadj_tri Y.neg X.pos,
        map_add, map_sub, map_sub, σConjEnd_comp, σConjEnd_comp,
        σConjEnd_tripleD, σConjEnd_tripleD,
        tripleD_neg_left, tripleD_neg_right, tripleD_neg_left, tripleD_neg_right,
        neg_neg, neg_neg]
      simp only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, neg_add, neg_sub]
    · change -σH3 (X.zero.1 Y.neg - Y.zero.1 X.neg) =
        -h3zornTraceAdjoint (-σConjEnd (h3zornTraceAdjoint X.zero.1)) (-σH3 Y.neg) +
          h3zornTraceAdjoint (-σConjEnd (h3zornTraceAdjoint Y.zero.1)) (-σH3 X.neg)
      have hadj_neg : ∀ Z : H3ZornTKKLie,
          h3zornTraceAdjoint (-σConjEnd (h3zornTraceAdjoint Z.zero.1)) = -σConjEnd Z.zero.1 := fun Z => by
        rw [← h3zornTraceAdjointLM_apply, map_neg, h3zornTraceAdjointLM_apply,
          ← σConjEnd_h3zornTraceAdjoint, h3zornTraceAdjoint_involutive]
      rw [hadj_neg X, hadj_neg Y]
      simp only [LinearMap.neg_apply, σConjEnd_apply, map_neg, map_sub, σH3_involutive, neg_neg]
      abel

@[simp] theorem θE7_neg (X : H3ZornTKKLie) : (θE7 X).neg = -σH3 X.pos := rfl
@[simp] theorem θE7_zero_coe (X : H3ZornTKKLie) :
    (θE7 X).zero.1 = -σConjEnd (h3zornTraceAdjoint X.zero.1) := rfl
@[simp] theorem θE7_pos (X : H3ZornTKKLie) : (θE7 X).pos = -σH3 X.neg := rfl
@[simp] theorem θE7_involutive (X : H3ZornTKKLie) : θE7 (θE7 X) = X := θE7.left_inv X

@[simp] theorem strTrace_θE7 (T₀ : h3zornTKKDatum.str) :
    strTrace ⟨-σConjEnd (h3zornTraceAdjoint T₀.1),
      h3zornTKKDatum.str.neg_mem (σConjEnd_mem_str (h3zornTKKDatum.adj_mem_str T₀.2))⟩ =
      -strTrace T₀ := by
  change H3Zorn.linearTrace (-σH3 (h3zornTraceAdjoint T₀.1 (σH3 1))) = -H3Zorn.linearTrace (T₀.1 1)
  have hneg : ∀ x : H3Zorn ℝ, H3Zorn.linearTrace (-x) = -H3Zorn.linearTrace x := fun x => by
    rw [show -x = (-1 : ℝ) • x from (neg_one_smul ℝ x).symm, H3Zorn.linearTrace_smul]
    ring
  rw [σH3_one, hneg, σH3_linearTrace, ← H3Zorn.traceBilin_one, h3zornTraceAdjoint_pair,
    H3Zorn.traceBilin_symm, H3Zorn.traceBilin_one]

/-- Scaled charge involution `σC (α, β, x, y) = (-β/4, 2α, -σH3 y, (1/2) σH3 x)` satisfying
`σC² = -(1/2) • id` and `symplecticForm (σC Q₁) (σC Q₂) = (1/2) * symplecticForm Q₁ Q₂`. -/
def σC : Charge ≃ₗ[ℝ] Charge where
  toFun Q :=
    { alpha := -(1 / 4 : ℝ) * Q.beta
      beta := 2 * Q.alpha
      x := -σH3 Q.y
      y := (1 / 2 : ℝ) • σH3 Q.x }
  invFun Q :=
    { alpha := (1 / 2 : ℝ) * Q.beta
      beta := -4 * Q.alpha
      x := (2 : ℝ) • σH3 Q.y
      y := -σH3 Q.x }
  left_inv Q := by
    apply FreudenthalCharge.ext <;> simp
  right_inv Q := by
    apply FreudenthalCharge.ext <;> simp
  map_add' Q₁ Q₂ := by
    apply FreudenthalCharge.ext
    · simp [alpha_add]; ring
    · simp [beta_add]; ring
    · simp [x_add, map_add]; abel
    · simp [y_add, map_add, smul_add]
  map_smul' r Q := by
    apply FreudenthalCharge.ext
    · simp [alpha_smul]; ring
    · simp [beta_smul]; ring
    · simp [x_smul, map_smul]
    · simp [y_smul, map_smul, smul_smul]; congr 1; ring

@[simp] theorem σC_alpha (Q : Charge) : (σC Q).alpha = -(1 / 4 : ℝ) * Q.beta := rfl
@[simp] theorem σC_beta (Q : Charge) : (σC Q).beta = 2 * Q.alpha := rfl
@[simp] theorem σC_x (Q : Charge) : (σC Q).x = -σH3 Q.y := rfl
@[simp] theorem σC_y (Q : Charge) : (σC Q).y = (1 / 2 : ℝ) • σH3 Q.x := rfl

theorem σC_sq (Q : Charge) : σC (σC Q) = -(1 / 2 : ℝ) • Q := by
  apply FreudenthalCharge.ext <;> simp <;> ring

theorem symplecticForm_σC (Q₁ Q₂ : Charge) :
    symplecticForm (σC Q₁) (σC Q₂) = (1 / 2 : ℝ) * symplecticForm Q₁ Q₂ := by
  rw [symplecticForm_expanded, symplecticForm_expanded]
  simp only [σC_alpha, σC_beta, σC_x, σC_y, h3_traceBilin_neg_left, h3_traceBilin_neg_right,
    H3Zorn.traceBilin_smul_left, H3Zorn.traceBilin_smul_right, σH3_traceBilin]
  ring

theorem symplecticForm_σC_self_eq (Q : Charge) :
    symplecticForm Q (σC Q) =
      2 * Q.alpha ^ 2 + (1 / 4 : ℝ) * Q.beta ^ 2 +
        (1 / 2 : ℝ) * H3Zorn.traceBilin Q.x (σH3 Q.x) + H3Zorn.traceBilin Q.y (σH3 Q.y) := by
  rw [symplecticForm_expanded]
  simp only [σC_alpha, σC_beta, σC_x, σC_y, h3_traceBilin_neg_right, H3Zorn.traceBilin_smul_right]
  rw [H3Zorn.traceBilin_symm Q.y (σH3 Q.y)]
  ring

theorem symplecticForm_σC_self_nonneg (Q : Charge) :
    0 ≤ symplecticForm Q (σC Q) := by
  rw [symplecticForm_σC_self_eq]
  have hx := traceBilin_σH3_self_nonneg Q.x
  have hy := traceBilin_σH3_self_nonneg Q.y
  nlinarith [sq_nonneg Q.alpha, sq_nonneg Q.beta]

theorem symplecticForm_σC_self_eq_zero_iff (Q : Charge) :
    symplecticForm Q (σC Q) = 0 ↔ Q = 0 := by
  constructor
  · intro h
    rw [symplecticForm_σC_self_eq] at h
    have hx := traceBilin_σH3_self_nonneg Q.x
    have hy := traceBilin_σH3_self_nonneg Q.y
    have ha : Q.alpha = 0 := by nlinarith [sq_nonneg Q.beta]
    have hb : Q.beta = 0 := by nlinarith [sq_nonneg Q.alpha]
    have hx0 : Q.x = 0 := (traceBilin_σH3_self_eq_zero_iff Q.x).mp (by nlinarith [sq_nonneg Q.alpha, sq_nonneg Q.beta])
    have hy0 : Q.y = 0 := (traceBilin_σH3_self_eq_zero_iff Q.y).mp (by nlinarith [sq_nonneg Q.alpha, sq_nonneg Q.beta])
    exact FreudenthalCharge.ext ha hb hx0 hy0
  · rintro rfl
    simp

theorem σC_repE7 (X : H3ZornTKKLie) (Q : Charge) :
    σC (repE7 X Q) = repE7 (θE7 X) (σC Q) := by
  have htr : strTrace (θE7 X).zero = -strTrace X.zero := strTrace_θE7 X.zero
  have hadj0 : h3zornTraceAdjoint (θE7 X).zero.1 = -σConjEnd X.zero.1 := by
    rw [θE7_zero_coe, ← h3zornTraceAdjointLM_apply, map_neg, h3zornTraceAdjointLM_apply,
      ← σConjEnd_h3zornTraceAdjoint, h3zornTraceAdjoint_involutive]
  apply FreudenthalCharge.ext
  · simp only [σC_alpha, repE7_beta, repE7_alpha, θE7_neg, σC_y, htr,
      h3_traceBilin_neg_left, H3Zorn.traceBilin_smul_right, σH3_traceBilin]
    ring
  · simp only [σC_beta, repE7_alpha, repE7_beta, θE7_pos, σC_x, htr,
      h3_traceBilin_neg_left, h3_traceBilin_neg_right, σH3_traceBilin]
    ring
  · simp only [σC_x, repE7_y, repE7_x, θE7_neg, θE7_pos, θE7_zero_coe,
      σC_beta, σC_y, htr, LinearMap.neg_apply, σConjEnd_apply, map_add,
      map_neg, map_smul, σH3_involutive, σH3_crossProduct,
      H3Zorn.crossProduct_smul_right, h3_crossProduct_neg_left]
    module
  · simp only [σC_y, repE7_x, repE7_y, θE7_neg, θE7_pos, σC_alpha, σC_x, htr, hadj0,
      LinearMap.neg_apply, σConjEnd_apply, map_add, map_sub, map_smul,
      σH3_involutive, σH3_crossProduct,
      h3_crossProduct_neg_left, h3_crossProduct_neg_right, smul_add, smul_sub, smul_neg, smul_smul]
    norm_num
    module

theorem θE7_K (Q₁ Q₂ : Charge) :
    θE7 (K Q₁ Q₂) = (2 : ℝ) • K (σC Q₁) (σC Q₂) := by
  apply h3zornTKKLie_ext
  · simp only [θE7_neg, h3tkk_smul_neg, K_pos, K_neg, σC_alpha, σC_x, σC_y,
      map_neg, map_add, map_smul, neg_neg, σH3_crossProduct,
      H3Zorn.crossProduct_smul_left, H3Zorn.crossProduct_smul_right,
      smul_add, smul_neg, smul_smul, ← neg_smul]
    have hmul : ∀ b : ℝ, 2 * (2 * -(-(1 / 4 : ℝ) * b)) = b := fun b => by ring
    have hc : (2 : ℝ) * (2 * (1 / 2 * (1 / 2 : ℝ))) = 1 := by norm_num
    simp only [hmul, hc, one_smul]
  · apply Subtype.ext
    apply LinearMap.ext; intro w
    have hadj1 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₁.x Q₂.y) =
        JordanTKK.tripleD ℝ Q₂.y Q₁.x :=
      h3zornTKKDatum.adj_tripleD Q₁.x Q₂.y
    have hadj2 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ Q₂.x Q₁.y) =
        JordanTKK.tripleD ℝ Q₁.y Q₂.x :=
      h3zornTKKDatum.adj_tripleD Q₂.x Q₁.y
    have hadj0 : h3zornTraceAdjoint (K Q₁ Q₂).zero.1 =
        (-2 : ℝ) • (JordanTKK.tripleD ℝ Q₂.y Q₁.x + JordanTKK.tripleD ℝ Q₁.y Q₂.x) +
        (-(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
          H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y) • h3zornStrOne.1 := by
      change h3zornTraceAdjointLM (K Q₁ Q₂).zero.1 = _
      simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul,
        h3zornTraceAdjointLM_apply, hadj1, hadj2, h3zornTraceAdjoint_h3zornStrOne]
    have hL : (θE7 (K Q₁ Q₂)).zero.1 w =
        -σConjEnd (h3zornTraceAdjoint (K Q₁ Q₂).zero.1) w := rfl
    rw [hL, hadj0]
    simp only [h3tkk_smul_zero, Submodule.coe_smul, Submodule.coe_add, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.neg_apply, σConjEnd_apply, σConjEnd_tripleD,
      map_add, map_smul, σH3_involutive,
      K_zero, h3zornStrOne_apply, σC_alpha, σC_beta, σC_x, σC_y,
      tripleD_neg_left, tripleD_smul_right, h3_traceBilin_neg_left,
      H3Zorn.traceBilin_smul_right, σH3_traceBilin]
    rw [H3Zorn.traceBilin_symm Q₁.y Q₂.x, H3Zorn.traceBilin_symm Q₂.y Q₁.x]
    simp only [smul_add, smul_neg, neg_add, smul_smul]
    norm_num
    module
  · simp only [θE7_pos, h3tkk_smul_pos, K_neg, K_pos, σC_beta, σC_y,
      map_smul, map_add, σH3_crossProduct,
      smul_add, smul_neg, smul_smul]
    norm_num
    module

private def θ₅Fun (U : FreudenthalTKK5E8) : FreudenthalTKK5E8 :=
  { gMinus2 := -U.gPlus2
    gMinus1 := Real.sqrt 2 • σC U.gPlus1
    gZeroE7 := θE7 U.gZeroE7
    gZeroCenter := -U.gZeroCenter
    gPlus1 := -(Real.sqrt 2) • σC U.gMinus1
    gPlus2 := -U.gMinus2 }

private theorem θ₅Fun_involutive (U : FreudenthalTKK5E8) : θ₅Fun (θ₅Fun U) = U := by
  have hs2 : Real.sqrt 2 * (Real.sqrt 2 * (2⁻¹ : ℝ)) = 1 := by
    rw [← mul_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
  apply FreudenthalTKK5E8.ext <;> simp [θ₅Fun, map_smul, map_neg, σC_sq, smul_smul]
  · rw [hs2, one_smul]
  · rw [hs2, one_smul]

/-- Cartan involution `θ₅ : FreudenthalTKK5E8 ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8` on the 248-dimensional
5-graded split `𝔈₈(8)` Lie algebra, yielding compact `120D` (`+1`) and non-compact `128D` (`-1`)
eigenspaces (`+8` Cartan signature). -/
def θ₅ : FreudenthalTKK5E8 ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8 where
  toFun := θ₅Fun
  invFun := θ₅Fun
  left_inv := θ₅Fun_involutive
  right_inv := θ₅Fun_involutive
  map_add' U V := by
    apply FreudenthalTKK5E8.ext <;> simp [θ₅Fun, map_add, smul_add] <;> ring
  map_smul' r U := by
    apply FreudenthalTKK5E8.ext <;> simp [θ₅Fun, map_smul] <;>
      rw [smul_smul, mul_comm (Real.sqrt 2) r, ← smul_smul]
  map_lie' {U V} := by
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    change θ₅Fun (bracket5LM U V) = bracket5LM (θ₅Fun U) (θ₅Fun V)
    apply FreudenthalTKK5E8.ext
    · simp only [θ₅Fun, bracket5LM_gMinus2, bracket5LM_gPlus2,
        symp_smul_left, symp_smul_right, symplecticForm_σC]
      have hsq : Real.sqrt 2 * (Real.sqrt 2 * (1 / 2 * symplecticForm U.gPlus1 V.gPlus1)) =
          symplecticForm U.gPlus1 V.gPlus1 := by
        rw [← mul_assoc, ← mul_assoc, hs2]; ring
      rw [hsq]
      ring
    · simp only [θ₅Fun, bracket5LM_gMinus1, bracket5LM_gPlus1,
        map_add, map_sub, map_smul, σC_repE7, smul_smul]
      module
    · simp only [θ₅Fun, bracket5LM_gZeroE7, map_add, map_sub, LieEquiv.map_lie,
        K_smul_left, K_smul_right, θE7_K, smul_smul]
      have hsq2 : Real.sqrt 2 * -Real.sqrt 2 = -2 := by rw [mul_neg, hs2]
      rw [hsq2, K_symm (σC U.gPlus1) (σC V.gMinus1), K_symm (σC V.gPlus1) (σC U.gMinus1)]
      module
    · simp only [θ₅Fun, bracket5LM_gZeroCenter, symp_smul_left,
        symp_smul_right, symplecticForm_σC, mul_neg, neg_mul]
      have hsq1 : Real.sqrt 2 * (Real.sqrt 2 * (1 / 2 * symplecticForm U.gMinus1 V.gPlus1)) =
          symplecticForm U.gMinus1 V.gPlus1 := by
        rw [← mul_assoc, ← mul_assoc, hs2]; ring
      have hsq2 : Real.sqrt 2 * (Real.sqrt 2 * (1 / 2 * symplecticForm V.gMinus1 U.gPlus1)) =
          symplecticForm V.gMinus1 U.gPlus1 := by
        rw [← mul_assoc, ← mul_assoc, hs2]; ring
      rw [hsq1, hsq2, symplecticForm_skew U.gMinus1 V.gPlus1, symplecticForm_skew V.gMinus1 U.gPlus1]
      ring
    · simp only [θ₅Fun, bracket5LM_gPlus1, bracket5LM_gMinus1,
        map_add, map_sub, map_smul, σC_repE7, smul_smul]
      module
    · simp only [θ₅Fun, bracket5LM_gPlus2, bracket5LM_gMinus2,
        symp_smul_left, symp_smul_right, symplecticForm_σC, mul_neg, neg_mul, neg_neg]
      have hsq : Real.sqrt 2 * (Real.sqrt 2 * (1 / 2 * symplecticForm U.gMinus1 V.gMinus1)) =
          symplecticForm U.gMinus1 V.gMinus1 := by
        rw [← mul_assoc, ← mul_assoc, hs2]; ring
      rw [hsq]
      ring

@[simp] theorem θ₅_gMinus2 (U : FreudenthalTKK5E8) : (θ₅ U).gMinus2 = -U.gPlus2 := rfl
@[simp] theorem θ₅_gMinus1 (U : FreudenthalTKK5E8) : (θ₅ U).gMinus1 = Real.sqrt 2 • σC U.gPlus1 := rfl
@[simp] theorem θ₅_gZeroE7 (U : FreudenthalTKK5E8) : (θ₅ U).gZeroE7 = θE7 U.gZeroE7 := rfl
@[simp] theorem θ₅_gZeroCenter (U : FreudenthalTKK5E8) : (θ₅ U).gZeroCenter = -U.gZeroCenter := rfl
@[simp] theorem θ₅_gPlus1 (U : FreudenthalTKK5E8) : (θ₅ U).gPlus1 = -(Real.sqrt 2) • σC U.gMinus1 := rfl
@[simp] theorem θ₅_gPlus2 (U : FreudenthalTKK5E8) : (θ₅ U).gPlus2 = -U.gMinus2 := rfl
@[simp] theorem θ₅_involutive (U : FreudenthalTKK5E8) : θ₅ (θ₅ U) = U := θ₅.left_inv U

/-! ### Structure Splitting of `h3zornTKKDatum.str` & Invariant Form `B_E7` -/

/-- The `H3Zorn ℝ` Jordan multiplication part `T(1)` of `T ∈ h3zornTKKDatum.str`. -/
def tkk5StrLmulPart : h3zornTKKDatum.str →ₗ[ℝ] H3Zorn ℝ where
  toFun T := T.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `H3ZornF4Derivations` derivation part `T - L_{T(1)}` of `T ∈ h3zornTKKDatum.str`. -/
def tkk5StrDerivPart (T : h3zornTKKDatum.str) : H3ZornF4Derivations :=
  (structureOperatorDirectSumEquiv.symm ⟨T.1, T.2⟩).1

theorem tkk5StrDerivPart_coe (T : h3zornTKKDatum.str) :
    (tkk5StrDerivPart T : Module.End ℝ (H3Zorn ℝ)) = T.1 - jordanLmul (R := ℝ) (tkk5StrLmulPart T) := by
  have hsurj := structureOperatorDirectSumEquiv.apply_symm_apply ⟨T.1, T.2⟩
  have heq : T.1 = (tkk5StrDerivPart T).1 + jordanLmul (R := ℝ)
      (structureOperatorDirectSumEquiv.symm ⟨T.1, T.2⟩).2 :=
    (congrArg Subtype.val hsurj).symm
  have h1 := LinearMap.ext_iff.mp heq (1 : H3Zorn ℝ)
  have hb : (structureOperatorDirectSumEquiv.symm ⟨T.1, T.2⟩).2 = tkk5StrLmulPart T := by
    change T.1 1 = (tkk5StrDerivPart T).1 1 + _ * 1 at h1
    rw [h3ZornF4_derivation_apply_one_eq_zero, zero_add] at h1
    change T.1 1 = candidateJordanMul _ 1 at h1
    rw [candidateJordanMul_one_right] at h1
    exact h1.symm
  rw [hb] at heq
  exact eq_sub_of_add_eq heq.symm

theorem tkk5StrDerivPart_add (T₁ T₂ : h3zornTKKDatum.str) :
    tkk5StrDerivPart (T₁ + T₂) = tkk5StrDerivPart T₁ + tkk5StrDerivPart T₂ := by
  apply Subtype.ext
  rw [Submodule.coe_add, tkk5StrDerivPart_coe, tkk5StrDerivPart_coe, tkk5StrDerivPart_coe]
  simp only [Submodule.coe_add, map_add]
  apply LinearMap.ext; intro x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, jordanLmul_apply]
  change T₁.1 x + T₂.1 x - (T₁.1 1 + T₂.1 1) * x =
    (T₁.1 x - T₁.1 1 * x) + (T₂.1 x - T₂.1 1 * x)
  rw [add_mul]; abel

theorem tkk5StrDerivPart_smul (r : ℝ) (T : h3zornTKKDatum.str) :
    tkk5StrDerivPart (r • T) = r • tkk5StrDerivPart T := by
  apply Subtype.ext
  rw [SetLike.val_smul, tkk5StrDerivPart_coe, tkk5StrDerivPart_coe]
  simp only [Submodule.coe_smul, map_smul]
  apply LinearMap.ext; intro x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, jordanLmul_apply]
  change r • T.1 x - (r • T.1 1) * x = r • (T.1 x - T.1 1 * x)
  rw [← candidateJordanMul_eq_mul, candidateJordanMul_smul_left, candidateJordanMul_eq_mul, smul_sub]

theorem strLmulPart_θE7 (T : h3zornTKKDatum.str) :
    tkk5StrLmulPart ⟨-σConjEnd (h3zornTraceAdjoint T.1),
        h3zornTKKDatum.str.neg_mem (σConjEnd_mem_str (h3zornTKKDatum.adj_mem_str T.2))⟩ =
      -σH3 (tkk5StrLmulPart T) := by
  change -σH3 (h3zornTraceAdjoint T.1 (σH3 1)) = -σH3 (T.1 1)
  rw [σH3_one]
  congr 1
  rcases h3zornTKKDatum.str_decomp T.1 T.2 with ⟨D, a, hT⟩
  have hT1 : T.1 1 = a := by
    rw [hT, LinearMap.add_apply, jordanLmul_apply,
      h3ZornF4_derivation_apply_one_eq_zero ⟨D.1, D.2⟩, zero_add]
    change candidateJordanMul a 1 = a
    exact candidateJordanMul_one_right a
  have hadj : h3zornTraceAdjoint T.1 = -(D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a := by
    rw [hT, show h3zornTraceAdjoint ((D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a) =
        h3zornTraceAdjointLM ((D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a) from rfl,
      map_add, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjoint_derivation, h3zornTraceAdjoint_jordanLmul]
  rw [hadj, LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply,
    h3ZornF4_derivation_apply_one_eq_zero ⟨D.1, D.2⟩, neg_zero, zero_add]
  have ha1 : a * (1 : H3Zorn ℝ) = a := candidateJordanMul_one_right a
  rw [ha1, hT1]

theorem strDerivPart_θE7 (T : h3zornTKKDatum.str) :
    tkk5StrDerivPart ⟨-σConjEnd (h3zornTraceAdjoint T.1),
        h3zornTKKDatum.str.neg_mem (σConjEnd_mem_str (h3zornTKKDatum.adj_mem_str T.2))⟩ =
      H3ZornJordanAut.derivationLieEquiv σH3Aut (tkk5StrDerivPart T) := by
  apply Subtype.ext
  rw [tkk5StrDerivPart_coe, strLmulPart_θE7, H3ZornJordanAut.derivationLieEquiv_apply]
  change -σConjEnd (h3zornTraceAdjoint T.1) - jordanLmul (R := ℝ) (-σH3 (T.1 1)) =
    σConjEnd (tkk5StrDerivPart T).1
  rw [tkk5StrDerivPart_coe]
  rcases h3zornTKKDatum.str_decomp T.1 T.2 with ⟨D, a, hT⟩
  have hT1 : T.1 1 = a := by
    rw [hT, LinearMap.add_apply, jordanLmul_apply,
      h3ZornF4_derivation_apply_one_eq_zero ⟨D.1, D.2⟩, zero_add]
    change candidateJordanMul a 1 = a
    exact candidateJordanMul_one_right a
  have hadj : h3zornTraceAdjoint T.1 = -(D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a := by
    rw [hT, show h3zornTraceAdjoint ((D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a) =
        h3zornTraceAdjointLM ((D : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a) from rfl,
      map_add, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjoint_derivation, h3zornTraceAdjoint_jordanLmul]
  have hs1 : tkk5StrLmulPart T = a := hT1
  rw [hadj, hT1, hs1, hT, add_sub_cancel_right]
  apply LinearMap.ext; intro x
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
    σConjEnd_apply, jordanLmul_apply, map_add, map_neg]
  change -( -σH3 (D.1 (σH3 x)) + σH3 (a * σH3 x) ) - (-σH3 a) * x = σH3 (D.1 (σH3 x))
  rw [show (-σH3 a) * x = -(σH3 a * x) by
    rw [← candidateJordanMul_eq_mul, ← candidateJordanMul_eq_mul,
      show -σH3 a = (-1 : ℝ) • σH3 a by module, candidateJordanMul_smul_left]; module]
  rw [σH3_mul, σH3_involutive]
  abel

/-- Ad-invariant symmetric bilinear form on `H3ZornTKKLie` (`𝔈₇(7)`). -/
private def bE7Raw (X Y : H3ZornTKKLie) : ℝ :=
  LinearMap.trace ℝ (H3Zorn ℝ) ((tkk5StrDerivPart X.zero).1 * (tkk5StrDerivPart Y.zero).1) +
    3 * H3Zorn.traceBilin (tkk5StrLmulPart X.zero) (tkk5StrLmulPart Y.zero) +
    3 * (H3Zorn.traceBilin X.neg Y.pos + H3Zorn.traceBilin X.pos Y.neg)

private theorem strDerivPart_coe_add (D₁ D₂ : H3ZornF4Derivations) :
    ((D₁ + D₂ : H3ZornF4Derivations) : Module.End ℝ (H3Zorn ℝ)) = D₁.1 + D₂.1 := rfl

private theorem strDerivPart_coe_smul (r : ℝ) (D : H3ZornF4Derivations) :
    ((r • D : H3ZornF4Derivations) : Module.End ℝ (H3Zorn ℝ)) = r • D.1 := rfl

private def bE7Right (X : H3ZornTKKLie) : H3ZornTKKLie →ₗ[ℝ] ℝ where
  toFun Y := bE7Raw X Y
  map_add' Y₁ Y₂ := by
    simp only [bE7Raw, h3tkk_add_neg, h3tkk_add_zero, h3tkk_add_pos, tkk5StrDerivPart_add,
      strDerivPart_coe_add, mul_add, map_add, H3Zorn.traceBilin_add_right]
    ring
  map_smul' r Y := by
    simp only [bE7Raw, h3tkk_smul_neg, h3tkk_smul_zero, h3tkk_smul_pos, tkk5StrDerivPart_smul,
      strDerivPart_coe_smul, mul_smul_comm, map_smul, H3Zorn.traceBilin_smul_right,
      RingHom.id_apply, smul_eq_mul]
    ring

def B_E7 : LinearMap.BilinForm ℝ H3ZornTKKLie where
  toFun := bE7Right
  map_add' X₁ X₂ := by
    apply LinearMap.ext; intro Y
    change bE7Raw (X₁ + X₂) Y = bE7Raw X₁ Y + bE7Raw X₂ Y
    simp only [bE7Raw, h3tkk_add_neg, h3tkk_add_zero, h3tkk_add_pos, tkk5StrDerivPart_add,
      strDerivPart_coe_add, add_mul, map_add, H3Zorn.traceBilin_add_left]
    ring
  map_smul' r X := by
    apply LinearMap.ext; intro Y
    change bE7Raw (r • X) Y = r * bE7Raw X Y
    simp only [bE7Raw, h3tkk_smul_neg, h3tkk_smul_zero, h3tkk_smul_pos, tkk5StrDerivPart_smul,
      strDerivPart_coe_smul, smul_mul_assoc, map_smul, H3Zorn.traceBilin_smul_left,
      smul_eq_mul]
    ring

theorem B_E7_apply (X Y : H3ZornTKKLie) : B_E7 X Y = bE7Raw X Y := rfl

theorem B_E7_symm (X Y : H3ZornTKKLie) : B_E7 X Y = B_E7 Y X := by
  simp only [B_E7_apply, bE7Raw, LinearMap.trace_mul_comm,
    H3Zorn.traceBilin_symm (tkk5StrLmulPart X.zero) (tkk5StrLmulPart Y.zero),
    H3Zorn.traceBilin_symm X.neg Y.pos, H3Zorn.traceBilin_symm X.pos Y.neg]
  ring

theorem B_E7_θE7 (X Y : H3ZornTKKLie) : B_E7 (θE7 X) (θE7 Y) = B_E7 X Y := by
  simp only [B_E7_apply, bE7Raw, θE7_neg, θE7_pos]
  have hD : ∀ Z : H3ZornTKKLie,
      (tkk5StrDerivPart (θE7 Z).zero).1 = σConjEnd (tkk5StrDerivPart Z.zero).1 := fun Z => by
    have h := congrArg Subtype.val (strDerivPart_θE7 Z.zero)
    exact h
  have ha : ∀ Z : H3ZornTKKLie, tkk5StrLmulPart (θE7 Z).zero = -σH3 (tkk5StrLmulPart Z.zero) :=
    fun Z => strLmulPart_θE7 Z.zero
  rw [hD X, hD Y, ha X, ha Y]
  have htr : LinearMap.trace ℝ (H3Zorn ℝ)
      (σConjEnd (tkk5StrDerivPart X.zero).1 * σConjEnd (tkk5StrDerivPart Y.zero).1) =
      LinearMap.trace ℝ (H3Zorn ℝ) ((tkk5StrDerivPart X.zero).1 * (tkk5StrDerivPart Y.zero).1) := by
    change LinearMap.trace ℝ (H3Zorn ℝ)
      (σConjEnd (tkk5StrDerivPart X.zero).1 ∘ₗ σConjEnd (tkk5StrDerivPart Y.zero).1) = _
    rw [← σConjEnd_comp]
    change LinearMap.trace ℝ (H3Zorn ℝ)
      (σH3.toLinearMap * ((tkk5StrDerivPart X.zero).1 * (tkk5StrDerivPart Y.zero).1) * σH3.symm.toLinearMap) = _
    exact LinearMap.trace_conj' _ σH3
  rw [htr]
  simp only [h3_traceBilin_neg_left, h3_traceBilin_neg_right, neg_neg, σH3_traceBilin]
  ring

/-- Exact ad-invariant symmetric bilinear form `B₅` on the 248-dimensional 5-graded
`FreudenthalTKK5E8` (`weights (1, 12, -6, 6)`):
`B₅ U V = B_E7 U₀ V₀ + 12 U_c V_c + 6 (⟨U₋₁, V₊₁⟩ - ⟨U₊₁, V₋₁⟩) + 6 (U₋₂ V₊₂ + U₊₂ V₋₂)`. -/
private def b5Raw (U V : FreudenthalTKK5E8) : ℝ :=
  B_E7 U.gZeroE7 V.gZeroE7 +
    12 * (U.gZeroCenter * V.gZeroCenter) +
    6 * (symplecticForm U.gMinus1 V.gPlus1 - symplecticForm U.gPlus1 V.gMinus1) +
    6 * (U.gMinus2 * V.gPlus2 + U.gPlus2 * V.gMinus2)

private def b5Right (U : FreudenthalTKK5E8) : FreudenthalTKK5E8 →ₗ[ℝ] ℝ where
  toFun V := b5Raw U V
  map_add' V₁ V₂ := by
    simp only [b5Raw, add_gMinus2, add_gMinus1, add_gZeroE7, add_gZeroCenter, add_gPlus1,
      add_gPlus2, map_add, symp_add_right]
    ring
  map_smul' r V := by
    simp only [b5Raw, smul_gMinus2, smul_gMinus1, smul_gZeroE7, smul_gZeroCenter, smul_gPlus1,
      smul_gPlus2, map_smul, RingHom.id_apply, smul_eq_mul, symp_smul_right]
    ring

def B₅ : LinearMap.BilinForm ℝ FreudenthalTKK5E8 where
  toFun := b5Right
  map_add' U₁ U₂ := by
    apply LinearMap.ext; intro V
    change b5Raw (U₁ + U₂) V = b5Raw U₁ V + b5Raw U₂ V
    simp only [b5Raw, add_gMinus2, add_gMinus1, add_gZeroE7, add_gZeroCenter, add_gPlus1,
      add_gPlus2, map_add, LinearMap.add_apply, symp_add_left]
    ring
  map_smul' r U := by
    apply LinearMap.ext; intro V
    change b5Raw (r • U) V = r * b5Raw U V
    simp only [b5Raw, smul_gMinus2, smul_gMinus1, smul_gZeroE7, smul_gZeroCenter, smul_gPlus1,
      smul_gPlus2, map_smul, LinearMap.smul_apply, smul_eq_mul, symp_smul_left]
    ring

theorem B₅_apply (U V : FreudenthalTKK5E8) : B₅ U V = b5Raw U V := rfl

theorem B₅_symm (U V : FreudenthalTKK5E8) : B₅ U V = B₅ V U := by
  simp only [B₅_apply, b5Raw, B_E7_symm U.gZeroE7 V.gZeroE7,
    symplecticForm_skew U.gMinus1 V.gPlus1, symplecticForm_skew U.gPlus1 V.gMinus1]
  ring

theorem B₅_isSymm : B₅.IsSymm := ⟨B₅_symm⟩

theorem B₅_θ₅ (U V : FreudenthalTKK5E8) : B₅ (θ₅ U) (θ₅ V) = B₅ U V := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [B₅_apply, b5Raw, θ₅_gMinus2, θ₅_gMinus1, θ₅_gZeroE7, θ₅_gZeroCenter,
    θ₅_gPlus1, θ₅_gPlus2, B_E7_θE7, symp_smul_left, symp_smul_right,
    symplecticForm_σC, mul_neg, neg_mul]
  have h1 : Real.sqrt 2 * (Real.sqrt 2 * (1 / 2 * symplecticForm U.gPlus1 V.gMinus1)) =
      symplecticForm U.gPlus1 V.gMinus1 := by
    rw [← mul_assoc, ← mul_assoc, hs2]; ring
  have h2 : Real.sqrt 2 * (Real.sqrt 2 * (1 / 2 * symplecticForm U.gMinus1 V.gPlus1)) =
      symplecticForm U.gMinus1 V.gPlus1 := by
    rw [← mul_assoc, ← mul_assoc, hs2]; ring
  rw [h1, h2]
  ring

/-- The positive-definite Cartan inner product `⟨U, V⟩_θ₅ = -B₅(U, θ₅ V)` on `FreudenthalTKK5E8`. -/
def cartanInner5 : LinearMap.BilinForm ℝ FreudenthalTKK5E8 where
  toFun U :=
    { toFun := fun V => -B₅ U (θ₅ V)
      map_add' V₁ V₂ := by rw [map_add, map_add, neg_add]
      map_smul' r V := by
        rw [map_smul, map_smul, RingHom.id_apply, smul_eq_mul, smul_eq_mul, mul_neg] }
  map_add' U₁ U₂ := by
    apply LinearMap.ext; intro V
    change -B₅ (U₁ + U₂) (θ₅ V) = -B₅ U₁ (θ₅ V) + -B₅ U₂ (θ₅ V)
    rw [map_add, LinearMap.add_apply, neg_add]
  map_smul' r U := by
    apply LinearMap.ext; intro V
    change -B₅ (r • U) (θ₅ V) = r * (-B₅ U (θ₅ V))
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem cartanInner5_apply (U V : FreudenthalTKK5E8) :
    cartanInner5 U V = -B₅ U (θ₅ V) := rfl

theorem cartanInner5_symm (U V : FreudenthalTKK5E8) :
    cartanInner5 U V = cartanInner5 V U := by
  rw [cartanInner5_apply, cartanInner5_apply, B₅_symm, ← B₅_θ₅ (θ₅ V) U, θ₅_involutive]

theorem cartanInner5_isSymm : cartanInner5.IsSymm := ⟨cartanInner5_symm⟩

/-! ### Part 6B: Operator Trace Identities, Ad-Invariance of `B₅`, and Positive Definiteness -/

private theorem zornBilin_sigma_zorn_basis_eq (X : ZornVectorMatrix ℝ) (j : Fin 8) :
    zornBilin X (σZorn (zorn_basis j)) =
      match j.val with
      | 0 => X.a
      | 1 => X.v 0
      | 2 => X.v 1
      | 3 => X.v 2
      | 4 => X.w 0
      | 5 => X.w 1
      | 6 => X.w 2
      | _ => X.b := by
  fin_cases j <;>
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
      ZornVectorMatrix.trace, ZornVec3.dot]

private theorem zornBilin_zorn_basis_sigma (i j : Fin 8) :
    zornBilin (zorn_basis i) (σZorn (zorn_basis j)) = if i = j then 1 else 0 := by
  rw [zornBilin_sigma_zorn_basis_eq]
  fin_cases i <;> fin_cases j <;> simp [zorn_basis]

private theorem zornBilin_sigma_basis_inner_sum (X Y : ZornVectorMatrix ℝ) :
    ∑ m : Fin 8, zornBilin X (σZorn (zorn_basis m)) * zornBilin (zorn_basis m) Y =
      zornBilin X Y := by
  rw [Fin.sum_univ_eight]
  simp only [zornBilin_sigma_zorn_basis_eq]
  have h0 : zornBilin (zorn_basis 0) Y = Y.b := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  have h1 : zornBilin (zorn_basis 1) Y = -Y.w 0 := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  have h2 : zornBilin (zorn_basis 2) Y = -Y.w 1 := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  have h3 : zornBilin (zorn_basis 3) Y = -Y.w 2 := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  have h4 : zornBilin (zorn_basis 4) Y = -Y.v 0 := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  have h5 : zornBilin (zorn_basis 5) Y = -Y.v 1 := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  have h6 : zornBilin (zorn_basis 6) Y = -Y.v 2 := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  have h7 : zornBilin (zorn_basis 7) Y = Y.a := by
    simp [zorn_basis, zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, h0, h1, h2, h3, h4, h5, h6, h7]
  simp [zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace,
    ZornVec3.dot_eq_sum_coords]
  ring

private theorem zornBilin_conj_conj (X Y : ZornVectorMatrix ℝ) :
    zornBilin (ZornVectorMatrix.conj X) (ZornVectorMatrix.conj Y) = zornBilin X Y := by
  simp [zornBilin, ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace, ZornVec3.dot]
  ring

private theorem zornBilin_conj_mul_left_sigma_sum (X Y : ZornVectorMatrix ℝ) :
    ∑ m : Fin 8,
      zornBilin (ZornVectorMatrix.mul X (σZorn (zorn_basis m)))
        (ZornVectorMatrix.mul Y (zorn_basis m)) = 4 * zornBilin X Y := by
  rw [Fin.sum_univ_eight]
  simp only [zorn_basis, σZorn, LinearEquiv.coe_mk, ZornVectorMatrix.mul, ZornVec3.dot,
    ZornVec3.cross, zornBilin, ZornVectorMatrix.conj, ZornVectorMatrix.trace,
    Fin.sum_univ_three]
  norm_num
  ring

private theorem zornBilin_mul_right_sigma_sum (X Y : ZornVectorMatrix ℝ) :
    ∑ m : Fin 8,
      zornBilin (ZornVectorMatrix.mul (σZorn (zorn_basis m)) X)
        (ZornVectorMatrix.mul (zorn_basis m) Y) = 4 * zornBilin X Y := by
  rw [Fin.sum_univ_eight]
  simp only [zorn_basis, σZorn, LinearEquiv.coe_mk, ZornVectorMatrix.mul, ZornVec3.dot,
    ZornVec3.cross, zornBilin, ZornVectorMatrix.conj, ZornVectorMatrix.trace,
    Fin.sum_univ_three]
  norm_num
  ring

private theorem sectorOfFin_finOfSector (s : H3Sector) : sectorOfFin (finOfSector s) = s := by
  cases s with
  | diag d => fin_cases d <;> rfl
  | j12 m => fin_cases m <;> rfl
  | j23 m => fin_cases m <;> rfl
  | j31 m => fin_cases m <;> rfl

private theorem finOfSector_injective : Function.Injective finOfSector := by
  intro s₁ s₂ h
  have := congrArg sectorOfFin h
  rwa [sectorOfFin_finOfSector, sectorOfFin_finOfSector] at this

private theorem traceBilin_h3ZornBasis_σ (i j : Fin 27) :
    H3Zorn.traceBilin (σH3 (h3ZornBasis i)) (h3ZornBasis j) = if i = j then 1 else 0 := by
  rw [H3Zorn.traceBilin_symm]
  have hi := finOfSector_sectorOfFin i
  have hj := finOfSector_sectorOfFin j
  rw [← hi, ← hj]
  simp only [finOfSector_injective.eq_iff]
  have hzb_eq : ∀ x y : H3Zorn ℝ, H3Zorn.traceBilin x y =
      x.α₁ * y.α₁ + x.α₂ * y.α₂ + x.α₃ * y.α₃ +
        zornBilin x.a y.a + zornBilin x.b y.b + zornBilin x.c y.c := fun _ _ => rfl
  have hσ0' : σZorn ZornVectorMatrix.zero = ZornVectorMatrix.zero := σZorn_zero
  have hzl (u : ZornVectorMatrix ℝ) : zornBilin ZornVectorMatrix.zero u = 0 := by
    rw [zornBilin]
    exact show ZornVectorMatrix.trace (ZornVectorMatrix.mul ZornVectorMatrix.zero (ZornVectorMatrix.conj u)) = 0 by
      rw [ZornVectorMatrix.zero_mul]; simp [ZornVectorMatrix.trace, ZornVectorMatrix.zero]
  have hzr (u : ZornVectorMatrix ℝ) : zornBilin u ZornVectorMatrix.zero = 0 := by
    rw [zornBilin]
    exact show ZornVectorMatrix.trace (ZornVectorMatrix.mul u (ZornVectorMatrix.conj ZornVectorMatrix.zero)) = 0 by
      rw [ZornVectorMatrix.conj_zero, ZornVectorMatrix.mul_zero]; simp [ZornVectorMatrix.trace, ZornVectorMatrix.zero]
  cases sectorOfFin i with
  | diag d₁ =>
    cases sectorOfFin j with
    | diag d₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      fin_cases d₁ <;> fin_cases d₂ <;>
        simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, h3_diag₁, h3_diag₂, h3_diag₃,
          hσ0', hzl]
    | j12 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      fin_cases d₁ <;>
        simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, h3_diag₁, h3_diag₂, h3_diag₃,
          embedJ12, hσ0', hzl, hzr]
    | j23 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      fin_cases d₁ <;>
        simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, h3_diag₁, h3_diag₂, h3_diag₃,
          embedJ23, hσ0', hzl, hzr]
    | j31 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      fin_cases d₁ <;>
        simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, h3_diag₁, h3_diag₂, h3_diag₃,
          embedJ31, hσ0', hzl, hzr]
  | j12 m₁ =>
    cases sectorOfFin j with
    | diag d₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      fin_cases d₂ <;>
        simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, h3_diag₁, h3_diag₂, h3_diag₃,
          embedJ12, hσ0', hzl]
    | j12 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [embedJ12, σH3_b, σH3_c, σH3_a, σH3_α₁, σH3_α₂, σH3_α₃, hσ0', hzl]
      rw [zornBilin_zorn_basis_sigma]
      have hiff : m₂ = m₁ ↔ H3Sector.j12 m₁ = H3Sector.j12 m₂ :=
        ⟨fun h => by subst h; rfl, fun h => by cases h; rfl⟩
      simp [hiff]
    | j23 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, embedJ12, embedJ23, hσ0', hzl, hzr]
    | j31 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, embedJ12, embedJ31, hσ0', hzl, hzr]
  | j23 m₁ =>
    cases sectorOfFin j with
    | diag d₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      fin_cases d₂ <;>
        simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, h3_diag₁, h3_diag₂, h3_diag₃,
          embedJ23, hσ0', hzl]
    | j12 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, embedJ23, embedJ12, hσ0', hzl, hzr]
    | j23 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [embedJ23, σH3_b, σH3_c, σH3_a, σH3_α₁, σH3_α₂, σH3_α₃, hσ0', hzl]
      rw [zornBilin_zorn_basis_sigma]
      have hiff : m₂ = m₁ ↔ H3Sector.j23 m₁ = H3Sector.j23 m₂ :=
        ⟨fun h => by subst h; rfl, fun h => by cases h; rfl⟩
      simp [hiff]
    | j31 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, embedJ23, embedJ31, hσ0', hzl, hzr]
  | j31 m₁ =>
    cases sectorOfFin j with
    | diag d₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      fin_cases d₂ <;>
        simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, h3_diag₁, h3_diag₂, h3_diag₃,
          embedJ31, hσ0', hzl]
    | j12 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, embedJ31, embedJ12, hσ0', hzl, hzr]
    | j23 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [σH3_α₁, σH3_α₂, σH3_α₃, σH3_a, σH3_b, σH3_c, embedJ31, embedJ23, hσ0', hzl, hzr]
    | j31 m₂ =>
      rw [h3ZornBasis_sector, h3ZornBasis_sector, hzb_eq]
      simp [embedJ31, σH3_b, σH3_c, σH3_a, σH3_α₁, σH3_α₂, σH3_α₃, hσ0', hzl]
      rw [zornBilin_zorn_basis_sigma]
      have hiff : m₂ = m₁ ↔ H3Sector.j31 m₁ = H3Sector.j31 m₂ :=
        ⟨fun h => by subst h; rfl, fun h => by cases h; rfl⟩
      simp [hiff]

private theorem h3ZornBasis_repr_eq_traceBilin_σ (x : H3Zorn ℝ) (i : Fin 27) :
    h3ZornBasis.repr x i = H3Zorn.traceBilin (σH3 (h3ZornBasis i)) x := by
  have hsum : ∀ (u : H3Zorn ℝ) (f : Fin 27 → H3Zorn ℝ),
      H3Zorn.traceBilin u (∑ j, f j) = ∑ j, H3Zorn.traceBilin u (f j) := by
    intro u f
    induction (Finset.univ : Finset (Fin 27)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change H3Zorn.traceBilin u 0 = 0
      exact H3Zorn.traceBilin_zero_right u
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, H3Zorn.traceBilin_add_right, ih]
  conv_rhs => rw [← h3ZornBasis.sum_repr x]
  rw [hsum]
  simp only [H3Zorn.traceBilin_smul_right, traceBilin_h3ZornBasis_σ,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem trace_h3zorn_eq_sum_σ (T : Module.End ℝ (H3Zorn ℝ)) :
    LinearMap.trace ℝ (H3Zorn ℝ) T =
      ∑ i : Fin 27, H3Zorn.traceBilin (σH3 (h3ZornBasis i)) (T (h3ZornBasis i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ h3ZornBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    h3ZornBasis_repr_eq_traceBilin_σ]

private theorem h3SectorEquiv_sum (f : Fin 27 → ℝ) :
    (∑ i : Fin 27, f i) =
      (f (finOfSector (.diag 0)) + f (finOfSector (.diag 1)) + f (finOfSector (.diag 2))) +
        (∑ m : Fin 8, f (finOfSector (.j12 m))) +
        (∑ m : Fin 8, f (finOfSector (.j23 m))) +
        (∑ m : Fin 8, f (finOfSector (.j31 m))) := by
  let e : Fin 3 ⊕ Fin 8 ⊕ Fin 8 ⊕ Fin 8 ≃ Fin 27 :=
    { toFun := fun s => match s with
        | .inl d => finOfSector (.diag d)
        | .inr (.inl m) => finOfSector (.j12 m)
        | .inr (.inr (.inl m)) => finOfSector (.j23 m)
        | .inr (.inr (.inr m)) => finOfSector (.j31 m)
      invFun := fun p => match sectorOfFin p with
        | .diag d => .inl d
        | .j12 m => .inr (.inl m)
        | .j23 m => .inr (.inr (.inl m))
        | .j31 m => .inr (.inr (.inr m))
      left_inv := by
        rintro (d | m | m | m)
        · fin_cases d <;> rfl
        · fin_cases m <;> rfl
        · fin_cases m <;> rfl
        · fin_cases m <;> rfl
      right_inv := by
        intro p
        fin_cases p <;> rfl }
  rw [← Equiv.sum_comp e f]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, e, Equiv.coe_fn_mk]
  ring

private theorem h3Zorn_decomp_inline (x : H3Zorn ℝ) :
    x = x.α₁ • h3_diag₁ + x.α₂ • h3_diag₂ + x.α₃ • h3_diag₃ +
      embedJ12 x.a + embedJ23 x.b + embedJ31 x.c := by
  apply H3Zorn.ext_h3 <;> simp [h3_diag₁, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31,
    H3Zorn.add_readback, H3Zorn.smul_readback, ZornVectorMatrix.smul_zero]

private theorem traceBilin_h3_mul_diag₁ (a b : H3Zorn ℝ) :
    H3Zorn.traceBilin (a * h3_diag₁) (b * h3_diag₁) =
      a.α₁ * b.α₁ + (1 / 4 : ℝ) * zornBilin a.a b.a + (1 / 4 : ℝ) * zornBilin a.c b.c := by
  have hmul (x : H3Zorn ℝ) : x * h3_diag₁ =
      ⟨x.α₁, 0, 0, (1 / 2 : ℝ) • x.a, 0, (1 / 2 : ℝ) • x.c⟩ := by
    have h0 : x * h3_diag₁ =
        x.α₁ • h3_diag₁ + (1 / 2 : ℝ) • embedJ12 x.a + (1 / 2 : ℝ) • embedJ31 x.c := by
      nth_rw 1 [h3Zorn_decomp_inline x]
      simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_h3_diag₁,
        mul_comm h3_diag₂ h3_diag₁, h3_diag₁_mul_h3_diag₂,
        mul_comm h3_diag₃ h3_diag₁, h3_diag₁_mul_h3_diag₃,
        mul_comm (embedJ12 _), mul_comm (embedJ23 _), mul_comm (embedJ31 _),
        h3_diag₁_mul_embedJ12, h3_diag₁_mul_embedJ23, h3_diag₁_mul_embedJ31, smul_zero, add_zero]
    rw [h0]
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, embedJ12, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, embedJ12, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, embedJ12, embedJ31]
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, embedJ12, embedJ31]
      change ((x.α₁ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • x.a) + (1 / 2 : ℝ) • 0) = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, embedJ12, embedJ31]
      change ((x.α₁ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • 0) = 0
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, embedJ12, embedJ31]
      change ((x.α₁ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • x.c) = (1 / 2 : ℝ) • x.c
      simp
  rw [hmul a, hmul b]
  have hz : zornBilin (0 : ZornVectorMatrix ℝ) 0 = 0 := by
    simp [zornBilin, ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace]
  change a.α₁ * b.α₁ + 0 * 0 + 0 * 0 +
      zornBilin ((1 / 2 : ℝ) • a.a) ((1 / 2 : ℝ) • b.a) + zornBilin 0 0 +
      zornBilin ((1 / 2 : ℝ) • a.c) ((1 / 2 : ℝ) • b.c) = _
  rw [hz, zornBilin_smul_left, zornBilin_smul_right, zornBilin_smul_left, zornBilin_smul_right]
  ring

private theorem traceBilin_h3_mul_diag₂ (a b : H3Zorn ℝ) :
    H3Zorn.traceBilin (a * h3_diag₂) (b * h3_diag₂) =
      a.α₂ * b.α₂ + (1 / 4 : ℝ) * zornBilin a.a b.a + (1 / 4 : ℝ) * zornBilin a.b b.b := by
  have hmul (x : H3Zorn ℝ) : x * h3_diag₂ =
      ⟨0, x.α₂, 0, (1 / 2 : ℝ) • x.a, (1 / 2 : ℝ) • x.b, 0⟩ := by
    have h0 : x * h3_diag₂ =
        x.α₂ • h3_diag₂ + (1 / 2 : ℝ) • embedJ12 x.a + (1 / 2 : ℝ) • embedJ23 x.b := by
      nth_rw 1 [h3Zorn_decomp_inline x]
      simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_h3_diag₂, h3_diag₂_mul_h3_diag₂,
        mul_comm h3_diag₃ h3_diag₂, h3_diag₂_mul_h3_diag₃,
        mul_comm (embedJ12 _), mul_comm (embedJ23 _), mul_comm (embedJ31 _),
        h3_diag₂_mul_embedJ12, h3_diag₂_mul_embedJ23, h3_diag₂_mul_embedJ31,
        smul_zero, add_zero, zero_add]
    rw [h0]
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, embedJ12, embedJ23]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, embedJ12, embedJ23]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, embedJ12, embedJ23]
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, embedJ12, embedJ23]
      change ((x.α₂ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • x.a) + (1 / 2 : ℝ) • 0) = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, embedJ12, embedJ23]
      change ((x.α₂ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • x.b) = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, embedJ12, embedJ23]
      change ((x.α₂ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • 0) = 0
      simp
  rw [hmul a, hmul b]
  have hz : zornBilin (0 : ZornVectorMatrix ℝ) 0 = 0 := by
    simp [zornBilin, ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace]
  change 0 * 0 + a.α₂ * b.α₂ + 0 * 0 +
      zornBilin ((1 / 2 : ℝ) • a.a) ((1 / 2 : ℝ) • b.a) +
      zornBilin ((1 / 2 : ℝ) • a.b) ((1 / 2 : ℝ) • b.b) + zornBilin 0 0 = _
  rw [hz, zornBilin_smul_left, zornBilin_smul_right, zornBilin_smul_left, zornBilin_smul_right]
  ring

private theorem traceBilin_h3_mul_diag₃ (a b : H3Zorn ℝ) :
    H3Zorn.traceBilin (a * h3_diag₃) (b * h3_diag₃) =
      a.α₃ * b.α₃ + (1 / 4 : ℝ) * zornBilin a.b b.b + (1 / 4 : ℝ) * zornBilin a.c b.c := by
  have hmul (x : H3Zorn ℝ) : x * h3_diag₃ =
      ⟨0, 0, x.α₃, 0, (1 / 2 : ℝ) • x.b, (1 / 2 : ℝ) • x.c⟩ := by
    have h0 : x * h3_diag₃ =
        x.α₃ • h3_diag₃ + (1 / 2 : ℝ) • embedJ23 x.b + (1 / 2 : ℝ) • embedJ31 x.c := by
      nth_rw 1 [h3Zorn_decomp_inline x]
      simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_h3_diag₃, h3_diag₂_mul_h3_diag₃,
        h3_diag₃_mul_h3_diag₃, mul_comm (embedJ12 _), mul_comm (embedJ23 _), mul_comm (embedJ31 _),
        h3_diag₃_mul_embedJ12, h3_diag₃_mul_embedJ23, h3_diag₃_mul_embedJ31,
        smul_zero, add_zero, zero_add]
    rw [h0]
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₃, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₃, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₃, embedJ23, embedJ31]
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₃, embedJ23, embedJ31]
      change ((x.α₃ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • 0) = 0
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₃, embedJ23, embedJ31]
      change ((x.α₃ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • x.b) + (1 / 2 : ℝ) • 0) = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₃, embedJ23, embedJ31]
      change ((x.α₃ • (0 : ZornVectorMatrix ℝ) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • x.c) = _
      simp
  rw [hmul a, hmul b]
  have hz : zornBilin (0 : ZornVectorMatrix ℝ) 0 = 0 := by
    simp [zornBilin, ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace]
  change 0 * 0 + 0 * 0 + a.α₃ * b.α₃ + zornBilin 0 0 +
      zornBilin ((1 / 2 : ℝ) • a.b) ((1 / 2 : ℝ) • b.b) +
      zornBilin ((1 / 2 : ℝ) • a.c) ((1 / 2 : ℝ) • b.c) = _
  rw [hz, zornBilin_smul_left, zornBilin_smul_right, zornBilin_smul_left, zornBilin_smul_right]
  ring

private theorem traceBilin_h3_mul_j12_sum (a b : H3Zorn ℝ) :
    ∑ m : Fin 8, H3Zorn.traceBilin (a * embedJ12 (σZorn (zorn_basis m))) (b * embedJ12 (zorn_basis m)) =
      2 * (a.α₁ + a.α₂) * (b.α₁ + b.α₂) + (1 / 2 : ℝ) * zornBilin a.a b.a +
        zornBilin a.b b.b + zornBilin a.c b.c := by
  have hmul (x : H3Zorn ℝ) (u : ZornVectorMatrix ℝ) :
      x * embedJ12 u =
        ⟨(1 / 2 : ℝ) * zornBilin x.a u, (1 / 2 : ℝ) * zornBilin x.a u, 0,
         ((1 / 2 : ℝ) * (x.α₁ + x.α₂)) • u,
         (1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj u) (ZornVectorMatrix.conj x.c),
         (1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj x.b) (ZornVectorMatrix.conj u)⟩ := by
    have h0 : x * embedJ12 u =
        ((1 / 2 : ℝ) * zornBilin x.a u) • (h3_diag₁ + h3_diag₂) +
        ((1 / 2 : ℝ) * (x.α₁ + x.α₂)) • embedJ12 u +
        (1 / 2 : ℝ) • embedJ31 (ZornVectorMatrix.mul (ZornVectorMatrix.conj x.b) (ZornVectorMatrix.conj u)) +
        (1 / 2 : ℝ) • embedJ23 (ZornVectorMatrix.mul (ZornVectorMatrix.conj u) (ZornVectorMatrix.conj x.c)) := by
      nth_rw 1 [h3Zorn_decomp_inline x]
      simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12,
        h3_diag₃_mul_embedJ12, embedJ12_mul_embedJ12,
        mul_comm (embedJ23 _), embedJ12_mul_embedJ23, embedJ31_mul_embedJ12,
        smul_zero, add_zero]
      module
    rw [h0]
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₂, embedJ12, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₂, embedJ12, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₂, embedJ12, embedJ23, embedJ31]
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₂, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.a u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₁ + x.α₂)) • u) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • 0 = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₂, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.a u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₁ + x.α₂)) • 0) + (1 / 2 : ℝ) • 0) +
          (1 / 2 : ℝ) • (u.conj.mul x.c.conj) = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₂, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.a u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₁ + x.α₂)) • 0) + (1 / 2 : ℝ) • (x.b.conj.mul u.conj)) +
          (1 / 2 : ℝ) • 0 = _
      simp
  have hterm (m : Fin 8) :
      H3Zorn.traceBilin (a * embedJ12 (σZorn (zorn_basis m))) (b * embedJ12 (zorn_basis m)) =
        (1 / 2 : ℝ) * zornBilin a.a (σZorn (zorn_basis m)) * zornBilin (zorn_basis m) b.a +
        (1 / 4 : ℝ) * (a.α₁ + a.α₂) * (b.α₁ + b.α₂) * zornBilin (σZorn (zorn_basis m)) (zorn_basis m) +
        (1 / 4 : ℝ) * zornBilin
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m))) (ZornVectorMatrix.conj a.c))
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m)) (ZornVectorMatrix.conj b.c)) +
        (1 / 4 : ℝ) * zornBilin
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj a.b) (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj b.b) (ZornVectorMatrix.conj (zorn_basis m))) := by
    rw [hmul a (σZorn (zorn_basis m)), hmul b (zorn_basis m)]
    change ((1 / 2 : ℝ) * zornBilin a.a (σZorn (zorn_basis m))) * ((1 / 2 : ℝ) * zornBilin b.a (zorn_basis m)) +
        ((1 / 2 : ℝ) * zornBilin a.a (σZorn (zorn_basis m))) * ((1 / 2 : ℝ) * zornBilin b.a (zorn_basis m)) +
        0 * 0 +
        zornBilin (((1 / 2 : ℝ) * (a.α₁ + a.α₂)) • σZorn (zorn_basis m))
          (((1 / 2 : ℝ) * (b.α₁ + b.α₂)) • zorn_basis m) +
        zornBilin ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m)))
            (ZornVectorMatrix.conj a.c))
          ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m))
            (ZornVectorMatrix.conj b.c)) +
        zornBilin ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj a.b)
            (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
          ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj b.b)
            (ZornVectorMatrix.conj (zorn_basis m))) = _
    simp only [zornBilin_smul_left, zornBilin_smul_right]
    rw [zornBilin_symm b.a (zorn_basis m)]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have h1 : ∑ m : Fin 8, zornBilin a.a (σZorn (zorn_basis m)) * zornBilin (zorn_basis m) b.a =
      zornBilin a.a b.a := zornBilin_sigma_basis_inner_sum a.a b.a
  have h2 : ∑ m : Fin 8, zornBilin (σZorn (zorn_basis m)) (zorn_basis m) = 8 := by
    simp_rw [← zornBilin_σZorn_right, zornBilin_zorn_basis_sigma]
    simp
  have h3 : ∑ m : Fin 8, zornBilin
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m))) (ZornVectorMatrix.conj a.c))
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m)) (ZornVectorMatrix.conj b.c)) =
      4 * zornBilin a.c b.c := by
    have hs := zornBilin_conj_mul_left_sigma_sum a.c b.c
    rw [← hs]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ZornVectorMatrix.conj_mul a.c (σZorn (zorn_basis m)),
      ← ZornVectorMatrix.conj_mul b.c (zorn_basis m), zornBilin_conj_conj]
  have h4 : ∑ m : Fin 8, zornBilin
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj a.b) (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj b.b) (ZornVectorMatrix.conj (zorn_basis m))) =
      4 * zornBilin a.b b.b := by
    have hs := zornBilin_mul_right_sigma_sum a.b b.b
    rw [← hs]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ZornVectorMatrix.conj_mul (σZorn (zorn_basis m)) a.b,
      ← ZornVectorMatrix.conj_mul (zorn_basis m) b.b, zornBilin_conj_conj]
  have h1' : ∑ x : Fin 8, zornBilin a.a (σZorn (zorn_basis x)) * zornBilin (zorn_basis x) b.a =
      zornBilin a.a b.a := h1
  rw [h1', h2, h3, h4]
  ring

private theorem traceBilin_h3_mul_j23_sum (a b : H3Zorn ℝ) :
    ∑ m : Fin 8, H3Zorn.traceBilin (a * embedJ23 (σZorn (zorn_basis m))) (b * embedJ23 (zorn_basis m)) =
      2 * (a.α₂ + a.α₃) * (b.α₂ + b.α₃) + (1 / 2 : ℝ) * zornBilin a.b b.b +
        zornBilin a.c b.c + zornBilin a.a b.a := by
  have hmul (x : H3Zorn ℝ) (u : ZornVectorMatrix ℝ) :
      x * embedJ23 u =
        ⟨0, (1 / 2 : ℝ) * zornBilin x.b u, (1 / 2 : ℝ) * zornBilin x.b u,
         (1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj x.c) (ZornVectorMatrix.conj u),
         ((1 / 2 : ℝ) * (x.α₂ + x.α₃)) • u,
         (1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj u) (ZornVectorMatrix.conj x.a)⟩ := by
    have h0 : x * embedJ23 u =
        ((1 / 2 : ℝ) * zornBilin x.b u) • (h3_diag₂ + h3_diag₃) +
        ((1 / 2 : ℝ) * (x.α₂ + x.α₃)) • embedJ23 u +
        (1 / 2 : ℝ) • embedJ12 (ZornVectorMatrix.mul (ZornVectorMatrix.conj x.c) (ZornVectorMatrix.conj u)) +
        (1 / 2 : ℝ) • embedJ31 (ZornVectorMatrix.mul (ZornVectorMatrix.conj u) (ZornVectorMatrix.conj x.a)) := by
      nth_rw 1 [h3Zorn_decomp_inline x]
      simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_embedJ23, h3_diag₂_mul_embedJ23,
        h3_diag₃_mul_embedJ23, embedJ23_mul_embedJ23,
        mul_comm (embedJ31 _), embedJ23_mul_embedJ31, embedJ12_mul_embedJ23,
        smul_zero, zero_add]
      module
    rw [h0]
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31]
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.b u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₂ + x.α₃)) • 0) + (1 / 2 : ℝ) • (x.c.conj.mul u.conj)) +
          (1 / 2 : ℝ) • 0 = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.b u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₂ + x.α₃)) • u) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • 0 = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₂, h3_diag₃, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.b u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₂ + x.α₃)) • 0) + (1 / 2 : ℝ) • 0) +
          (1 / 2 : ℝ) • (u.conj.mul x.a.conj) = _
      simp
  have hterm (m : Fin 8) :
      H3Zorn.traceBilin (a * embedJ23 (σZorn (zorn_basis m))) (b * embedJ23 (zorn_basis m)) =
        (1 / 2 : ℝ) * zornBilin a.b (σZorn (zorn_basis m)) * zornBilin (zorn_basis m) b.b +
        (1 / 4 : ℝ) * (a.α₂ + a.α₃) * (b.α₂ + b.α₃) * zornBilin (σZorn (zorn_basis m)) (zorn_basis m) +
        (1 / 4 : ℝ) * zornBilin
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj a.c) (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj b.c) (ZornVectorMatrix.conj (zorn_basis m))) +
        (1 / 4 : ℝ) * zornBilin
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m))) (ZornVectorMatrix.conj a.a))
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m)) (ZornVectorMatrix.conj b.a)) := by
    rw [hmul a (σZorn (zorn_basis m)), hmul b (zorn_basis m)]
    change 0 * 0 +
        ((1 / 2 : ℝ) * zornBilin a.b (σZorn (zorn_basis m))) * ((1 / 2 : ℝ) * zornBilin b.b (zorn_basis m)) +
        ((1 / 2 : ℝ) * zornBilin a.b (σZorn (zorn_basis m))) * ((1 / 2 : ℝ) * zornBilin b.b (zorn_basis m)) +
        zornBilin ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj a.c)
            (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
          ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj b.c)
            (ZornVectorMatrix.conj (zorn_basis m))) +
        zornBilin (((1 / 2 : ℝ) * (a.α₂ + a.α₃)) • σZorn (zorn_basis m))
          (((1 / 2 : ℝ) * (b.α₂ + b.α₃)) • zorn_basis m) +
        zornBilin ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m)))
            (ZornVectorMatrix.conj a.a))
          ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m))
            (ZornVectorMatrix.conj b.a)) = _
    simp only [zornBilin_smul_left, zornBilin_smul_right]
    rw [zornBilin_symm b.b (zorn_basis m)]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have h1 := zornBilin_sigma_basis_inner_sum a.b b.b
  have h2 : ∑ m : Fin 8, zornBilin (σZorn (zorn_basis m)) (zorn_basis m) = 8 := by
    simp_rw [← zornBilin_σZorn_right, zornBilin_zorn_basis_sigma]
    simp
  have h3 : ∑ m : Fin 8, zornBilin
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj a.c) (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj b.c) (ZornVectorMatrix.conj (zorn_basis m))) =
      4 * zornBilin a.c b.c := by
    have hs := zornBilin_mul_right_sigma_sum a.c b.c
    rw [← hs]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ZornVectorMatrix.conj_mul (σZorn (zorn_basis m)) a.c,
      ← ZornVectorMatrix.conj_mul (zorn_basis m) b.c, zornBilin_conj_conj]
  have h4 : ∑ m : Fin 8, zornBilin
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m))) (ZornVectorMatrix.conj a.a))
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m)) (ZornVectorMatrix.conj b.a)) =
      4 * zornBilin a.a b.a := by
    have hs := zornBilin_conj_mul_left_sigma_sum a.a b.a
    rw [← hs]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ZornVectorMatrix.conj_mul a.a (σZorn (zorn_basis m)),
      ← ZornVectorMatrix.conj_mul b.a (zorn_basis m), zornBilin_conj_conj]
  have h1' : ∑ x : Fin 8, zornBilin a.b (σZorn (zorn_basis x)) * zornBilin (zorn_basis x) b.b =
      zornBilin a.b b.b := h1
  rw [h1', h2, h3, h4]
  ring

private theorem traceBilin_h3_mul_j31_sum (a b : H3Zorn ℝ) :
    ∑ m : Fin 8, H3Zorn.traceBilin (a * embedJ31 (σZorn (zorn_basis m))) (b * embedJ31 (zorn_basis m)) =
      2 * (a.α₃ + a.α₁) * (b.α₃ + b.α₁) + (1 / 2 : ℝ) * zornBilin a.c b.c +
        zornBilin a.a b.a + zornBilin a.b b.b := by
  have hmul (x : H3Zorn ℝ) (u : ZornVectorMatrix ℝ) :
      x * embedJ31 u =
        ⟨(1 / 2 : ℝ) * zornBilin x.c u, 0, (1 / 2 : ℝ) * zornBilin x.c u,
         (1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj u) (ZornVectorMatrix.conj x.b),
         (1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj x.a) (ZornVectorMatrix.conj u),
         ((1 / 2 : ℝ) * (x.α₃ + x.α₁)) • u⟩ := by
    have h0 : x * embedJ31 u =
        ((1 / 2 : ℝ) * zornBilin x.c u) • (h3_diag₃ + h3_diag₁) +
        ((1 / 2 : ℝ) * (x.α₃ + x.α₁)) • embedJ31 u +
        (1 / 2 : ℝ) • embedJ23 (ZornVectorMatrix.mul (ZornVectorMatrix.conj x.a) (ZornVectorMatrix.conj u)) +
        (1 / 2 : ℝ) • embedJ12 (ZornVectorMatrix.mul (ZornVectorMatrix.conj u) (ZornVectorMatrix.conj x.b)) := by
      nth_rw 1 [h3Zorn_decomp_inline x]
      simp only [add_mul, smul_mul_assoc, h3_diag₁_mul_embedJ31, h3_diag₂_mul_embedJ31,
        h3_diag₃_mul_embedJ31, embedJ31_mul_embedJ31,
        mul_comm (embedJ12 _), embedJ31_mul_embedJ12, embedJ23_mul_embedJ31,
        smul_zero, add_zero]
      module
    rw [h0]
    apply H3Zorn.ext_h3
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₃, embedJ12, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₃, embedJ12, embedJ23, embedJ31]
    · simp [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₃, embedJ12, embedJ23, embedJ31]
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₃, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.c u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₃ + x.α₁)) • 0) + (1 / 2 : ℝ) • 0) +
          (1 / 2 : ℝ) • (u.conj.mul x.b.conj) = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₃, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.c u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₃ + x.α₁)) • 0) + (1 / 2 : ℝ) • (x.a.conj.mul u.conj)) +
          (1 / 2 : ℝ) • 0 = _
      simp
    · simp only [H3Zorn.add_readback, H3Zorn.smul_readback, h3_diag₁, h3_diag₃, embedJ12, embedJ23, embedJ31]
      change (((1 / 2 * zornBilin x.c u) • ((0 : ZornVectorMatrix ℝ) + 0) +
          (1 / 2 * (x.α₃ + x.α₁)) • u) + (1 / 2 : ℝ) • 0) + (1 / 2 : ℝ) • 0 = _
      simp
  have hterm (m : Fin 8) :
      H3Zorn.traceBilin (a * embedJ31 (σZorn (zorn_basis m))) (b * embedJ31 (zorn_basis m)) =
        (1 / 2 : ℝ) * zornBilin a.c (σZorn (zorn_basis m)) * zornBilin (zorn_basis m) b.c +
        (1 / 4 : ℝ) * (a.α₃ + a.α₁) * (b.α₃ + b.α₁) * zornBilin (σZorn (zorn_basis m)) (zorn_basis m) +
        (1 / 4 : ℝ) * zornBilin
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m))) (ZornVectorMatrix.conj a.b))
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m)) (ZornVectorMatrix.conj b.b)) +
        (1 / 4 : ℝ) * zornBilin
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj a.a) (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj b.a) (ZornVectorMatrix.conj (zorn_basis m))) := by
    rw [hmul a (σZorn (zorn_basis m)), hmul b (zorn_basis m)]
    change ((1 / 2 : ℝ) * zornBilin a.c (σZorn (zorn_basis m))) * ((1 / 2 : ℝ) * zornBilin b.c (zorn_basis m)) +
        0 * 0 +
        ((1 / 2 : ℝ) * zornBilin a.c (σZorn (zorn_basis m))) * ((1 / 2 : ℝ) * zornBilin b.c (zorn_basis m)) +
        zornBilin ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m)))
            (ZornVectorMatrix.conj a.b))
          ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m))
            (ZornVectorMatrix.conj b.b)) +
        zornBilin ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj a.a)
            (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
          ((1 / 2 : ℝ) • ZornVectorMatrix.mul (ZornVectorMatrix.conj b.a)
            (ZornVectorMatrix.conj (zorn_basis m))) +
        zornBilin (((1 / 2 : ℝ) * (a.α₃ + a.α₁)) • σZorn (zorn_basis m))
          (((1 / 2 : ℝ) * (b.α₃ + b.α₁)) • zorn_basis m) = _
    simp only [zornBilin_smul_left, zornBilin_smul_right]
    rw [zornBilin_symm b.c (zorn_basis m)]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have h1 := zornBilin_sigma_basis_inner_sum a.c b.c
  have h2 : ∑ m : Fin 8, zornBilin (σZorn (zorn_basis m)) (zorn_basis m) = 8 := by
    simp_rw [← zornBilin_σZorn_right, zornBilin_zorn_basis_sigma]
    simp
  have h3 : ∑ m : Fin 8, zornBilin
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj (σZorn (zorn_basis m))) (ZornVectorMatrix.conj a.b))
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis m)) (ZornVectorMatrix.conj b.b)) =
      4 * zornBilin a.b b.b := by
    have hs := zornBilin_conj_mul_left_sigma_sum a.b b.b
    rw [← hs]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ZornVectorMatrix.conj_mul a.b (σZorn (zorn_basis m)),
      ← ZornVectorMatrix.conj_mul b.b (zorn_basis m), zornBilin_conj_conj]
  have h4 : ∑ m : Fin 8, zornBilin
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj a.a) (ZornVectorMatrix.conj (σZorn (zorn_basis m))))
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj b.a) (ZornVectorMatrix.conj (zorn_basis m))) =
      4 * zornBilin a.a b.a := by
    have hs := zornBilin_mul_right_sigma_sum a.a b.a
    rw [← hs]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ZornVectorMatrix.conj_mul (σZorn (zorn_basis m)) a.a,
      ← ZornVectorMatrix.conj_mul (zorn_basis m) b.a, zornBilin_conj_conj]
  have h1' : ∑ x : Fin 8, zornBilin a.c (σZorn (zorn_basis x)) * zornBilin (zorn_basis x) b.c =
      zornBilin a.c b.c := h1
  rw [h1', h2, h3, h4]
  ring

theorem h3zorn_jordanLmul_trace_mul (a b : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b) =
      3 * H3Zorn.traceBilin a b + 2 * H3Zorn.linearTrace a * H3Zorn.linearTrace b := by
  rw [trace_h3zorn_eq_sum_σ]
  have hstep : ∀ i : Fin 27,
      H3Zorn.traceBilin (σH3 (h3ZornBasis i)) ((jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b) (h3ZornBasis i)) =
        H3Zorn.traceBilin (a * σH3 (h3ZornBasis i)) (b * h3ZornBasis i) := fun i => by
    change H3Zorn.traceBilin (σH3 (h3ZornBasis i)) (jordanLmul (R := ℝ) a (b * h3ZornBasis i)) =
      H3Zorn.traceBilin (jordanLmul (R := ℝ) a (σH3 (h3ZornBasis i))) (b * h3ZornBasis i)
    rw [← h3zornTraceAdjoint_pair (jordanLmul (R := ℝ) a) (σH3 (h3ZornBasis i)) (b * h3ZornBasis i),
      h3zornTraceAdjoint_jordanLmul]
  simp_rw [hstep]
  rw [h3SectorEquiv_sum]
  have hz0_σ : σZorn ZornVectorMatrix.zero = ZornVectorMatrix.zero := by
    change σZorn (0 : ZornVectorMatrix ℝ) = 0; exact σZorn_zero
  have hd0 : σH3 (h3ZornBasis (finOfSector (.diag 0))) = h3_diag₁ := by
    rw [h3ZornBasis_sector]; apply H3Zorn.ext_h3 <;> simp [h3_diag₁, hz0_σ]
  have hd1 : σH3 (h3ZornBasis (finOfSector (.diag 1))) = h3_diag₂ := by
    rw [h3ZornBasis_sector]; apply H3Zorn.ext_h3 <;> simp [h3_diag₂, hz0_σ]
  have hd2 : σH3 (h3ZornBasis (finOfSector (.diag 2))) = h3_diag₃ := by
    rw [h3ZornBasis_sector]; apply H3Zorn.ext_h3 <;> simp [h3_diag₃, hz0_σ]
  have hs0 : h3ZornBasis (finOfSector (.diag 0)) = h3_diag₁ := h3ZornBasis_sector (.diag 0)
  have hs1 : h3ZornBasis (finOfSector (.diag 1)) = h3_diag₂ := h3ZornBasis_sector (.diag 1)
  have hs2 : h3ZornBasis (finOfSector (.diag 2)) = h3_diag₃ := h3ZornBasis_sector (.diag 2)
  have hj12 : ∀ m : Fin 8, σH3 (h3ZornBasis (finOfSector (.j12 m))) = embedJ12 (σZorn (zorn_basis m)) := by
    intro m; rw [h3ZornBasis_sector]
    apply H3Zorn.ext_h3 <;> simp [embedJ12, hz0_σ]
  have hj23 : ∀ m : Fin 8, σH3 (h3ZornBasis (finOfSector (.j23 m))) = embedJ23 (σZorn (zorn_basis m)) := by
    intro m; rw [h3ZornBasis_sector]
    apply H3Zorn.ext_h3 <;> simp [embedJ23, hz0_σ]
  have hj31 : ∀ m : Fin 8, σH3 (h3ZornBasis (finOfSector (.j31 m))) = embedJ31 (σZorn (zorn_basis m)) := by
    intro m; rw [h3ZornBasis_sector]
    apply H3Zorn.ext_h3 <;> simp [embedJ31, hz0_σ]
  rw [hd0, hd1, hd2, hs0, hs1, hs2]
  simp_rw [hj12, hj23, hj31, h3ZornBasis_sector]
  rw [traceBilin_h3_mul_diag₁, traceBilin_h3_mul_diag₂, traceBilin_h3_mul_diag₃,
    traceBilin_h3_mul_j12_sum, traceBilin_h3_mul_j23_sum, traceBilin_h3_mul_j31_sum]
  change _ = 3 * (a.α₁ * b.α₁ + a.α₂ * b.α₂ + a.α₃ * b.α₃ + zornBilin a.a b.a + zornBilin a.b b.b + zornBilin a.c b.c) +
    2 * (a.α₁ + a.α₂ + a.α₃) * (b.α₁ + b.α₂ + b.α₃)
  ring

theorem h3zorn_derivation_linearTrace_zero (D : H3ZornF4Derivations) (u : H3Zorn ℝ) :
    H3Zorn.linearTrace (D.1 u) = 0 := by
  have h9 := h3Zorn_jordanLmul_operatorTrace_eq_nine_linearTrace (D.1 u)
  have hcomm : jordanLmul (R := ℝ) (D.1 u) =
      D.1 * jordanLmul (R := ℝ) u - jordanLmul (R := ℝ) u * D.1 := by
    apply LinearMap.ext; intro z
    change (D.1 u) * z = D.1 (u * z) - u * (D.1 z)
    have hd := D.2 u z
    change D.1 (u * z) = D.1 u * z + u * D.1 z at hd
    rw [hd]; abel
  have htr : LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul (R := ℝ) (D.1 u)) = 0 := by
    rw [hcomm, map_sub, LinearMap.trace_mul_comm, sub_self]
  linarith

theorem h3zorn_deriv_innerDeriv_trace (D : H3ZornF4Derivations) (u v : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ) (D.1 * (h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ))) =
      3 * H3Zorn.traceBilin (D.1 u) v := by
  have hinner : (h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ)) =
      ⁅jordanLmul (R := ℝ) u, jordanLmul (R := ℝ) v⁆ := by
    apply LinearMap.ext; intro z
    change u * (v * z) - v * (u * z) = _
    rfl
  have hDL : ⁅D.1, jordanLmul (R := ℝ) u⁆ = jordanLmul (R := ℝ) (D.1 u) := by
    apply LinearMap.ext; intro z
    change D.1 (u * z) - u * (D.1 z) = (D.1 u) * z
    have hd := D.2 u z
    change D.1 (u * z) = D.1 u * z + u * D.1 z at hd
    rw [hd]; abel
  rw [hinner, ← LinearMap.trace_lie_mul_eq D.1 (jordanLmul (R := ℝ) u) (jordanLmul (R := ℝ) v),
    hDL, h3zorn_jordanLmul_trace_mul,
    h3zorn_derivation_linearTrace_zero D u, mul_zero, zero_mul, add_zero]

private theorem strDerivPart_bracket (T₁ T₂ : h3zornTKKDatum.str) :
    (tkk5StrDerivPart ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩).1 =
      (tkk5StrDerivPart T₁).1 * (tkk5StrDerivPart T₂).1 - (tkk5StrDerivPart T₂).1 * (tkk5StrDerivPart T₁).1 +
      (h3ZornJordanInnerDerivation (tkk5StrLmulPart T₁) (tkk5StrLmulPart T₂) : Module.End ℝ (H3Zorn ℝ)) := by
  rcases h3zornTKKDatum.str_decomp T₁.1 T₁.2 with ⟨D₁, a₁, hT₁⟩
  rcases h3zornTKKDatum.str_decomp T₂.1 T₂.2 with ⟨D₂, a₂, hT₂⟩
  have ha₁ : tkk5StrLmulPart T₁ = a₁ := by
    change T₁.1 1 = a₁
    rw [hT₁, LinearMap.add_apply, jordanLmul_apply,
      h3ZornF4_derivation_apply_one_eq_zero ⟨D₁.1, D₁.2⟩, zero_add]
    exact candidateJordanMul_one_right a₁
  have ha₂ : tkk5StrLmulPart T₂ = a₂ := by
    change T₂.1 1 = a₂
    rw [hT₂, LinearMap.add_apply, jordanLmul_apply,
      h3ZornF4_derivation_apply_one_eq_zero ⟨D₂.1, D₂.2⟩, zero_add]
    exact candidateJordanMul_one_right a₂
  have hd₁ : (tkk5StrDerivPart T₁).1 = D₁.1 := by rw [tkk5StrDerivPart_coe, ha₁, hT₁, add_sub_cancel_right]
  have hd₂ : (tkk5StrDerivPart T₂).1 = D₂.1 := by rw [tkk5StrDerivPart_coe, ha₂, hT₂, add_sub_cancel_right]
  have ha₁₂ : tkk5StrLmulPart ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩ =
      D₁.1 a₂ - D₂.1 a₁ := by
    change (T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1) 1 = D₁.1 a₂ - D₂.1 a₁
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hT₁, hT₂]
    have h1a : (D₁.1 + jordanLmul (R := ℝ) a₁) 1 = a₁ := by
      rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero ⟨D₁.1, D₁.2⟩, zero_add]
      exact candidateJordanMul_one_right a₁
    have h2a : (D₂.1 + jordanLmul (R := ℝ) a₂) 1 = a₂ := by
      rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero ⟨D₂.1, D₂.2⟩, zero_add]
      exact candidateJordanMul_one_right a₂
    rw [h2a, h1a, LinearMap.add_apply, LinearMap.add_apply, jordanLmul_apply, jordanLmul_apply]
    change (D₁.1 a₂ + a₁ * a₂) - (D₂.1 a₁ + a₂ * a₁) = D₁.1 a₂ - D₂.1 a₁
    rw [mul_comm a₂ a₁]; abel
  rw [tkk5StrDerivPart_coe, ha₁₂, ha₁, ha₂, hd₁, hd₂]
  apply LinearMap.ext; intro z
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    Module.End.mul_apply, jordanLmul_apply]
  rw [hT₁, hT₂]
  simp only [LinearMap.add_apply, jordanLmul_apply]
  change (D₁.1 (D₂.1 z + a₂ * z) + a₁ * (D₂.1 z + a₂ * z)) -
      (D₂.1 (D₁.1 z + a₁ * z) + a₂ * (D₁.1 z + a₁ * z)) - (D₁.1 a₂ - D₂.1 a₁) * z =
    (D₁.1 (D₂.1 z) - D₂.1 (D₁.1 z)) + (a₁ * (a₂ * z) - a₂ * (a₁ * z))
  have hm₁ : D₁.1 (a₂ * z) = D₁.1 a₂ * z + a₂ * D₁.1 z := D₁.2 a₂ z
  have hm₂ : D₂.1 (a₁ * z) = D₂.1 a₁ * z + a₁ * D₂.1 z := D₂.2 a₁ z
  rw [D₁.1.map_add, D₂.1.map_add, hm₁, hm₂, mul_add, mul_add, sub_mul]
  abel

private theorem strLmulPart_bracket (T₁ T₂ : h3zornTKKDatum.str) :
    tkk5StrLmulPart ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩ =
      (tkk5StrDerivPart T₁).1 (tkk5StrLmulPart T₂) - (tkk5StrDerivPart T₂).1 (tkk5StrLmulPart T₁) := by
  rcases h3zornTKKDatum.str_decomp T₁.1 T₁.2 with ⟨D₁, a₁, hT₁⟩
  rcases h3zornTKKDatum.str_decomp T₂.1 T₂.2 with ⟨D₂, a₂, hT₂⟩
  have ha₁ : tkk5StrLmulPart T₁ = a₁ := by
    change T₁.1 1 = a₁
    rw [hT₁, LinearMap.add_apply, jordanLmul_apply,
      h3ZornF4_derivation_apply_one_eq_zero ⟨D₁.1, D₁.2⟩, zero_add]
    exact candidateJordanMul_one_right a₁
  have ha₂ : tkk5StrLmulPart T₂ = a₂ := by
    change T₂.1 1 = a₂
    rw [hT₂, LinearMap.add_apply, jordanLmul_apply,
      h3ZornF4_derivation_apply_one_eq_zero ⟨D₂.1, D₂.2⟩, zero_add]
    exact candidateJordanMul_one_right a₂
  have hd₁ : (tkk5StrDerivPart T₁).1 = D₁.1 := by rw [tkk5StrDerivPart_coe, ha₁, hT₁, add_sub_cancel_right]
  have hd₂ : (tkk5StrDerivPart T₂).1 = D₂.1 := by rw [tkk5StrDerivPart_coe, ha₂, hT₂, add_sub_cancel_right]
  rw [ha₁, ha₂, hd₁, hd₂]
  change (T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1) 1 = D₁.1 a₂ - D₂.1 a₁
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hT₁, hT₂]
  have h1a : (D₁.1 + jordanLmul (R := ℝ) a₁) 1 = a₁ := by
    rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero ⟨D₁.1, D₁.2⟩, zero_add]
    exact candidateJordanMul_one_right a₁
  have h2a : (D₂.1 + jordanLmul (R := ℝ) a₂) 1 = a₂ := by
    rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero ⟨D₂.1, D₂.2⟩, zero_add]
    exact candidateJordanMul_one_right a₂
  rw [h2a, h1a, LinearMap.add_apply, LinearMap.add_apply, jordanLmul_apply, jordanLmul_apply]
  change (D₁.1 a₂ + a₁ * a₂) - (D₂.1 a₁ + a₂ * a₁) = D₁.1 a₂ - D₂.1 a₁
  rw [mul_comm a₂ a₁]; abel

private theorem strDerivPart_tripleD (u v : H3Zorn ℝ) :
    (tkk5StrDerivPart ⟨JordanTKK.tripleD ℝ u v, h3zornTKKDatum.tripleD_mem_str u v⟩).1 =
      (h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ)) := by
  have ha : tkk5StrLmulPart ⟨JordanTKK.tripleD ℝ u v, h3zornTKKDatum.tripleD_mem_str u v⟩ = u * v := by
    change JordanTKK.tripleD ℝ u v 1 = u * v
    rw [JordanTKK.tripleD_eq_left_add_inner, LinearMap.add_apply, jordanLmul_apply]
    change (u * v) * 1 + (u * (v * 1) - v * (u * 1)) = u * v
    have h1 : ∀ w : H3Zorn ℝ, w * 1 = w := candidateJordanMul_one_right
    rw [h1 (u * v), h1 v, h1 u, mul_comm v u, sub_self, add_zero]
  apply LinearMap.ext; intro z
  rw [tkk5StrDerivPart_coe, ha, LinearMap.sub_apply]
  change JordanTKK.tripleD ℝ u v z - (jordanLmul (R := ℝ) (u * v)) z =
    (h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ)) z
  rw [JordanTKK.tripleD_eq_left_add_inner, LinearMap.add_apply, jordanLmul_apply]
  change (u * v) * z + (u * (v * z) - v * (u * z)) - (u * v) * z = u * (v * z) - v * (u * z)
  abel

private theorem strLmulPart_tripleD (u v : H3Zorn ℝ) :
    tkk5StrLmulPart ⟨JordanTKK.tripleD ℝ u v, h3zornTKKDatum.tripleD_mem_str u v⟩ = u * v := by
  change JordanTKK.tripleD ℝ u v 1 = u * v
  rw [JordanTKK.tripleD_eq_left_add_inner, LinearMap.add_apply, jordanLmul_apply]
  change (u * v) * 1 + (u * (v * 1) - v * (u * 1)) = u * v
  have h1 : ∀ w : H3Zorn ℝ, w * 1 = w := candidateJordanMul_one_right
  rw [h1 (u * v), h1 v, h1 u, mul_comm v u, sub_self, add_zero]

private theorem traceBilin_deriv_skew (D : H3ZornF4Derivations) (x y : H3Zorn ℝ) :
    H3Zorn.traceBilin (D.1 x) y = -H3Zorn.traceBilin x (D.1 y) := by
  have hd : h3zornTraceAdjoint D.1 = -D.1 :=
    h3zornTraceAdjoint_derivation ⟨D.1, D.2⟩
  rw [H3Zorn.traceBilin_symm (D.1 x) y, ← h3zornTraceAdjoint_pair D.1 y x, hd]
  simp only [LinearMap.neg_apply, h3_traceBilin_neg_left]
  rw [H3Zorn.traceBilin_symm]

private theorem traceBilin_mul_swap_left (a x y : H3Zorn ℝ) :
    H3Zorn.traceBilin (a * x) y = H3Zorn.traceBilin a (x * y) := by
  rw [mul_comm a x]
  change H3Zorn.traceBilin (jordanLmul (R := ℝ) x a) y = H3Zorn.traceBilin a (jordanLmul (R := ℝ) x y)
  rw [← h3zornTraceAdjoint_pair (jordanLmul (R := ℝ) x) a y, h3zornTraceAdjoint_jordanLmul]

theorem B_E7_lieInvariant (Z X Y : H3ZornTKKLie) :
    B_E7 ⁅Z, X⁆ Y + B_E7 X ⁅Z, Y⁆ = 0 := by
  have hstr0 : (tkk5StrDerivPart (0 : h3zornTKKDatum.str)).1 = 0 := by
    apply LinearMap.ext; intro z
    rw [tkk5StrDerivPart_coe, map_zero]
    change (0 - (0 : H3Zorn ℝ) * z) = 0
    rw [zero_mul, sub_zero]
  have hnegLM : JordanTKK.negLM (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str) = negInj := rfl
  have hzeroLM : JordanTKK.zeroLM (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str) = zeroInj := rfl
  have hposLM : JordanTKK.posLM (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str) = posInj := rfl
  have hzeroInj : ∀ (T₀ : h3zornTKKDatum.str) (U V : H3ZornTKKLie),
      B_E7 ⁅zeroInj T₀, U⁆ V + B_E7 U ⁅zeroInj T₀, V⁆ = 0 := by
    intro T₀ U V
    have hBU : ⁅zeroInj T₀, U⁆ =
        negInj (T₀.1 U.neg) +
        zeroInj ⟨T₀.1 ∘ₗ U.zero.1 - U.zero.1 ∘ₗ T₀.1, h3zornTKKDatum.str_lie_mem T₀.2 U.zero.2⟩ +
        posInj (-h3zornTraceAdjoint T₀.1 U.pos) := by
      nth_rw 1 [JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) U]
      rw [hnegLM, hzeroLM, hposLM]
      simp only [lie_add, zeroInj_bracket_negInj, zeroInj_bracket_zeroInj, zeroInj_bracket_posInj]
    have hBV : ⁅zeroInj T₀, V⁆ =
        negInj (T₀.1 V.neg) +
        zeroInj ⟨T₀.1 ∘ₗ V.zero.1 - V.zero.1 ∘ₗ T₀.1, h3zornTKKDatum.str_lie_mem T₀.2 V.zero.2⟩ +
        posInj (-h3zornTraceAdjoint T₀.1 V.pos) := by
      nth_rw 1 [JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) V]
      rw [hnegLM, hzeroLM, hposLM]
      simp only [lie_add, zeroInj_bracket_negInj, zeroInj_bracket_zeroInj, zeroInj_bracket_posInj]
    rw [hBU, hBV]
    simp only [B_E7_apply, bE7Raw, h3tkk_add_neg, h3tkk_add_zero, h3tkk_add_pos]
    have hc_neg : ∀ C : H3Zorn ℝ, (negInj C).neg = C := fun _ => rfl
    have hc_neg0 : ∀ C : H3Zorn ℝ, (negInj C).pos = 0 := fun _ => rfl
    have hc_pos : ∀ C : H3Zorn ℝ, (posInj C).pos = C := fun _ => rfl
    have hc_pos0 : ∀ C : H3Zorn ℝ, (posInj C).neg = 0 := fun _ => rfl
    have hz_neg : ∀ T : h3zornTKKDatum.str, (zeroInj T).neg = 0 := fun _ => rfl
    have hz_pos : ∀ T : h3zornTKKDatum.str, (zeroInj T).pos = 0 := fun _ => rfl
    have hz_z : ∀ T : h3zornTKKDatum.str, (zeroInj T).zero = T := fun _ => rfl
    have hn_z : ∀ C : H3Zorn ℝ, (negInj C).zero = 0 := fun _ => rfl
    have hp_z : ∀ C : H3Zorn ℝ, (posInj C).zero = 0 := fun _ => rfl
    simp only [hc_neg, hc_neg0, hc_pos, hc_pos0, hz_neg, hz_pos, hz_z, hn_z, hp_z,
      zero_add, add_zero]
    rw [strDerivPart_bracket, strDerivPart_bracket, strLmulPart_bracket, strLmulPart_bracket]
    set D₀ := tkk5StrDerivPart T₀
    set DU := tkk5StrDerivPart U.zero
    set DV := tkk5StrDerivPart V.zero
    set a₀ := tkk5StrLmulPart T₀
    set aU := tkk5StrLmulPart U.zero
    set aV := tkk5StrLmulPart V.zero
    simp only [sub_mul, add_mul, mul_sub, mul_add, map_add, map_sub,
      H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_sub_right]
    rw [LinearMap.trace_mul_comm (R := ℝ) (M := H3Zorn ℝ)
        (h3ZornJordanInnerDerivation a₀ aU : Module.End ℝ (H3Zorn ℝ)) DV.1,
      h3zorn_deriv_innerDeriv_trace DV a₀ aU,
      h3zorn_deriv_innerDeriv_trace DU a₀ aV,
      LinearMap.trace_mul_cycle (R := ℝ) (M := H3Zorn ℝ) D₀.1 DU.1 DV.1,
      LinearMap.trace_mul_comm (R := ℝ) (M := H3Zorn ℝ) (DV.1 * D₀.1) DU.1,
      LinearMap.trace_mul_comm (R := ℝ) (M := H3Zorn ℝ) (DU.1 * D₀.1) DV.1,
      ← mul_assoc DU.1 D₀.1 DV.1,
      LinearMap.trace_mul_comm (R := ℝ) (M := H3Zorn ℝ) (DU.1 * D₀.1) DV.1]
    have hD0_skew1 := traceBilin_deriv_skew D₀ aU aV
    have hDU_skew : H3Zorn.traceBilin (DU.1 a₀) aV = H3Zorn.traceBilin aV (DU.1 a₀) :=
      H3Zorn.traceBilin_symm _ _
    have hDV_skew : H3Zorn.traceBilin (DV.1 a₀) aU = H3Zorn.traceBilin aU (DV.1 a₀) :=
      H3Zorn.traceBilin_symm _ _
    have hpair1 : H3Zorn.traceBilin (T₀.1 U.neg) V.pos = H3Zorn.traceBilin U.neg (h3zornTraceAdjoint T₀.1 V.pos) := by
      rw [H3Zorn.traceBilin_symm (T₀.1 U.neg) V.pos, ← h3zornTraceAdjoint_pair T₀.1 V.pos U.neg,
        H3Zorn.traceBilin_symm]
    have hpair2 : H3Zorn.traceBilin (h3zornTraceAdjoint T₀.1 U.pos) V.neg = H3Zorn.traceBilin U.pos (T₀.1 V.neg) :=
      h3zornTraceAdjoint_pair T₀.1 U.pos V.neg
    rw [h3_traceBilin_neg_left, h3_traceBilin_neg_right, hD0_skew1, hDU_skew, hDV_skew, hpair1, hpair2]
    ring
  have hnegInj : ∀ (C : H3Zorn ℝ) (U V : H3ZornTKKLie),
      B_E7 ⁅negInj C, U⁆ V + B_E7 U ⁅negInj C, V⁆ = 0 := by
    intro C U V
    have hBU : ⁅negInj C, U⁆ =
        negInj (-(U.zero.1 C)) +
        zeroInj ⟨JordanTKK.tripleD ℝ C U.pos, h3zornTKKDatum.tripleD_mem_str C U.pos⟩ := by
      nth_rw 1 [JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) U]
      rw [hnegLM, hzeroLM, hposLM]
      simp only [lie_add, negInj_bracket_negInj, negInj_bracket_zeroInj, negInj_bracket_posInj, zero_add]
    have hBV : ⁅negInj C, V⁆ =
        negInj (-(V.zero.1 C)) +
        zeroInj ⟨JordanTKK.tripleD ℝ C V.pos, h3zornTKKDatum.tripleD_mem_str C V.pos⟩ := by
      nth_rw 1 [JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) V]
      rw [hnegLM, hzeroLM, hposLM]
      simp only [lie_add, negInj_bracket_negInj, negInj_bracket_zeroInj, negInj_bracket_posInj, zero_add]
    rw [hBU, hBV]
    simp only [B_E7_apply, bE7Raw, h3tkk_add_neg, h3tkk_add_zero, h3tkk_add_pos]
    have hc_neg : ∀ x : H3Zorn ℝ, (negInj x).neg = x := fun _ => rfl
    have hc_neg0 : ∀ x : H3Zorn ℝ, (negInj x).pos = 0 := fun _ => rfl
    have hz_neg : ∀ T : h3zornTKKDatum.str, (zeroInj T).neg = 0 := fun _ => rfl
    have hz_pos : ∀ T : h3zornTKKDatum.str, (zeroInj T).pos = 0 := fun _ => rfl
    have hz_z : ∀ T : h3zornTKKDatum.str, (zeroInj T).zero = T := fun _ => rfl
    have hn_z : ∀ x : H3Zorn ℝ, (negInj x).zero = 0 := fun _ => rfl
    simp [hc_neg, hc_neg0, hz_neg, hz_pos, hz_z, hn_z]
    rw [strDerivPart_tripleD, strDerivPart_tripleD, strLmulPart_tripleD, strLmulPart_tripleD,
      LinearMap.trace_mul_comm (R := ℝ) (M := H3Zorn ℝ) _ (tkk5StrDerivPart V.zero).1,
      h3zorn_deriv_innerDeriv_trace (tkk5StrDerivPart V.zero) C U.pos,
      h3zorn_deriv_innerDeriv_trace (tkk5StrDerivPart U.zero) C V.pos]
    have hUV : ∀ (W : H3ZornTKKLie) (Y : H3Zorn ℝ),
        H3Zorn.traceBilin ((tkk5StrDerivPart W.zero).1 C) Y +
          H3Zorn.traceBilin (C * Y) (tkk5StrLmulPart W.zero) =
        H3Zorn.traceBilin (W.zero.1 C) Y := fun W Y => by
      rcases h3zornTKKDatum.str_decomp W.zero.1 W.zero.2 with ⟨DW, aW, hW⟩
      have haW : tkk5StrLmulPart W.zero = aW := by
        change W.zero.1 1 = aW
        rw [hW, LinearMap.add_apply, jordanLmul_apply,
          h3ZornF4_derivation_apply_one_eq_zero ⟨DW.1, DW.2⟩, zero_add]
        exact candidateJordanMul_one_right aW
      have hdW : (tkk5StrDerivPart W.zero).1 = DW.1 := by
        rw [tkk5StrDerivPart_coe, haW, hW, add_sub_cancel_right]
      rw [hdW, haW, hW, LinearMap.add_apply, jordanLmul_apply, H3Zorn.traceBilin_add_left]
      rw [H3Zorn.traceBilin_symm (C * Y) aW, traceBilin_mul_swap_left aW C Y]
    have h1 := hUV V U.pos
    have h2 := hUV U V.pos
    have h0h : (⟨0, 0, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩ : H3Zorn ℝ) = 0 := rfl
    simp only [h0h, add_zero, H3Zorn.traceBilin_zero_left, H3Zorn.traceBilin_zero_right, zero_add]
    rw [H3Zorn.traceBilin_symm (tkk5StrLmulPart U.zero) (C * V.pos),
      h3_traceBilin_neg_left, H3Zorn.traceBilin_symm U.pos (-(V.zero.1 C)),
      h3_traceBilin_neg_left]
    linarith
  have hposInj : ∀ (C : H3Zorn ℝ) (U V : H3ZornTKKLie),
      B_E7 ⁅posInj C, U⁆ V + B_E7 U ⁅posInj C, V⁆ = 0 := by
    intro C U V
    have hz_s : σH3 (0 : H3Zorn ℝ) = 0 := map_zero σH3
    have hth : posInj C = θE7 (negInj (-σH3 C)) := by
      apply h3zornTKKLie_ext
      · change (0 : H3Zorn ℝ) = -σH3 (0 : H3Zorn ℝ); rw [hz_s, neg_zero]
      · apply Subtype.ext
        change (0 : Module.End ℝ (H3Zorn ℝ)) = -σConjEnd (h3zornTraceAdjoint 0)
        rw [show h3zornTraceAdjoint (0 : Module.End ℝ (H3Zorn ℝ)) = 0 from map_zero h3zornTraceAdjointLM]
        simp
      · simp [negInj, posInj, σH3_involutive]
    rw [hth, ← B_E7_θE7 ⁅θE7 (negInj (-σH3 C)), U⁆ V,
      ← B_E7_θE7 U ⁅θE7 (negInj (-σH3 C)), V⁆,
      LieEquiv.map_lie, LieEquiv.map_lie, θE7_involutive]
    exact hnegInj (-σH3 C) (θE7 U) (θE7 V)
  have h1' : B_E7 ⁅Z, X⁆ Y =
      B_E7 ⁅negInj Z.neg, X⁆ Y + B_E7 ⁅zeroInj Z.zero, X⁆ Y + B_E7 ⁅posInj Z.pos, X⁆ Y := by
    conv_lhs => rw [JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) Z, hnegLM, hzeroLM, hposLM]
    simp only [add_lie, map_add, LinearMap.add_apply]
  have h2' : B_E7 X ⁅Z, Y⁆ =
      B_E7 X ⁅negInj Z.neg, Y⁆ + B_E7 X ⁅zeroInj Z.zero, Y⁆ + B_E7 X ⁅posInj Z.pos, Y⁆ := by
    conv_lhs => rw [JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) Z, hnegLM, hzeroLM, hposLM]
    simp only [add_lie, map_add]
  linarith [hnegInj Z.neg X Y, hzeroInj Z.zero X Y, hposInj Z.pos X Y]

private theorem traceBilin_crossProduct_cycle (a b c : H3Zorn ℝ) :
    H3Zorn.traceBilin (H3Zorn.crossProduct a b) c =
      H3Zorn.traceBilin a (H3Zorn.crossProduct b c) :=
  H3Zorn.traceBilin_crossProduct_assoc a b c

theorem B_E7_K_eq (Q₁ Q₂ : Charge) (X : H3ZornTKKLie) :
    B_E7 (K Q₁ Q₂) X = -6 * symplecticForm (repE7 X Q₁) Q₂ := by
  rcases h3zornTKKDatum.str_decomp X.zero.1 X.zero.2 with ⟨D, a, hX0⟩
  have ha : tkk5StrLmulPart X.zero = a := by
    change X.zero.1 1 = a
    rw [hX0, LinearMap.add_apply, jordanLmul_apply,
      h3ZornF4_derivation_apply_one_eq_zero ⟨D.1, D.2⟩, zero_add]
    exact candidateJordanMul_one_right a
  have hd : (tkk5StrDerivPart X.zero).1 = D.1 := by
    rw [tkk5StrDerivPart_coe, ha, hX0, add_sub_cancel_right]
  have hhadj : h3zornTraceAdjoint X.zero.1 = -D.1 + jordanLmul (R := ℝ) a := by
    rw [hX0, show h3zornTraceAdjoint (D.1 + jordanLmul (R := ℝ) a) =
        h3zornTraceAdjointLM (D.1 + jordanLmul (R := ℝ) a) from rfl,
      map_add, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjoint_derivation, h3zornTraceAdjoint_jordanLmul]
  have hK_der : (tkk5StrDerivPart (K Q₁ Q₂).zero).1 =
      (-2 : ℝ) • ((h3ZornJordanInnerDerivation Q₁.x Q₂.y : Module.End ℝ (H3Zorn ℝ)) +
        (h3ZornJordanInnerDerivation Q₂.x Q₁.y : Module.End ℝ (H3Zorn ℝ))) := by
    have hK0 : (K Q₁ Q₂).zero =
        (-2 : ℝ) • (⟨JordanTKK.tripleD ℝ Q₁.x Q₂.y, h3zornTKKDatum.tripleD_mem_str _ _⟩ +
          ⟨JordanTKK.tripleD ℝ Q₂.x Q₁.y, h3zornTKKDatum.tripleD_mem_str _ _⟩) +
        (-(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
          H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y) • h3zornStrOne := rfl
    rw [hK0, tkk5StrDerivPart_add, tkk5StrDerivPart_smul, tkk5StrDerivPart_add, tkk5StrDerivPart_smul]
    have h1d : tkk5StrDerivPart h3zornStrOne = 0 := by
      apply Subtype.ext; rw [tkk5StrDerivPart_coe]
      have hs : tkk5StrLmulPart h3zornStrOne = 1 := by
        change h3zornStrOne.1 1 = 1
        rw [h3zornStrOne_apply]
      rw [hs]; apply LinearMap.ext; intro z
      rw [LinearMap.sub_apply, h3zornStrOne_apply, jordanLmul_apply]
      change z - candidateJordanMul 1 z = 0
      rw [candidateJordanMul_comm 1 z, candidateJordanMul_one_right z, sub_self]
    rw [h1d, smul_zero, add_zero]
    change (-2 : ℝ) • ((tkk5StrDerivPart ⟨JordanTKK.tripleD ℝ Q₁.x Q₂.y, _⟩).1 +
        (tkk5StrDerivPart ⟨JordanTKK.tripleD ℝ Q₂.x Q₁.y, _⟩).1) = _
    rw [strDerivPart_tripleD, strDerivPart_tripleD]
  have hK_lm : tkk5StrLmulPart (K Q₁ Q₂).zero =
      (-2 : ℝ) • (Q₁.x * Q₂.y + Q₂.x * Q₁.y) +
      (-(Q₁.alpha * Q₂.beta + Q₁.beta * Q₂.alpha) +
        H3Zorn.traceBilin Q₁.x Q₂.y + H3Zorn.traceBilin Q₂.x Q₁.y) • (1 : H3Zorn ℝ) := by
    change (K Q₁ Q₂).zero.1 1 = _
    simp only [K_zero, Submodule.coe_add, Submodule.coe_smul, LinearMap.add_apply,
      LinearMap.smul_apply, h3zornStrOne_apply]
    have h12 : JordanTKK.tripleD ℝ Q₁.x Q₂.y 1 = Q₁.x * Q₂.y := strLmulPart_tripleD Q₁.x Q₂.y
    have h21 : JordanTKK.tripleD ℝ Q₂.x Q₁.y 1 = Q₂.x * Q₁.y := strLmulPart_tripleD Q₂.x Q₁.y
    rw [h12, h21]
  rw [B_E7_apply, bE7Raw, hK_der, hK_lm, hd, ha, K_neg, K_pos]
  simp only [smul_mul_assoc, add_mul, map_smul, map_add, smul_eq_mul,
    H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_smul_left,
    h3_traceBilin_neg_left, H3Zorn.traceBilin_one, H3Zorn.traceBilin_symm (1 : H3Zorn ℝ) a]
  rw [LinearMap.trace_mul_comm (R := ℝ) (M := H3Zorn ℝ) _ D.1,
    LinearMap.trace_mul_comm (R := ℝ) (M := H3Zorn ℝ) _ D.1,
    ← hd,
    h3zorn_deriv_innerDeriv_trace (tkk5StrDerivPart X.zero) Q₁.x Q₂.y,
    h3zorn_deriv_innerDeriv_trace (tkk5StrDerivPart X.zero) Q₂.x Q₁.y]
  rw [symplecticForm_expanded]
  simp only [repE7_alpha, repE7_beta, repE7_x, repE7_y]
  rw [hhadj, show strTrace X.zero = H3Zorn.linearTrace a by
    change H3Zorn.linearTrace (X.zero.1 1) = _; rw [show X.zero.1 1 = a from ha]]
  simp only [hX0, LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply,
    H3Zorn.traceBilin_add_left, H3Zorn.traceBilin_sub_left, H3Zorn.traceBilin_smul_left,
    h3_traceBilin_neg_left]
  rw [← hd, traceBilin_deriv_skew (tkk5StrDerivPart X.zero) Q₁.y Q₂.x,
    H3Zorn.traceBilin_symm Q₁.y ((tkk5StrDerivPart X.zero).1 Q₂.x), hd]
  rw [traceBilin_mul_swap_left a Q₁.x Q₂.y, traceBilin_mul_swap_left a Q₁.y Q₂.x,
    H3Zorn.traceBilin_symm a (Q₁.x * Q₂.y),
    mul_comm Q₁.y Q₂.x, H3Zorn.traceBilin_symm a (Q₂.x * Q₁.y)]
  rw [H3Zorn.traceBilin_symm (H3Zorn.crossProduct Q₁.x Q₂.x) X.neg,
    H3Zorn.traceBilin_symm (H3Zorn.crossProduct Q₁.y Q₂.y) X.pos,
    traceBilin_crossProduct_cycle X.neg Q₁.x Q₂.x,
    traceBilin_crossProduct_cycle X.pos Q₁.y Q₂.y,
    H3Zorn.traceBilin_symm Q₁.y X.neg, H3Zorn.traceBilin_symm Q₂.y X.neg,
    H3Zorn.traceBilin_symm Q₁.x X.pos, H3Zorn.traceBilin_symm Q₂.x X.pos,
    H3Zorn.traceBilin_symm Q₁.x Q₂.y, H3Zorn.traceBilin_symm Q₁.y Q₂.x]
  ring

theorem B₅_lieInvariant (W U V : FreudenthalTKK5E8) :
    B₅ ⁅W, U⁆ V + B₅ U ⁅W, V⁆ = 0 := by
  have hm2 : ∀ (w : ℝ) (U V : FreudenthalTKK5E8),
      B₅ ⁅injMinus2 w, U⁆ V + B₅ U ⁅injMinus2 w, V⁆ = 0 := by
    intro w U V
    change B₅ (bracket5LM (injMinus2 w) U) V + B₅ U (bracket5LM (injMinus2 w) V) = 0
    simp [B₅_apply, b5Raw, bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
      bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2,
      injMinus2_eq, symp_zero_left, symp_zero_right, K_zero_right]
    ring
  have hp2 : ∀ (w : ℝ) (U V : FreudenthalTKK5E8),
      B₅ ⁅injPlus2 w, U⁆ V + B₅ U ⁅injPlus2 w, V⁆ = 0 := by
    intro w U V
    have hth : injPlus2 w = θ₅ (injMinus2 (-w)) := by
      apply FreudenthalTKK5E8.ext <;> simp [θ₅_gMinus2, θ₅_gMinus1, θ₅_gZeroE7,
        θ₅_gZeroCenter, θ₅_gPlus1, θ₅_gPlus2, injMinus2, injPlus2]
    rw [hth, ← B₅_θ₅ ⁅θ₅ (injMinus2 (-w)), U⁆ V, ← B₅_θ₅ U ⁅θ₅ (injMinus2 (-w)), V⁆,
      LieEquiv.map_lie, LieEquiv.map_lie, θ₅_involutive]
    exact hm2 (-w) (θ₅ U) (θ₅ V)
  have hzc : ∀ (c : ℝ) (U V : FreudenthalTKK5E8),
      B₅ ⁅injZeroCenter c, U⁆ V + B₅ U ⁅injZeroCenter c, V⁆ = 0 := by
    intro c U V
    change B₅ (bracket5LM (injZeroCenter c) U) V + B₅ U (bracket5LM (injZeroCenter c) V) = 0
    simp [B₅_apply, b5Raw, bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
      bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2,
      injZeroCenter_eq, K_zero_right,
      symp_zero_left, symp_zero_right,
      symp_smul_left, symp_smul_right, symp_neg_left, symp_neg_right]
    ring
  have hze7 : ∀ (X : H3ZornTKKLie) (U V : FreudenthalTKK5E8),
      B₅ ⁅injZeroE7 X, U⁆ V + B₅ U ⁅injZeroE7 X, V⁆ = 0 := by
    intro X U V
    change B₅ (bracket5LM (injZeroE7 X) U) V + B₅ U (bracket5LM (injZeroE7 X) V) = 0
    simp [B₅_apply, b5Raw, bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
      bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2,
      injZeroE7_eq, K_zero_right, symp_zero_left, symp_zero_right]
    have hE7 := B_E7_lieInvariant X U.gZeroE7 V.gZeroE7
    have hs1 := repE7_symplecticForm_skew X U.gMinus1 V.gPlus1
    have hs2 := repE7_symplecticForm_skew X U.gPlus1 V.gMinus1
    linarith
  have hm1 : ∀ (P : Charge) (U V : FreudenthalTKK5E8),
      B₅ ⁅injMinus1 P, U⁆ V + B₅ U ⁅injMinus1 P, V⁆ = 0 := by
    intro P U V
    change B₅ (bracket5LM (injMinus1 P) U) V + B₅ U (bracket5LM (injMinus1 P) V) = 0
    simp [B₅_apply, b5Raw, bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
      bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2,
      injMinus1_eq,
      symp_zero_left, symp_add_left, symp_add_right,
      symp_smul_left, symp_smul_right, symp_neg_left, symp_neg_right]
    have hK1 : B_E7 (K U.gPlus1 P) V.gZeroE7 = -6 * symplecticForm (repE7 V.gZeroE7 P) U.gPlus1 := by
      rw [K_symm U.gPlus1 P, B_E7_K_eq]
    have hK2 : B_E7 U.gZeroE7 (K V.gPlus1 P) = -6 * symplecticForm (repE7 U.gZeroE7 P) V.gPlus1 := by
      rw [B_E7_symm, K_symm V.gPlus1 P, B_E7_K_eq]
    rw [hK1, hK2, symplecticForm_skew P U.gMinus1,
      symplecticForm_skew (repE7 V.gZeroE7 P) U.gPlus1,
      symplecticForm_skew P U.gPlus1, symplecticForm_skew P V.gPlus1]
    ring
  have hp1 : ∀ (P : Charge) (U V : FreudenthalTKK5E8),
      B₅ ⁅injPlus1 P, U⁆ V + B₅ U ⁅injPlus1 P, V⁆ = 0 := by
    intro P U V
    have hs2 : -(Real.sqrt 2 * -(Real.sqrt 2)⁻¹) = 1 := by
      rw [mul_neg, neg_neg, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]
    have hth : injPlus1 P = θ₅ (injMinus1 (-(Real.sqrt 2)⁻¹ • σC.symm P)) := by
      apply FreudenthalTKK5E8.ext <;> simp [θ₅_gMinus2, θ₅_gMinus1, θ₅_gZeroE7,
        θ₅_gZeroCenter, θ₅_gPlus1, θ₅_gPlus2, injMinus1, injPlus1, map_smul, smul_smul]
    rw [hth, ← B₅_θ₅ ⁅θ₅ (injMinus1 (-(Real.sqrt 2)⁻¹ • σC.symm P)), U⁆ V,
      ← B₅_θ₅ U ⁅θ₅ (injMinus1 (-(Real.sqrt 2)⁻¹ • σC.symm P)), V⁆,
      LieEquiv.map_lie, LieEquiv.map_lie, θ₅_involutive]
    exact hm1 (-(Real.sqrt 2)⁻¹ • σC.symm P) (θ₅ U) (θ₅ V)
  have hW : W = injMinus2 W.gMinus2 + injMinus1 W.gMinus1 + injZeroE7 W.gZeroE7 +
      injZeroCenter W.gZeroCenter + injPlus1 W.gPlus1 + injPlus2 W.gPlus2 := by
    apply FreudenthalTKK5E8.ext <;> simp
  have hU1 : B₅ ⁅W, U⁆ V = B₅ ⁅injMinus2 W.gMinus2, U⁆ V + B₅ ⁅injMinus1 W.gMinus1, U⁆ V +
      B₅ ⁅injZeroE7 W.gZeroE7, U⁆ V + B₅ ⁅injZeroCenter W.gZeroCenter, U⁆ V +
      B₅ ⁅injPlus1 W.gPlus1, U⁆ V + B₅ ⁅injPlus2 W.gPlus2, U⁆ V := by
    conv_lhs => rw [hW]
    simp only [add_lie, map_add, LinearMap.add_apply]
  have hU2 : B₅ U ⁅W, V⁆ = B₅ U ⁅injMinus2 W.gMinus2, V⁆ + B₅ U ⁅injMinus1 W.gMinus1, V⁆ +
      B₅ U ⁅injZeroE7 W.gZeroE7, V⁆ + B₅ U ⁅injZeroCenter W.gZeroCenter, V⁆ +
      B₅ U ⁅injPlus1 W.gPlus1, V⁆ + B₅ U ⁅injPlus2 W.gPlus2, V⁆ := by
    conv_lhs => rw [hW]
    simp only [add_lie, map_add]
  linarith [hm2 W.gMinus2 U V, hm1 W.gMinus1 U V, hze7 W.gZeroE7 U V,
    hzc W.gZeroCenter U V, hp1 W.gPlus1 U V, hp2 W.gPlus2 U V]

private theorem trace_deriv_σConjEnd_nonneg (D : H3ZornF4Derivations) :
    0 ≤ -LinearMap.trace ℝ (H3Zorn ℝ) (D.1 * σConjEnd D.1) := by
  rw [trace_h3zorn_eq_sum_σ, ← Finset.sum_neg_distrib]
  refine Finset.sum_nonneg fun i _ => ?_
  change 0 ≤ -H3Zorn.traceBilin (σH3 (h3ZornBasis i)) (D.1 (σH3 (D.1 (σH3 (h3ZornBasis i)))))
  rw [H3Zorn.traceBilin_symm (σH3 (h3ZornBasis i)), traceBilin_deriv_skew D, neg_neg,
    H3Zorn.traceBilin_symm _ (D.1 (σH3 (h3ZornBasis i)))]
  exact traceBilin_σH3_self_nonneg (D.1 (σH3 (h3ZornBasis i)))

private theorem trace_deriv_σConjEnd_eq_zero_iff (D : H3ZornF4Derivations) :
    -LinearMap.trace ℝ (H3Zorn ℝ) (D.1 * σConjEnd D.1) = 0 ↔ D = 0 := by
  constructor
  · intro h
    rw [trace_h3zorn_eq_sum_σ, ← Finset.sum_neg_distrib] at h
    have hall : ∀ i ∈ (Finset.univ : Finset (Fin 27)),
        -H3Zorn.traceBilin (σH3 (h3ZornBasis i)) ((D.1 * σConjEnd D.1) (h3ZornBasis i)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by
        change 0 ≤ -H3Zorn.traceBilin (σH3 (h3ZornBasis i)) (D.1 (σH3 (D.1 (σH3 (h3ZornBasis i)))))
        rw [H3Zorn.traceBilin_symm (σH3 (h3ZornBasis i)), traceBilin_deriv_skew D, neg_neg,
          H3Zorn.traceBilin_symm _ (D.1 (σH3 (h3ZornBasis i)))]
        exact traceBilin_σH3_self_nonneg _).mp h
    apply Subtype.ext
    apply h3ZornBasis.ext
    intro i
    have hsig : ∀ j : Fin 27, D.1 (σH3 (h3ZornBasis j)) = 0 := fun j => by
      have hj := hall j (Finset.mem_univ j)
      change -H3Zorn.traceBilin (σH3 (h3ZornBasis j)) (D.1 (σH3 (D.1 (σH3 (h3ZornBasis j))))) = 0 at hj
      rw [H3Zorn.traceBilin_symm (σH3 (h3ZornBasis j)), traceBilin_deriv_skew D, neg_neg,
        H3Zorn.traceBilin_symm _ (D.1 (σH3 (h3ZornBasis j))),
        traceBilin_σH3_self_eq_zero_iff] at hj
      exact hj
    have hbasis : h3ZornBasis i ∈ Submodule.span ℝ (Set.range (fun j => σH3 (h3ZornBasis j))) := by
      have hsp : σH3 (h3ZornBasis i) = ∑ j : Fin 27, (h3ZornBasis.repr (σH3 (h3ZornBasis i)) j) • h3ZornBasis j :=
        (h3ZornBasis.sum_repr _).symm
      rw [← σH3_involutive (h3ZornBasis i), hsp, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hmem : ∀ x ∈ Submodule.span ℝ (Set.range (fun j => σH3 (h3ZornBasis j))), D.1 x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem _ hy => rcases hy with ⟨j, rfl⟩; exact hsig j
      | zero => exact map_zero D.1
      | add _ _ _ _ ih1 ih2 => rw [map_add, ih1, ih2, add_zero]
      | smul c _ _ ih => rw [map_smul, ih, smul_zero]
    exact hmem _ hbasis
  · rintro rfl
    simp

theorem cartanInner5_self_eq (U : FreudenthalTKK5E8) :
    cartanInner5 U U =
      (-LinearMap.trace ℝ (H3Zorn ℝ) ((tkk5StrDerivPart U.gZeroE7.zero).1 * σConjEnd (tkk5StrDerivPart U.gZeroE7.zero).1) +
        3 * H3Zorn.traceBilin (tkk5StrLmulPart U.gZeroE7.zero) (σH3 (tkk5StrLmulPart U.gZeroE7.zero)) +
        3 * H3Zorn.traceBilin U.gZeroE7.neg (σH3 U.gZeroE7.neg) +
        3 * H3Zorn.traceBilin U.gZeroE7.pos (σH3 U.gZeroE7.pos)) +
      12 * U.gZeroCenter ^ 2 +
      6 * Real.sqrt 2 *
        (symplecticForm U.gMinus1 (σC U.gMinus1) + symplecticForm U.gPlus1 (σC U.gPlus1)) +
      6 * (U.gMinus2 ^ 2 + U.gPlus2 ^ 2) := by
  have hD : (tkk5StrDerivPart (θE7 U.gZeroE7).zero).1 = σConjEnd (tkk5StrDerivPart U.gZeroE7.zero).1 :=
    congrArg Subtype.val (strDerivPart_θE7 U.gZeroE7.zero)
  have ha : tkk5StrLmulPart (θE7 U.gZeroE7).zero = -σH3 (tkk5StrLmulPart U.gZeroE7.zero) :=
    strLmulPart_θE7 U.gZeroE7.zero
  simp only [cartanInner5_apply, B₅_apply, b5Raw, B_E7_apply, bE7Raw,
    θ₅_gMinus2, θ₅_gMinus1, θ₅_gZeroE7, θ₅_gZeroCenter, θ₅_gPlus1, θ₅_gPlus2,
    θE7_neg, θE7_pos, hD, ha, h3_traceBilin_neg_right, symp_smul_right]
  rw [H3Zorn.traceBilin_symm U.gZeroE7.pos (σH3 U.gZeroE7.pos)]
  ring

theorem cartanInner5_nonneg (U : FreudenthalTKK5E8) : 0 ≤ cartanInner5 U U := by
  rw [cartanInner5_self_eq]
  have h1 := trace_deriv_σConjEnd_nonneg (tkk5StrDerivPart U.gZeroE7.zero)
  have h2 := traceBilin_σH3_self_nonneg (tkk5StrLmulPart U.gZeroE7.zero)
  have h3 := traceBilin_σH3_self_nonneg U.gZeroE7.neg
  have h4 := traceBilin_σH3_self_nonneg U.gZeroE7.pos
  have h5 := symplecticForm_σC_self_nonneg U.gMinus1
  have h6 := symplecticForm_σC_self_nonneg U.gPlus1
  have hsq2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2, sq_nonneg U.gPlus2]

theorem cartanInner5_eq_zero_iff (U : FreudenthalTKK5E8) :
    cartanInner5 U U = 0 ↔ U = 0 := by
  constructor
  · intro h
    rw [cartanInner5_self_eq] at h
    have h1 := trace_deriv_σConjEnd_nonneg (tkk5StrDerivPart U.gZeroE7.zero)
    have h2 := traceBilin_σH3_self_nonneg (tkk5StrLmulPart U.gZeroE7.zero)
    have h3 := traceBilin_σH3_self_nonneg U.gZeroE7.neg
    have h4 := traceBilin_σH3_self_nonneg U.gZeroE7.pos
    have h5 := symplecticForm_σC_self_nonneg U.gMinus1
    have h6 := symplecticForm_σC_self_nonneg U.gPlus1
    have hsq2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hm2 : U.gMinus2 = 0 := by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gPlus2]
    have hp2 : U.gPlus2 = 0 := by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2]
    have hzc : U.gZeroCenter = 0 := by nlinarith [sq_nonneg U.gMinus2, sq_nonneg U.gPlus2]
    have hm1 : U.gMinus1 = 0 := (symplecticForm_σC_self_eq_zero_iff U.gMinus1).mp
      (by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2, sq_nonneg U.gPlus2])
    have hp1 : U.gPlus1 = 0 := (symplecticForm_σC_self_eq_zero_iff U.gPlus1).mp
      (by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2, sq_nonneg U.gPlus2])
    have hd : tkk5StrDerivPart U.gZeroE7.zero = 0 := (trace_deriv_σConjEnd_eq_zero_iff _).mp
      (by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2, sq_nonneg U.gPlus2])
    have ha : tkk5StrLmulPart U.gZeroE7.zero = 0 := (traceBilin_σH3_self_eq_zero_iff _).mp
      (by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2, sq_nonneg U.gPlus2])
    have hneg : U.gZeroE7.neg = 0 := (traceBilin_σH3_self_eq_zero_iff _).mp
      (by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2, sq_nonneg U.gPlus2])
    have hpos : U.gZeroE7.pos = 0 := (traceBilin_σH3_self_eq_zero_iff _).mp
      (by nlinarith [sq_nonneg U.gZeroCenter, sq_nonneg U.gMinus2, sq_nonneg U.gPlus2])
    have hz0 : U.gZeroE7.zero = 0 := by
      apply Subtype.ext
      have hcoe := tkk5StrDerivPart_coe U.gZeroE7.zero
      rw [hd, ha] at hcoe
      have hlm : jordanLmul (R := ℝ) (0 : H3Zorn ℝ) = 0 := by
        apply LinearMap.ext; intro z; change (0 : H3Zorn ℝ) * z = 0; exact zero_mul z
      rw [hlm, sub_zero] at hcoe
      exact hcoe.symm
    have he7 : U.gZeroE7 = 0 := h3zornTKKLie_ext hneg hz0 hpos
    exact FreudenthalTKK5E8.ext hm2 hm1 he7 hzc hp1 hp2
  · rintro rfl
    simp

/-! ### 120D/128D Cartan Eigenspace Dimensions (`+8` Signature) and `IsKilling` -/

private theorem zornBilin_zero_right (x : ZornVectorMatrix ℝ) : zornBilin x 0 = 0 := by
  have h := zornBilin_smul_right (0 : ℝ) x (0 : ZornVectorMatrix ℝ)
  simpa using h

private theorem zornBilin_sub_right (x y z : ZornVectorMatrix ℝ) :
    zornBilin x (y - z) = zornBilin x y - zornBilin x z := by
  rw [sub_eq_add_neg, zornBilin_add_right, zornBilin_neg_right, sub_eq_add_neg]

private theorem zornBilin_sum_right {ι : Type*} (s : Finset ι) (x : ZornVectorMatrix ℝ)
    (f : ι → ZornVectorMatrix ℝ) :
    zornBilin x (∑ i ∈ s, f i) = ∑ i ∈ s, zornBilin x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact zornBilin_zero_right x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, zornBilin_add_right, ih]

private theorem h3_sum_a {ι : Type*} (s : Finset ι) (f : ι → H3Zorn ℝ) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H3Zorn.add_readback, ih]
    rfl

private def zornEigBasis (i : Fin 8) : ZornVectorMatrix ℝ :=
  match i with
  | 0 => ⟨1, 0, 0, 1⟩
  | 1 => ⟨0, ZornVec3.basis 0, -ZornVec3.basis 0, 0⟩
  | 2 => ⟨0, ZornVec3.basis 1, -ZornVec3.basis 1, 0⟩
  | 3 => ⟨0, ZornVec3.basis 2, -ZornVec3.basis 2, 0⟩
  | 4 => ⟨1, 0, 0, -1⟩
  | 5 => ⟨0, ZornVec3.basis 0, ZornVec3.basis 0, 0⟩
  | 6 => ⟨0, ZornVec3.basis 1, ZornVec3.basis 1, 0⟩
  | 7 => ⟨0, ZornVec3.basis 2, ZornVec3.basis 2, 0⟩

private theorem σZorn_zornEigBasis (i : Fin 8) :
    σZorn (zornEigBasis i) = if i.val < 4 then zornEigBasis i else -zornEigBasis i := by
  fin_cases i
  all_goals
    apply ZornVectorMatrix.ext
    · simp [zornEigBasis, ZornVectorMatrix.neg]
    · funext k; fin_cases k <;> simp [zornEigBasis, ZornVectorMatrix.neg, ZornVec3.basis]
    · funext k; fin_cases k <;> simp [zornEigBasis, ZornVectorMatrix.neg, ZornVec3.basis]
    · simp [zornEigBasis, ZornVectorMatrix.neg]

private theorem zornBilin_zornEigBasis (i j : Fin 8) :
    zornBilin (zornEigBasis i) (zornEigBasis j) =
      if i = j then (if i.val < 4 then (2 : ℝ) else -2) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [zornEigBasis, zornBilin, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
      ZornVectorMatrix.trace, ZornVec3.dot, ZornVec3.basis] <;>
    try norm_num

private theorem zornEigBasis_linearIndependent : LinearIndependent ℝ zornEigBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 : zornBilin (zornEigBasis i) (∑ j : Fin 8, c j • zornEigBasis j) = 0 := by
    rw [hc, zornBilin_zero_right]
  have hsum : zornBilin (zornEigBasis i) (∑ j : Fin 8, c j • zornEigBasis j) =
      ∑ j : Fin 8, c j * zornBilin (zornEigBasis i) (zornEigBasis j) := by
    rw [zornBilin_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zornBilin_smul_right]
  rw [hsum] at h0
  simp_rw [zornBilin_zornEigBasis] at h0
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj.symm])
      (fun hi => absurd (Finset.mem_univ i) hi)] at h0
  simp only [ite_true] at h0
  by_cases hi : i.val < 4
  · simp only [hi, ite_true] at h0; linarith
  · simp only [hi, ite_false] at h0; linarith

/-- `+1`-eigenspace (`4D`) of `σZorn` on `ZornVectorMatrix ℝ`. -/
def zornCompact : Submodule ℝ (ZornVectorMatrix ℝ) :=
  LinearMap.ker (σZorn.toLinearMap - LinearMap.id)

/-- `-1`-eigenspace (`4D`) of `σZorn` on `ZornVectorMatrix ℝ`. -/
def zornNoncompact : Submodule ℝ (ZornVectorMatrix ℝ) :=
  LinearMap.ker (σZorn.toLinearMap + LinearMap.id)

@[simp] theorem mem_zornCompact_iff {X : ZornVectorMatrix ℝ} :
    X ∈ zornCompact ↔ σZorn X = X := by
  change σZorn X - X = 0 ↔ σZorn X = X
  exact sub_eq_zero

@[simp] theorem mem_zornNoncompact_iff {X : ZornVectorMatrix ℝ} :
    X ∈ zornNoncompact ↔ σZorn X = -X := by
  change σZorn X + X = 0 ↔ σZorn X = -X
  exact add_eq_zero_iff_eq_neg

theorem zornCompact_inf_zornNoncompact : zornCompact ⊓ zornNoncompact = ⊥ := by
  rw [eq_bot_iff]
  intro X hX
  rcases Submodule.mem_inf.mp hX with ⟨h1, h2⟩
  rw [mem_zornCompact_iff] at h1
  rw [mem_zornNoncompact_iff] at h2
  rw [Submodule.mem_bot]
  have h2X : (2 : ℝ) • X = 0 := by
    have hXneg : X = -X := h1.symm.trans h2
    calc (2 : ℝ) • X = X + X := two_smul ℝ X
      _ = X + (-X) := by nth_rw 2 [hXneg]
      _ = 0 := add_neg_cancel _
  exact (smul_eq_zero.mp h2X).resolve_left (by norm_num)

theorem zornCompact_sup_zornNoncompact : zornCompact ⊔ zornNoncompact = ⊤ := by
  rw [eq_top_iff]
  intro X _
  have hX : X = (1 / 2 : ℝ) • (X + σZorn X) + (1 / 2 : ℝ) • (X - σZorn X) := by module
  rw [hX]
  refine Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ ?_))
  · rw [mem_zornCompact_iff, map_add, σZorn_involutive, add_comm]
  · rw [mem_zornNoncompact_iff, map_sub, σZorn_involutive, neg_sub]

theorem finrank_zornCompact : Module.finrank ℝ zornCompact = 4 := by
  let v : Fin 4 → zornCompact := fun i =>
    ⟨zornEigBasis ⟨i.val, by omega⟩, by
      rw [mem_zornCompact_iff, σZorn_zornEigBasis]
      simp [i.isLt]⟩
  have hv : LinearIndependent ℝ v := by
    have hcomp : zornCompact.subtype ∘ v = fun i : Fin 4 => zornEigBasis ⟨i.val, by omega⟩ := rfl
    have hinj : Function.Injective (fun i : Fin 4 => (⟨i.val, by omega⟩ : Fin 8)) := by
      intro a b hab; ext; exact Fin.mk.inj hab
    have hli : LinearIndependent ℝ (zornCompact.subtype ∘ v) := by
      rw [hcomp]; exact zornEigBasis_linearIndependent.comp _ hinj
    exact hli.of_comp zornCompact.subtype
  have hgeC : 4 ≤ Module.finrank ℝ zornCompact := by
    simpa [Fintype.card_fin] using hv.fintype_card_le_finrank
  let w : Fin 4 → zornNoncompact := fun i =>
    ⟨zornEigBasis ⟨i.val + 4, by omega⟩, by
      rw [mem_zornNoncompact_iff, σZorn_zornEigBasis]
      have hlt : ¬ (i.val + 4 < 4) := by omega
      simp [hlt]⟩
  have hw : LinearIndependent ℝ w := by
    have hcomp : zornNoncompact.subtype ∘ w = fun i : Fin 4 => zornEigBasis ⟨i.val + 4, by omega⟩ := rfl
    have hinj : Function.Injective (fun i : Fin 4 => (⟨i.val + 4, by omega⟩ : Fin 8)) := by
      intro a b hab; ext; have := Fin.mk.inj hab; omega
    have hli : LinearIndependent ℝ (zornNoncompact.subtype ∘ w) := by
      rw [hcomp]; exact zornEigBasis_linearIndependent.comp _ hinj
    exact hli.of_comp zornNoncompact.subtype
  have hgeP : 4 ≤ Module.finrank ℝ zornNoncompact := by
    simpa [Fintype.card_fin] using hw.fintype_card_le_finrank
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq zornCompact zornNoncompact
  rw [zornCompact_sup_zornNoncompact, zornCompact_inf_zornNoncompact, finrank_top, finrank_bot,
    add_zero, finrank_zornVectorMatrix] at hsum
  omega

theorem finrank_zornNoncompact : Module.finrank ℝ zornNoncompact = 4 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq zornCompact zornNoncompact
  rw [zornCompact_sup_zornNoncompact, zornCompact_inf_zornNoncompact, finrank_top, finrank_bot,
    add_zero, finrank_zornVectorMatrix, finrank_zornCompact] at hsum
  omega

/-- `+1`-eigenspace (`15D`) of `σH3` on `H3Zorn ℝ`. -/
def h3Compact : Submodule ℝ (H3Zorn ℝ) :=
  LinearMap.ker (σH3.toLinearMap - LinearMap.id)

/-- `-1`-eigenspace (`12D`) of `σH3` on `H3Zorn ℝ`. -/
def h3Noncompact : Submodule ℝ (H3Zorn ℝ) :=
  LinearMap.ker (σH3.toLinearMap + LinearMap.id)

@[simp] theorem mem_h3Compact_iff {x : H3Zorn ℝ} : x ∈ h3Compact ↔ σH3 x = x := by
  change σH3 x - x = 0 ↔ σH3 x = x
  exact sub_eq_zero

@[simp] theorem mem_h3Noncompact_iff {x : H3Zorn ℝ} : x ∈ h3Noncompact ↔ σH3 x = -x := by
  change σH3 x + x = 0 ↔ σH3 x = -x
  exact add_eq_zero_iff_eq_neg

private def h3CompactEquiv :
    h3Compact ≃ₗ[ℝ] (ℝ × ℝ × ℝ) × (zornCompact × zornCompact × zornCompact) where
  toFun x :=
    ((x.1.α₁, x.1.α₂, x.1.α₃),
     (⟨x.1.a, mem_zornCompact_iff.mpr (by rw [← σH3_a]; exact congrArg H3Zorn.a (mem_h3Compact_iff.mp x.2))⟩,
      ⟨x.1.b, mem_zornCompact_iff.mpr (by rw [← σH3_b]; exact congrArg H3Zorn.b (mem_h3Compact_iff.mp x.2))⟩,
      ⟨x.1.c, mem_zornCompact_iff.mpr (by rw [← σH3_c]; exact congrArg H3Zorn.c (mem_h3Compact_iff.mp x.2))⟩))
  invFun p :=
    ⟨⟨p.1.1, p.1.2.1, p.1.2.2, p.2.1.1, p.2.2.1.1, p.2.2.2.1⟩,
      mem_h3Compact_iff.mpr (by
        apply H3Zorn.ext_h3 <;> simp [mem_zornCompact_iff.mp p.2.1.2,
          mem_zornCompact_iff.mp p.2.2.1.2, mem_zornCompact_iff.mp p.2.2.2.2])⟩
  left_inv x := by apply Subtype.ext; apply H3Zorn.ext_h3 <;> rfl
  right_inv p := by rcases p with ⟨⟨α₁, α₂, α₃⟩, ⟨a, b, c⟩⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def h3NoncompactEquiv :
    h3Noncompact ≃ₗ[ℝ] zornNoncompact × zornNoncompact × zornNoncompact where
  toFun x :=
    (⟨x.1.a, mem_zornNoncompact_iff.mpr (by rw [← σH3_a]; exact congrArg H3Zorn.a (mem_h3Noncompact_iff.mp x.2))⟩,
     ⟨x.1.b, mem_zornNoncompact_iff.mpr (by rw [← σH3_b]; exact congrArg H3Zorn.b (mem_h3Noncompact_iff.mp x.2))⟩,
     ⟨x.1.c, mem_zornNoncompact_iff.mpr (by rw [← σH3_c]; exact congrArg H3Zorn.c (mem_h3Noncompact_iff.mp x.2))⟩)
  invFun p :=
    ⟨⟨0, 0, 0, p.1.1, p.2.1.1, p.2.2.1⟩,
      mem_h3Noncompact_iff.mpr (by
        have hneg_h3 : (-⟨0, 0, 0, p.1.1, p.2.1.1, p.2.2.1⟩ : H3Zorn ℝ) =
            ⟨-0, -0, -0, -p.1.1, -p.2.1.1, -p.2.2.1⟩ := rfl
        rw [hneg_h3]
        apply H3Zorn.ext_h3 <;> simp [mem_zornNoncompact_iff.mp p.1.2,
          mem_zornNoncompact_iff.mp p.2.1.2, mem_zornNoncompact_iff.mp p.2.2.2])⟩
  left_inv x := by
    have hx := mem_h3Noncompact_iff.mp x.2
    have h1 : x.1.α₁ = 0 := by
      have h' : x.1.α₁ = -x.1.α₁ := by rw [← σH3_α₁]; exact congrArg H3Zorn.α₁ hx
      linarith
    have h2 : x.1.α₂ = 0 := by
      have h' : x.1.α₂ = -x.1.α₂ := by rw [← σH3_α₂]; exact congrArg H3Zorn.α₂ hx
      linarith
    have h3 : x.1.α₃ = 0 := by
      have h' : x.1.α₃ = -x.1.α₃ := by rw [← σH3_α₃]; exact congrArg H3Zorn.α₃ hx
      linarith
    apply Subtype.ext; apply H3Zorn.ext_h3 <;> simp [h1, h2, h3]
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_h3Compact : Module.finrank ℝ h3Compact = 15 := by
  rw [LinearEquiv.finrank_eq h3CompactEquiv, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self, finrank_zornCompact]

theorem finrank_h3Noncompact : Module.finrank ℝ h3Noncompact = 12 := by
  rw [LinearEquiv.finrank_eq h3NoncompactEquiv, Module.finrank_prod, Module.finrank_prod,
    finrank_zornNoncompact]

private def σF4 : H3ZornF4Derivations ≃ₗ[ℝ] H3ZornF4Derivations :=
  (H3ZornJordanAut.derivationLieEquiv σH3Aut).toLinearEquiv

@[simp] private theorem σF4_coe (D : H3ZornF4Derivations) :
    (σF4 D).1 = σConjEnd D.1 := by
  change (H3ZornJordanAut.derivationLieEquiv σH3Aut D).1 = σConjEnd D.1
  rw [H3ZornJordanAut.derivationLieEquiv_apply]
  apply LinearMap.ext; intro x; rfl

@[simp] private theorem σF4_involutive (D : H3ZornF4Derivations) : σF4 (σF4 D) = D := by
  apply Subtype.ext; simp

/-- `+1`-eigenspace (`24D`) of Cartan conjugation on `H3ZornF4Derivations` (`sp(3) ⊕ su(2)`). -/
def f4Compact : Submodule ℝ H3ZornF4Derivations :=
  LinearMap.ker (σF4.toLinearMap - LinearMap.id)

/-- `-1`-eigenspace (`28D`) of Cartan conjugation on `H3ZornF4Derivations`. -/
def f4Noncompact : Submodule ℝ H3ZornF4Derivations :=
  LinearMap.ker (σF4.toLinearMap + LinearMap.id)

@[simp] theorem mem_f4Compact_iff {D : H3ZornF4Derivations} :
    D ∈ f4Compact ↔ σF4 D = D := by
  change σF4 D - D = 0 ↔ σF4 D = D
  exact sub_eq_zero

@[simp] theorem mem_f4Noncompact_iff {D : H3ZornF4Derivations} :
    D ∈ f4Noncompact ↔ σF4 D = -D := by
  change σF4 D + D = 0 ↔ σF4 D = -D
  exact add_eq_zero_iff_eq_neg

theorem f4Compact_inf_f4Noncompact : f4Compact ⊓ f4Noncompact = ⊥ := by
  rw [eq_bot_iff]
  intro D hD
  rcases Submodule.mem_inf.mp hD with ⟨h1, h2⟩
  rw [mem_f4Compact_iff] at h1
  rw [mem_f4Noncompact_iff] at h2
  rw [Submodule.mem_bot]
  have h2D : (2 : ℝ) • D = 0 := by
    have hDneg : D = -D := h1.symm.trans h2
    calc (2 : ℝ) • D = D + D := two_smul ℝ D
      _ = D + (-D) := by nth_rw 2 [hDneg]
      _ = 0 := add_neg_cancel _
  exact (smul_eq_zero.mp h2D).resolve_left (by norm_num)

theorem f4Compact_sup_f4Noncompact : f4Compact ⊔ f4Noncompact = ⊤ := by
  rw [eq_top_iff]
  intro D _
  have hD : D = (1 / 2 : ℝ) • (D + σF4 D) + (1 / 2 : ℝ) • (D - σF4 D) := by module
  rw [hD]
  refine Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.smul_mem _ _ ?_))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ ?_))
  · rw [mem_f4Compact_iff, map_add, σF4_involutive, add_comm]
  · rw [mem_f4Noncompact_iff, map_sub, σF4_involutive, neg_sub]

private theorem σConjEnd_innerDeriv (u v : H3Zorn ℝ) :
    σConjEnd (h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ)) =
      (h3ZornJordanInnerDerivation (σH3 u) (σH3 v) : Module.End ℝ (H3Zorn ℝ)) := by
  apply LinearMap.ext; intro z
  simp only [σConjEnd_apply, h3ZornJordanInnerDerivation_apply,
    map_sub, σH3_mul, σH3_involutive]

private theorem inner12_on_diag1 (x y : ZornVectorMatrix ℝ) :
    (h3ZornJordanInnerDerivation (embedJ12 x) (embedJ12 y) : EndH3) h3_diag₁ = 0 := by
  rw [h3ZornJordanInnerDerivation_apply, mul_comm (embedJ12 x) h3_diag₁,
    mul_comm (embedJ12 y) h3_diag₁, h3_diag₁_mul_embedJ12, h3_diag₁_mul_embedJ12,
    mul_smul_comm, mul_smul_comm, embedJ12_mul_embedJ12, embedJ12_mul_embedJ12,
    zornBilin_symm y x, sub_self]

private theorem inner12_on_diag2 (x y : ZornVectorMatrix ℝ) :
    (h3ZornJordanInnerDerivation (embedJ12 x) (embedJ12 y) : EndH3) h3_diag₂ = 0 := by
  rw [h3ZornJordanInnerDerivation_apply, mul_comm (embedJ12 x) h3_diag₂,
    mul_comm (embedJ12 y) h3_diag₂, h3_diag₂_mul_embedJ12, h3_diag₂_mul_embedJ12,
    mul_smul_comm, mul_smul_comm, embedJ12_mul_embedJ12, embedJ12_mul_embedJ12,
    zornBilin_symm y x, sub_self]

private theorem inner12_on_diag3 (x y : ZornVectorMatrix ℝ) :
    (h3ZornJordanInnerDerivation (embedJ12 x) (embedJ12 y) : EndH3) h3_diag₃ = 0 := by
  rw [h3ZornJordanInnerDerivation_apply, mul_comm (embedJ12 x) h3_diag₃,
    mul_comm (embedJ12 y) h3_diag₃, h3_diag₃_mul_embedJ12, h3_diag₃_mul_embedJ12,
    mul_zero, mul_zero, sub_self]

private theorem peirceShiftEv_inner12 (x y : ZornVectorMatrix ℝ) :
    peirceShiftEv ⟨(h3ZornJordanInnerDerivation (embedJ12 x) (embedJ12 y) : EndH3),
        h3ZornJordanInnerDerivation_mem_F4 _ _⟩ = 0 := by
  change ((_ : EndH3) h3_diag₁ |>.a, (_ : EndH3) h3_diag₂ |>.b, (_ : EndH3) h3_diag₃ |>.c) = 0
  rw [inner12_on_diag1, inner12_on_diag2, inner12_on_diag3]
  rfl

private def shiftTriple (s : Fin 3 × Fin 4) (isNC : Bool) : ZornTriple :=
  let v := zornEigBasis (if isNC then ⟨s.2.val + 4, by omega⟩ else ⟨s.2.val, by omega⟩)
  match s.1 with
  | 0 => (v, 0, 0)
  | 1 => (0, v, 0)
  | 2 => (0, 0, v)

private theorem shiftTriple_linearIndependent (isNC : Bool) :
    LinearIndependent ℝ (fun s : Fin 3 × Fin 4 => shiftTriple s isNC) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  rcases s with ⟨k, j⟩
  have h_eq : ∀ r : Fin 3,
      (∑ i : Fin 4, c (r, i) • zornEigBasis
        (if isNC then ⟨i.val + 4, by omega⟩ else ⟨i.val, by omega⟩)) = 0 →
      c (r, j) = 0 := by
    intro r hsum
    have hinj : Function.Injective (fun i : Fin 4 =>
        if isNC then (⟨i.val + 4, by omega⟩ : Fin 8) else ⟨i.val, by omega⟩) := by
      intro a b hab
      cases isNC <;> simp only [Bool.false_eq_true, ↓reduceIte] at hab
      · ext; exact Fin.mk.inj hab
      · ext; have := Fin.mk.inj hab; omega
    have hli := zornEigBasis_linearIndependent.comp _ hinj
    rw [Fintype.linearIndependent_iff] at hli
    exact hli (fun i => c (r, i)) hsum j
  fin_cases k
  · have h0 : (∑ p : Fin 3 × Fin 4, c p •
        (match p.1 with
          | 0 => zornEigBasis (if isNC then ⟨p.2.val + 4, by omega⟩ else ⟨p.2.val, by omega⟩)
          | 1 => 0
          | 2 => 0)) = 0 := by
      have hfst := congrArg Prod.fst hc
      rw [Prod.fst_sum] at hfst
      simp only [Prod.smul_fst, shiftTriple] at hfst
      exact hfst
    rw [Fintype.sum_prod_type] at h0
    simp only [Fin.sum_univ_three, Fin.isValue, smul_zero, Finset.sum_const_zero, add_zero] at h0
    exact h_eq 0 h0
  · have h0 : (∑ p : Fin 3 × Fin 4, c p •
        (match p.1 with
          | 0 => 0
          | 1 => zornEigBasis (if isNC then ⟨p.2.val + 4, by omega⟩ else ⟨p.2.val, by omega⟩)
          | 2 => 0)) = 0 := by
      have hsnd := congrArg (fun p : ZornTriple => p.2.1) hc
      rw [Prod.snd_sum, Prod.fst_sum] at hsnd
      simp only [Prod.smul_snd, Prod.smul_fst, shiftTriple] at hsnd
      exact hsnd
    rw [Fintype.sum_prod_type] at h0
    simp only [Fin.sum_univ_three, Fin.isValue, smul_zero, Finset.sum_const_zero,
      zero_add, add_zero] at h0
    exact h_eq 1 h0
  · have h0 : (∑ p : Fin 3 × Fin 4, c p •
        (match p.1 with
          | 0 => 0
          | 1 => 0
          | 2 => zornEigBasis (if isNC then ⟨p.2.val + 4, by omega⟩ else ⟨p.2.val, by omega⟩))) = 0 := by
      have hsnd := congrArg (fun p : ZornTriple => p.2.2) hc
      rw [Prod.snd_sum] at hsnd
      simp only [Prod.smul_snd, shiftTriple] at hsnd
      exact hsnd
    rw [Fintype.sum_prod_type] at h0
    simp only [Fin.sum_univ_three, Fin.isValue, smul_zero, Finset.sum_const_zero, zero_add] at h0
    exact h_eq 2 h0

private def compactPair8 (k : Fin 12) : Fin 8 × Fin 8 :=
  match k with
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3) | 3 => (1, 2) | 4 => (1, 3) | 5 => (2, 3)
  | 6 => (4, 5) | 7 => (4, 6) | 8 => (4, 7) | 9 => (5, 6) | 10 => (5, 7) | 11 => (6, 7)

private theorem compactPair8_lt (k : Fin 12) : (compactPair8 k).1 < (compactPair8 k).2 := by
  fin_cases k <;> decide

private theorem compactPair8_inj : Function.Injective compactPair8 := by decide

private theorem compactPair8_sign (k : Fin 12) :
    ((compactPair8 k).1.val < 4 ∧ (compactPair8 k).2.val < 4) ∨
      (4 ≤ (compactPair8 k).1.val ∧ 4 ≤ (compactPair8 k).2.val) := by
  fin_cases k <;> decide

private def noncompactPair8 (k : Fin 16) : Fin 8 × Fin 8 :=
  (⟨k.val / 4, by omega⟩, ⟨k.val % 4 + 4, by omega⟩)

private theorem noncompactPair8_lt (k : Fin 16) :
    (noncompactPair8 k).1 < (noncompactPair8 k).2 := by
  fin_cases k <;> decide

private theorem noncompactPair8_inj : Function.Injective noncompactPair8 := by decide

private theorem noncompactPair8_sign (k : Fin 16) :
    (noncompactPair8 k).1.val < 4 ∧ 4 ≤ (noncompactPair8 k).2.val := by
  fin_cases k <;> decide

private theorem inner12_zornEigBasis_linearIndependent {n : ℕ}
    (pair : Fin n → Fin 8 × Fin 8)
    (hlt : ∀ k, (pair k).1 < (pair k).2)
    (hinj : Function.Injective pair) :
    LinearIndependent ℝ (fun k : Fin n =>
      (⟨(h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (pair k).1))
          (embedJ12 (zornEigBasis (pair k).2)) : EndH3),
        h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations)) := by
  rw [Fintype.linearIndependent_iff]
  intro d hd q
  have hev := congrArg (fun D : H3ZornF4Derivations =>
      zornBilin (zornEigBasis (pair q).1)
        ((D.1 (embedJ12 (zornEigBasis (pair q).2))).a)) hd
  have hzero : zornBilin (zornEigBasis (pair q).1)
      (((0 : H3ZornF4Derivations).1 (embedJ12 (zornEigBasis (pair q).2))).a) = 0 := by
    change zornBilin (zornEigBasis (pair q).1) (0 : H3Zorn ℝ).a = 0
    exact zornBilin_zero_right _
  rw [hzero] at hev
  have hsum : zornBilin (zornEigBasis (pair q).1)
      (((∑ k : Fin n, d k • (⟨(h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (pair k).1))
          (embedJ12 (zornEigBasis (pair k).2)) : EndH3),
        h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations)).1
        (embedJ12 (zornEigBasis (pair q).2))).a) =
      ∑ k : Fin n, d k * ((1 / 2 : ℝ) *
        (zornBilin (zornEigBasis (pair k).2) (zornEigBasis (pair q).2) *
           zornBilin (zornEigBasis (pair q).1) (zornEigBasis (pair k).1) -
         zornBilin (zornEigBasis (pair k).1) (zornEigBasis (pair q).2) *
           zornBilin (zornEigBasis (pair q).1) (zornEigBasis (pair k).2))) := by
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, H3Zorn.smul_readback, h3_sum_a, zornBilin_sum_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    change zornBilin _ ((d k) • _) = _
    rw [zornBilin_smul_right]
    congr 1
    rw [inner12_embedJ12_a, zornBilin_smul_right, zornBilin_sub_right,
      zornBilin_smul_right, zornBilin_smul_right]
  rw [hsum] at hev
  have hterm : ∀ k : Fin n, k ≠ q →
      zornBilin (zornEigBasis (pair k).2) (zornEigBasis (pair q).2) *
         zornBilin (zornEigBasis (pair q).1) (zornEigBasis (pair k).1) -
       zornBilin (zornEigBasis (pair k).1) (zornEigBasis (pair q).2) *
         zornBilin (zornEigBasis (pair q).1) (zornEigBasis (pair k).2) = 0 := by
    intro k hkq
    rw [zornBilin_zornEigBasis, zornBilin_zornEigBasis, zornBilin_zornEigBasis, zornBilin_zornEigBasis]
    have hne : pair k ≠ pair q := fun h => hkq (hinj h)
    have h1 : ¬ ((pair k).2 = (pair q).2 ∧ (pair q).1 = (pair k).1) := fun ⟨a, b⟩ =>
      hne (Prod.ext b.symm a)
    have h2 : ¬ ((pair k).1 = (pair q).2 ∧ (pair q).1 = (pair k).2) := fun ⟨a, b⟩ => by
      have hk := hlt k; have hq := hlt q; omega
    split_ifs <;> try simp_all
  rw [Finset.sum_eq_single q (fun k _ hkq => by rw [hterm k hkq, mul_zero, mul_zero])
      (fun hq => absurd (Finset.mem_univ q) hq)] at hev
  simp_rw [zornBilin_zornEigBasis] at hev
  have hltq := hlt q
  have hne1 : (pair q).1 ≠ (pair q).2 := ne_of_lt hltq
  simp only [hne1, ite_true, ite_false, zero_mul, sub_zero] at hev
  by_cases h1 : (pair q).1.val < 4 <;> by_cases h2 : (pair q).2.val < 4 <;>
    simp only [h1, h2, ite_true, ite_false] at hev <;> linarith

private theorem f4_mixed_linearIndependent {n : ℕ}
    (isNC : Bool)
    (pair : Fin n → Fin 8 × Fin 8)
    (hlt : ∀ k, (pair k).1 < (pair k).2)
    (hinj : Function.Injective pair) :
    LinearIndependent ℝ (Sum.elim
      (fun s : Fin 3 × Fin 4 => peirceShiftSection (shiftTriple s isNC))
      (fun k : Fin n =>
        (⟨(h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (pair k).1))
            (embedJ12 (zornEigBasis (pair k).2)) : EndH3),
          h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc idx
  have hsplit : (∑ s : Fin 3 × Fin 4, c (Sum.inl s) • peirceShiftSection (shiftTriple s isNC)) +
      (∑ k : Fin n, c (Sum.inr k) •
        (⟨(h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (pair k).1))
            (embedJ12 (zornEigBasis (pair k).2)) : EndH3),
          h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations)) = 0 := by
    rw [Fintype.sum_sum_type] at hc; exact hc
  have hev0 := congrArg peirceShiftEv hsplit
  simp only [map_add, map_sum, map_smul, map_zero, peirceShiftEv_section,
    peirceShiftEv_inner12, smul_zero, Finset.sum_const_zero, add_zero] at hev0
  have hc_inl : ∀ s : Fin 3 × Fin 4, c (Sum.inl s) = 0 := by
    have hli := shiftTriple_linearIndependent isNC
    rw [Fintype.linearIndependent_iff] at hli
    exact hli (fun s => c (Sum.inl s)) hev0
  have hrest : (∑ k : Fin n, c (Sum.inr k) •
      (⟨(h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (pair k).1))
          (embedJ12 (zornEigBasis (pair k).2)) : EndH3),
        h3ZornJordanInnerDerivation_mem_F4 _ _⟩ : H3ZornF4Derivations)) = 0 := by
    rw [Finset.sum_congr rfl (fun s _ => by rw [hc_inl s, zero_smul]),
      Finset.sum_const_zero, zero_add] at hsplit
    exact hsplit
  have hc_inr : ∀ k : Fin n, c (Sum.inr k) = 0 := by
    have hli := inner12_zornEigBasis_linearIndependent pair hlt hinj
    rw [Fintype.linearIndependent_iff] at hli
    exact hli (fun k => c (Sum.inr k)) hrest
  cases idx with
  | inl s => exact hc_inl s
  | inr k => exact hc_inr k

private theorem σZorn_zvmZero : σZorn ZornVectorMatrix.zero = ZornVectorMatrix.zero := σZorn_zero

private theorem σH3_h3_diag1 : σH3 h3_diag₁ = h3_diag₁ := by
  apply H3Zorn.ext_h3 <;> simp [h3_diag₁, σZorn_zvmZero]

private theorem σH3_h3_diag2 : σH3 h3_diag₂ = h3_diag₂ := by
  apply H3Zorn.ext_h3 <;> simp [h3_diag₂, σZorn_zvmZero]

private theorem σH3_embedJ12 (u : ZornVectorMatrix ℝ) :
    σH3 (embedJ12 u) = embedJ12 (σZorn u) := by
  apply H3Zorn.ext_h3 <;> simp [embedJ12, σZorn_zvmZero]

private theorem σH3_embedJ23 (u : ZornVectorMatrix ℝ) :
    σH3 (embedJ23 u) = embedJ23 (σZorn u) := by
  apply H3Zorn.ext_h3 <;> simp [embedJ23, σZorn_zvmZero]

private theorem σH3_embedJ31 (u : ZornVectorMatrix ℝ) :
    σH3 (embedJ31 u) = embedJ31 (σZorn u) := by
  apply H3Zorn.ext_h3 <;> simp [embedJ31, σZorn_zvmZero]

private theorem innerDeriv_neg_left (u v : H3Zorn ℝ) :
    (h3ZornJordanInnerDerivation (-u) v : Module.End ℝ (H3Zorn ℝ)) =
      -(h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ)) := by
  apply LinearMap.ext; intro z
  simp [h3ZornJordanInnerDerivation_apply, sub_eq_add_neg, add_comm]

private theorem innerDeriv_neg_right (u v : H3Zorn ℝ) :
    (h3ZornJordanInnerDerivation u (-v) : Module.End ℝ (H3Zorn ℝ)) =
      -(h3ZornJordanInnerDerivation u v : Module.End ℝ (H3Zorn ℝ)) := by
  apply LinearMap.ext; intro z
  simp [h3ZornJordanInnerDerivation_apply, sub_eq_add_neg, add_comm]

private theorem embedJ12_neg (u : ZornVectorMatrix ℝ) : embedJ12 (-u) = -embedJ12 u := by
  have h1 : (0 : ℝ) = -0 := neg_zero.symm
  have hz : (ZornVectorMatrix.zero : ZornVectorMatrix ℝ) = -ZornVectorMatrix.zero := neg_zero.symm
  apply H3Zorn.ext_h3
  · exact h1
  · exact h1
  · exact h1
  · rfl
  · exact hz
  · exact hz

private theorem σF4_peirceShiftSection (p : ZornTriple) :
    σF4 (peirceShiftSection p) = peirceShiftSection (σZorn p.1, σZorn p.2.1, σZorn p.2.2) := by
  apply Subtype.ext
  rw [σF4_coe]
  dsimp [peirceShiftSection]
  rw [map_add, map_add, map_smul, map_smul, map_smul,
    σConjEnd_innerDeriv, σConjEnd_innerDeriv, σConjEnd_innerDeriv,
    σH3_h3_diag1, σH3_h3_diag2, σH3_embedJ12, σH3_embedJ23, σH3_embedJ31]

theorem finrank_f4Compact : Module.finrank ℝ f4Compact = 24 := by
  let fam : (Fin 3 × Fin 4) ⊕ Fin 12 → H3ZornF4Derivations := Sum.elim
    (fun s => peirceShiftSection (shiftTriple s false))
    (fun k => ⟨(h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (compactPair8 k).1))
        (embedJ12 (zornEigBasis (compactPair8 k).2)) : EndH3),
      h3ZornJordanInnerDerivation_mem_F4 _ _⟩)
  have hmemC : ∀ idx, fam idx ∈ f4Compact := by
    intro idx
    rw [mem_f4Compact_iff]
    cases idx with
    | inl s =>
      simp only [fam, Sum.elim_inl, σF4_peirceShiftSection]
      rcases s with ⟨k, j⟩
      have hσ : σZorn (zornEigBasis ⟨j.val, by omega⟩) = zornEigBasis ⟨j.val, by omega⟩ := by
        rw [σZorn_zornEigBasis]; simp [j.isLt]
      fin_cases k
      · dsimp [shiftTriple]; rw [hσ, σZorn_zvmZero]
      · dsimp [shiftTriple]; rw [hσ, σZorn_zvmZero]
      · dsimp [shiftTriple]; rw [hσ, σZorn_zvmZero]
    | inr k =>
      dsimp [fam]
      apply Subtype.ext
      rw [σF4_coe, σConjEnd_innerDeriv, σH3_embedJ12, σH3_embedJ12,
        σZorn_zornEigBasis, σZorn_zornEigBasis]
      rcases compactPair8_sign k with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [h1, h2, ite_true]
      · have h1' : ¬ (compactPair8 k).1.val < 4 := by omega
        have h2' : ¬ (compactPair8 k).2.val < 4 := by omega
        simp only [h1', h2', ite_false]
        change (h3ZornJordanInnerDerivation (embedJ12 (-zornEigBasis (compactPair8 k).1))
          (embedJ12 (-zornEigBasis (compactPair8 k).2)) : EndH3) = _
        rw [embedJ12_neg, embedJ12_neg, innerDeriv_neg_left, innerDeriv_neg_right, neg_neg]
  let famC : (Fin 3 × Fin 4) ⊕ Fin 12 → f4Compact := fun idx => ⟨fam idx, hmemC idx⟩
  have hliC : LinearIndependent ℝ famC := by
    have hcomp : f4Compact.subtype ∘ famC = fam := rfl
    have hli : LinearIndependent ℝ (f4Compact.subtype ∘ famC) := by
      rw [hcomp]
      exact f4_mixed_linearIndependent false compactPair8 compactPair8_lt compactPair8_inj
    exact hli.of_comp f4Compact.subtype
  have hgeC : 24 ≤ Module.finrank ℝ f4Compact := by
    have hcard : Fintype.card ((Fin 3 × Fin 4) ⊕ Fin 12) = 24 := by decide
    simpa [hcard] using hliC.fintype_card_le_finrank
  let famP_raw : (Fin 3 × Fin 4) ⊕ Fin 16 → H3ZornF4Derivations := Sum.elim
    (fun s => peirceShiftSection (shiftTriple s true))
    (fun k => ⟨(h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (noncompactPair8 k).1))
        (embedJ12 (zornEigBasis (noncompactPair8 k).2)) : EndH3),
      h3ZornJordanInnerDerivation_mem_F4 _ _⟩)
  have hmemP : ∀ idx, famP_raw idx ∈ f4Noncompact := by
    intro idx
    rw [mem_f4Noncompact_iff]
    cases idx with
    | inl s =>
      simp only [famP_raw, Sum.elim_inl, σF4_peirceShiftSection]
      rcases s with ⟨k, j⟩
      have hσ : σZorn (zornEigBasis ⟨j.val + 4, by omega⟩) = -zornEigBasis ⟨j.val + 4, by omega⟩ := by
        rw [σZorn_zornEigBasis]
        have hlt : ¬ ((⟨j.val + 4, by omega⟩ : Fin 8).val < 4) := by simp
        simp only [hlt, ite_false]
      have hz0 : (-ZornVectorMatrix.zero : ZornVectorMatrix ℝ) = ZornVectorMatrix.zero := neg_zero
      have hneg_sec : ∀ p : ZornTriple, peirceShiftSection (-p) = -peirceShiftSection p := fun p =>
        map_neg peirceShiftSection p
      fin_cases k
      · dsimp [shiftTriple]; rw [hσ, σZorn_zvmZero, ← hneg_sec]; simp [hz0]
      · dsimp [shiftTriple]; rw [hσ, σZorn_zvmZero, ← hneg_sec]; simp [hz0]
      · dsimp [shiftTriple]; rw [hσ, σZorn_zvmZero, ← hneg_sec]; simp [hz0]
    | inr k =>
      dsimp [famP_raw]
      apply Subtype.ext
      rw [σF4_coe, σConjEnd_innerDeriv, σH3_embedJ12, σH3_embedJ12,
        σZorn_zornEigBasis, σZorn_zornEigBasis]
      rcases noncompactPair8_sign k with ⟨h1, h2⟩
      have h2' : ¬ (noncompactPair8 k).2.val < 4 := by omega
      simp only [h1, h2', ite_true, ite_false]
      change (h3ZornJordanInnerDerivation (embedJ12 (zornEigBasis (noncompactPair8 k).1))
        (embedJ12 (-zornEigBasis (noncompactPair8 k).2)) : EndH3) = _
      rw [embedJ12_neg, innerDeriv_neg_right]; rfl
  let famP : (Fin 3 × Fin 4) ⊕ Fin 16 → f4Noncompact := fun idx => ⟨famP_raw idx, hmemP idx⟩
  have hliP : LinearIndependent ℝ famP := by
    have hcomp : f4Noncompact.subtype ∘ famP = famP_raw := rfl
    have hli : LinearIndependent ℝ (f4Noncompact.subtype ∘ famP) := by
      rw [hcomp]
      exact f4_mixed_linearIndependent true noncompactPair8 noncompactPair8_lt noncompactPair8_inj
    exact hli.of_comp f4Noncompact.subtype
  have hgeP : 28 ≤ Module.finrank ℝ f4Noncompact := by
    have hcard : Fintype.card ((Fin 3 × Fin 4) ⊕ Fin 16) = 28 := by decide
    simpa [hcard] using hliP.fintype_card_le_finrank
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq f4Compact f4Noncompact
  rw [f4Compact_sup_f4Noncompact, f4Compact_inf_f4Noncompact, finrank_top, finrank_bot,
    add_zero, finrank_H3ZornF4Derivations] at hsum
  omega

theorem finrank_f4Noncompact : Module.finrank ℝ f4Noncompact = 28 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq f4Compact f4Noncompact
  rw [f4Compact_sup_f4Noncompact, f4Compact_inf_f4Noncompact, finrank_top, finrank_bot,
    add_zero, finrank_H3ZornF4Derivations, finrank_f4Compact] at hsum
  omega

/-- `+1`-eigenspace (`63D`) of `θE7` on `H3ZornTKKLie` (`su(8)`). -/
def e7Compact : LieSubalgebra ℝ H3ZornTKKLie where
  carrier := {X | θE7 X = X}
  zero_mem' := map_zero θE7
  add_mem' {X Y} hX hY := by change θE7 (X + Y) = X + Y; rw [map_add, hX, hY]
  smul_mem' r {X} hX := by change θE7 (r • X) = r • X; rw [map_smul, hX]
  lie_mem' {X Y} hX hY := by change θE7 ⁅X, Y⁆ = ⁅X, Y⁆; rw [LieEquiv.map_lie, hX, hY]

/-- `-1`-eigenspace (`70D`) of `θE7` on `H3ZornTKKLie`. -/
def e7Noncompact : Submodule ℝ H3ZornTKKLie :=
  LinearMap.ker (θE7.toLinearEquiv.toLinearMap + LinearMap.id)

@[simp] theorem mem_e7Compact_iff {X : H3ZornTKKLie} : X ∈ e7Compact ↔ θE7 X = X := Iff.rfl

@[simp] theorem mem_e7Noncompact_iff {X : H3ZornTKKLie} : X ∈ e7Noncompact ↔ θE7 X = -X := by
  change θE7 X + X = 0 ↔ θE7 X = -X
  exact add_eq_zero_iff_eq_neg

private theorem deriv_add_lmul_mem_str (D : H3ZornF4Derivations) (a : H3Zorn ℝ) :
    D.1 + jordanLmul (R := ℝ) a ∈ h3zornTKKDatum.str :=
  ⟨⟨D.1, D.2⟩, a, rfl⟩

private def e7CompactEquiv : e7Compact ≃ₗ[ℝ] H3Zorn ℝ × f4Compact × h3Noncompact where
  toFun X :=
    (X.1.neg,
     ⟨tkk5StrDerivPart X.1.zero, mem_f4Compact_iff.mpr (by
       have h0 := congrArg (fun Y : H3ZornTKKLie => Y.zero) (mem_e7Compact_iff.mp X.2)
       have hD := congrArg tkk5StrDerivPart h0
       change tkk5StrDerivPart ⟨-σConjEnd (h3zornTraceAdjoint X.1.zero.1), _⟩ = tkk5StrDerivPart X.1.zero at hD
       rw [strDerivPart_θE7] at hD
       exact hD)⟩,
     ⟨tkk5StrLmulPart X.1.zero, mem_h3Noncompact_iff.mpr (by
       have h0 := congrArg (fun Y : H3ZornTKKLie => Y.zero) (mem_e7Compact_iff.mp X.2)
       have ha := congrArg tkk5StrLmulPart h0
       change tkk5StrLmulPart ⟨-σConjEnd (h3zornTraceAdjoint X.1.zero.1), _⟩ = tkk5StrLmulPart X.1.zero at ha
       rw [strLmulPart_θE7] at ha
       exact neg_eq_iff_eq_neg.mp ha)⟩)
  invFun p :=
    ⟨⟨p.1, ⟨p.2.1.1.1 + jordanLmul (R := ℝ) p.2.2.1, deriv_add_lmul_mem_str p.2.1.1 p.2.2.1⟩, -σH3 p.1⟩,
      mem_e7Compact_iff.mpr (by
        have hD := mem_f4Compact_iff.mp p.2.1.2
        have ha := mem_h3Noncompact_iff.mp p.2.2.2
        apply h3zornTKKLie_ext
        · simp [σH3_involutive]
        · apply Subtype.ext
          rw [θE7_zero_coe]
          let D : H3ZornF4Derivations := p.2.1.1
          let a : H3Zorn ℝ := p.2.2.1
          have hadjD : h3zornTraceAdjoint D.1 = -D.1 := h3zornTraceAdjoint_derivation D
          have hadj : h3zornTraceAdjoint (D.1 + jordanLmul (R := ℝ) a) =
              -D.1 + jordanLmul (R := ℝ) a := by
            rw [show h3zornTraceAdjoint (D.1 + jordanLmul (R := ℝ) a) =
                h3zornTraceAdjointLM (D.1 + jordanLmul (R := ℝ) a) from rfl,
              map_add, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
              hadjD, h3zornTraceAdjoint_jordanLmul]
          change -σConjEnd (h3zornTraceAdjoint (D.1 + jordanLmul (R := ℝ) a)) =
            D.1 + jordanLmul (R := ℝ) a
          rw [hadj, map_add, map_neg, neg_add, neg_neg, ← σF4_coe, hD]
          have hjm : σConjEnd (jordanLmul (R := ℝ) a) = jordanLmul (R := ℝ) (σH3 a) := by
            apply LinearMap.ext; intro z; simp [σConjEnd_apply, jordanLmul_apply, σH3_mul, σH3_involutive]
          rw [hjm, ha, show jordanLmul (R := ℝ) (-a) = -jordanLmul (R := ℝ) a by
            apply LinearMap.ext; intro z; simp [jordanLmul_apply, neg_mul]]
          rw [neg_neg]
        · simp)⟩
  left_inv X := by
    apply Subtype.ext
    have hpos : -σH3 X.1.neg = X.1.pos := by
      have hp := congrArg (fun Y : H3ZornTKKLie => Y.pos) (mem_e7Compact_iff.mp X.2)
      rw [θE7_pos] at hp; exact hp
    apply h3zornTKKLie_ext
    · rfl
    · apply Subtype.ext
      change (tkk5StrDerivPart X.1.zero).1 + jordanLmul (R := ℝ) (tkk5StrLmulPart X.1.zero) = X.1.zero.1
      rw [tkk5StrDerivPart_coe, sub_add_cancel]
    · exact hpos
  right_inv p := by
    rcases p with ⟨c, ⟨D, hD⟩, ⟨a, ha⟩⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext; apply Subtype.ext
        change (tkk5StrDerivPart ⟨D.1 + jordanLmul (R := ℝ) a, deriv_add_lmul_mem_str D a⟩).1 = D.1
        rw [tkk5StrDerivPart_coe]
        have hl : tkk5StrLmulPart ⟨D.1 + jordanLmul (R := ℝ) a, deriv_add_lmul_mem_str D a⟩ = a := by
          change (D.1 + jordanLmul (R := ℝ) a) 1 = a
          rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero D,
            zero_add]
          exact candidateJordanMul_one_right a
        rw [hl, add_sub_cancel_right]
      · apply Subtype.ext
        change (D.1 + jordanLmul (R := ℝ) a) 1 = a
        rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero D, zero_add]
        exact candidateJordanMul_one_right a
  map_add' _ _ := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> simp [tkk5StrDerivPart_add, map_add]
  map_smul' _ _ := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> simp [tkk5StrDerivPart_smul, map_smul]

private def e7NoncompactEquiv : e7Noncompact ≃ₗ[ℝ] H3Zorn ℝ × f4Noncompact × h3Compact where
  toFun X :=
    (X.1.neg,
     ⟨tkk5StrDerivPart X.1.zero, mem_f4Noncompact_iff.mpr (by
       have h0 := congrArg (fun Y : H3ZornTKKLie => Y.zero) (mem_e7Noncompact_iff.mp X.2)
       have hneg0 : (-X.1).zero = -X.1.zero := rfl
       rw [hneg0] at h0
       have hD := congrArg tkk5StrDerivPart h0
       change tkk5StrDerivPart ⟨-σConjEnd (h3zornTraceAdjoint X.1.zero.1), _⟩ = tkk5StrDerivPart (-X.1.zero) at hD
       rw [strDerivPart_θE7] at hD
       have hnegD : tkk5StrDerivPart (-X.1.zero) = -tkk5StrDerivPart X.1.zero := by
         rw [← neg_one_smul ℝ X.1.zero, tkk5StrDerivPart_smul, neg_one_smul]
       rw [hnegD] at hD
       exact hD)⟩,
     ⟨tkk5StrLmulPart X.1.zero, mem_h3Compact_iff.mpr (by
       have h0 := congrArg (fun Y : H3ZornTKKLie => Y.zero) (mem_e7Noncompact_iff.mp X.2)
       have hneg0 : (-X.1).zero = -X.1.zero := rfl
       rw [hneg0] at h0
       have ha := congrArg tkk5StrLmulPart h0
       change tkk5StrLmulPart ⟨-σConjEnd (h3zornTraceAdjoint X.1.zero.1), _⟩ = tkk5StrLmulPart (-X.1.zero) at ha
       rw [strLmulPart_θE7, map_neg] at ha
       exact neg_inj.mp ha)⟩)
  invFun p :=
    ⟨⟨p.1, ⟨p.2.1.1.1 + jordanLmul (R := ℝ) p.2.2.1, deriv_add_lmul_mem_str p.2.1.1 p.2.2.1⟩, σH3 p.1⟩,
      mem_e7Noncompact_iff.mpr (by
        have hD := mem_f4Noncompact_iff.mp p.2.1.2
        have ha := mem_h3Compact_iff.mp p.2.2.2
        apply h3zornTKKLie_ext
        · simp [σH3_involutive]
        · apply Subtype.ext
          let D : H3ZornF4Derivations := p.2.1.1
          let a : H3Zorn ℝ := p.2.2.1
          have hneg0 : (-⟨p.1, ⟨D.1 + jordanLmul (R := ℝ) a,
              deriv_add_lmul_mem_str D a⟩, σH3 p.1⟩ : H3ZornTKKLie).zero =
              -⟨D.1 + jordanLmul (R := ℝ) a, deriv_add_lmul_mem_str D a⟩ := rfl
          rw [θE7_zero_coe, hneg0]
          have hadjD : h3zornTraceAdjoint D.1 = -D.1 := h3zornTraceAdjoint_derivation D
          have hadj : h3zornTraceAdjoint (D.1 + jordanLmul (R := ℝ) a) =
              -D.1 + jordanLmul (R := ℝ) a := by
            rw [show h3zornTraceAdjoint (D.1 + jordanLmul (R := ℝ) a) =
                h3zornTraceAdjointLM (D.1 + jordanLmul (R := ℝ) a) from rfl,
              map_add, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
              hadjD, h3zornTraceAdjoint_jordanLmul]
          change -σConjEnd (h3zornTraceAdjoint (D.1 + jordanLmul (R := ℝ) a)) =
            -(D.1 + jordanLmul (R := ℝ) a)
          rw [hadj, map_add, map_neg, neg_add, neg_neg, ← σF4_coe, hD,
            show (-D).1 = -D.1 from rfl]
          have hjm : σConjEnd (jordanLmul (R := ℝ) a) = jordanLmul (R := ℝ) (σH3 a) := by
            apply LinearMap.ext; intro z; simp [σConjEnd_apply, jordanLmul_apply, σH3_mul, σH3_involutive]
          rw [hjm, ha, neg_add]
        · simp)⟩
  left_inv X := by
    apply Subtype.ext
    have hpos : σH3 X.1.neg = X.1.pos := by
      have hp := congrArg (fun Y : H3ZornTKKLie => Y.pos) (mem_e7Noncompact_iff.mp X.2)
      have hnegp : (-X.1).pos = -X.1.pos := rfl
      rw [θE7_pos, hnegp, neg_inj] at hp; exact hp
    apply h3zornTKKLie_ext
    · rfl
    · apply Subtype.ext
      change (tkk5StrDerivPart X.1.zero).1 + jordanLmul (R := ℝ) (tkk5StrLmulPart X.1.zero) = X.1.zero.1
      rw [tkk5StrDerivPart_coe, sub_add_cancel]
    · exact hpos
  right_inv p := by
    rcases p with ⟨c, ⟨D, hD⟩, ⟨a, ha⟩⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext; apply Subtype.ext
        change (tkk5StrDerivPart ⟨D.1 + jordanLmul (R := ℝ) a, deriv_add_lmul_mem_str D a⟩).1 = D.1
        rw [tkk5StrDerivPart_coe]
        have hl : tkk5StrLmulPart ⟨D.1 + jordanLmul (R := ℝ) a, deriv_add_lmul_mem_str D a⟩ = a := by
          change (D.1 + jordanLmul (R := ℝ) a) 1 = a
          rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero D,
            zero_add]
          exact candidateJordanMul_one_right a
        rw [hl, add_sub_cancel_right]
      · apply Subtype.ext
        change (D.1 + jordanLmul (R := ℝ) a) 1 = a
        rw [LinearMap.add_apply, jordanLmul_apply, h3ZornF4_derivation_apply_one_eq_zero D,
          zero_add]
        exact candidateJordanMul_one_right a
  map_add' _ _ := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> simp [tkk5StrDerivPart_add, map_add]
  map_smul' _ _ := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> simp [tkk5StrDerivPart_smul, map_smul]

theorem finrank_e7Compact : Module.finrank ℝ e7Compact = 63 := by
  rw [LinearEquiv.finrank_eq e7CompactEquiv, Module.finrank_prod, Module.finrank_prod,
    finrank_h3zorn, finrank_f4Compact, finrank_h3Noncompact]

theorem finrank_e7Noncompact : Module.finrank ℝ e7Noncompact = 70 := by
  rw [LinearEquiv.finrank_eq e7NoncompactEquiv, Module.finrank_prod, Module.finrank_prod,
    finrank_h3zorn, finrank_f4Noncompact, finrank_h3Compact]

/-- The `120D` compact Cartan subalgebra `k = {U | θ₅ U = U}` (`so(16)`) of `FreudenthalTKK5E8`. -/
def tkk5E8CartanCompact : LieSubalgebra ℝ FreudenthalTKK5E8 where
  carrier := {U | θ₅ U = U}
  zero_mem' := map_zero θ₅
  add_mem' {U V} hU hV := by change θ₅ (U + V) = U + V; rw [map_add, hU, hV]
  smul_mem' r {U} hU := by change θ₅ (r • U) = r • U; rw [map_smul, hU]
  lie_mem' {U V} hU hV := by change θ₅ ⁅U, V⁆ = ⁅U, V⁆; rw [LieEquiv.map_lie, hU, hV]

/-- The `128D` non-compact Cartan complement `p = {U | θ₅ U = -U}` of `FreudenthalTKK5E8`. -/
def tkk5E8CartanNoncompact : Submodule ℝ FreudenthalTKK5E8 :=
  LinearMap.ker (θ₅.toLinearEquiv.toLinearMap + LinearMap.id)

@[simp] theorem mem_tkk5E8CartanCompact_iff {U : FreudenthalTKK5E8} :
    U ∈ tkk5E8CartanCompact ↔ θ₅ U = U := Iff.rfl

@[simp] theorem mem_tkk5E8CartanNoncompact_iff {U : FreudenthalTKK5E8} :
    U ∈ tkk5E8CartanNoncompact ↔ θ₅ U = -U := by
  change θ₅ U + U = 0 ↔ θ₅ U = -U
  exact add_eq_zero_iff_eq_neg

private theorem sq2_mul_half : Real.sqrt 2 * Real.sqrt 2 * (1 / 2 : ℝ) = 1 := by
  rw [Real.mul_self_sqrt (by norm_num)]; norm_num

private def tkk5E8CartanCompactEquiv :
    tkk5E8CartanCompact ≃ₗ[ℝ] ℝ × Charge × e7Compact where
  toFun U :=
    (U.1.gMinus2, U.1.gMinus1,
     ⟨U.1.gZeroE7, mem_e7Compact_iff.mpr (congrArg FreudenthalTKK5E8.gZeroE7 (mem_tkk5E8CartanCompact_iff.mp U.2))⟩)
  invFun p :=
    ⟨⟨p.1, p.2.1, p.2.2.1, 0, -(Real.sqrt 2) • σC p.2.1, -p.1⟩,
      mem_tkk5E8CartanCompact_iff.mpr (by
        have hc : Real.sqrt 2 * -(Real.sqrt 2) * -(1 / 2 : ℝ) = 1 := by
          rw [mul_neg, mul_neg, neg_mul, neg_neg, sq2_mul_half]
        apply FreudenthalTKK5E8.ext
        · simp [θ₅_gMinus2]
        · rw [θ₅_gMinus1, map_smul, σC_sq, smul_smul, smul_smul, hc, one_smul]
        · simp only [θ₅_gZeroE7, mem_e7Compact_iff.mp p.2.2.2]
        · simp [θ₅_gZeroCenter]
        · simp [θ₅_gPlus1]
        · simp [θ₅_gPlus2])⟩
  left_inv U := by
    have hU := mem_tkk5E8CartanCompact_iff.mp U.2
    have hzc : U.1.gZeroCenter = 0 := by
      have h := congrArg FreudenthalTKK5E8.gZeroCenter hU
      rw [θ₅_gZeroCenter] at h; linarith
    have hp1 : U.1.gPlus1 = -(Real.sqrt 2) • σC U.1.gMinus1 := by
      have h := congrArg FreudenthalTKK5E8.gPlus1 hU
      rw [θ₅_gPlus1] at h; exact h.symm
    have hp2 : U.1.gPlus2 = -U.1.gMinus2 := by
      have h := congrArg FreudenthalTKK5E8.gPlus2 hU
      rw [θ₅_gPlus2] at h; exact h.symm
    apply Subtype.ext
    exact FreudenthalTKK5E8.ext rfl rfl rfl hzc.symm hp1.symm hp2.symm
  right_inv p := by rcases p with ⟨w, Q, X⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tkk5E8CartanNoncompactEquiv :
    tkk5E8CartanNoncompact ≃ₗ[ℝ] ℝ × Charge × ℝ × e7Noncompact where
  toFun U :=
    (U.1.gMinus2, U.1.gMinus1, U.1.gZeroCenter,
     ⟨U.1.gZeroE7, mem_e7Noncompact_iff.mpr (congrArg FreudenthalTKK5E8.gZeroE7 (mem_tkk5E8CartanNoncompact_iff.mp U.2))⟩)
  invFun p :=
    ⟨⟨p.1, p.2.1, p.2.2.2.1, p.2.2.1, Real.sqrt 2 • σC p.2.1, p.1⟩,
      mem_tkk5E8CartanNoncompact_iff.mpr (by
        have hgm1 : (-⟨p.1, p.2.1, p.2.2.2.1, p.2.2.1, Real.sqrt 2 • σC p.2.1, p.1⟩ :
            FreudenthalTKK5E8).gMinus1 = -p.2.1 := rfl
        have hgzE7 : (-⟨p.1, p.2.1, p.2.2.2.1, p.2.2.1, Real.sqrt 2 • σC p.2.1, p.1⟩ :
            FreudenthalTKK5E8).gZeroE7 = -p.2.2.2.1 := rfl
        have hc : Real.sqrt 2 * Real.sqrt 2 * -(1 / 2 : ℝ) = -1 := by
          rw [mul_neg, sq2_mul_half]
        apply FreudenthalTKK5E8.ext
        · simp [θ₅_gMinus2]
        · rw [θ₅_gMinus1, hgm1, map_smul, σC_sq, smul_smul, smul_smul, hc, neg_one_smul]
        · rw [θ₅_gZeroE7, hgzE7, mem_e7Noncompact_iff.mp p.2.2.2.2]
        · simp [θ₅_gZeroCenter]
        · simp [θ₅_gPlus1]
        · simp [θ₅_gPlus2])⟩
  left_inv U := by
    have hU := mem_tkk5E8CartanNoncompact_iff.mp U.2
    have hp1 : U.1.gPlus1 = Real.sqrt 2 • σC U.1.gMinus1 := by
      have h := congrArg FreudenthalTKK5E8.gPlus1 hU
      rw [θ₅_gPlus1] at h
      have hn : (-U.1).gPlus1 = -U.1.gPlus1 := rfl
      rw [hn, neg_smul] at h
      exact neg_inj.mp h.symm
    have hp2 : U.1.gPlus2 = U.1.gMinus2 := by
      have h := congrArg FreudenthalTKK5E8.gPlus2 hU
      rw [θ₅_gPlus2] at h
      have hn : (-U.1).gPlus2 = -U.1.gPlus2 := rfl
      rw [hn] at h; linarith
    apply Subtype.ext
    exact FreudenthalTKK5E8.ext rfl rfl rfl rfl hp1.symm hp2.symm
  right_inv p := by rcases p with ⟨w, Q, c, X⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_tkk5E8CartanCompact : Module.finrank ℝ tkk5E8CartanCompact = 120 := by
  rw [LinearEquiv.finrank_eq tkk5E8CartanCompactEquiv, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self, finrank_charge, finrank_e7Compact]

theorem finrank_tkk5E8CartanNoncompact : Module.finrank ℝ tkk5E8CartanNoncompact = 128 := by
  rw [LinearEquiv.finrank_eq tkk5E8CartanNoncompactEquiv, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_prod, Module.finrank_self, finrank_charge, finrank_e7Noncompact]

theorem freudenthalTKK5E8_cartan_signature_eq_pos_8 :
    (Module.finrank ℝ tkk5E8CartanNoncompact : ℤ) - Module.finrank ℝ tkk5E8CartanCompact = 8 := by
  rw [finrank_tkk5E8CartanNoncompact, finrank_tkk5E8CartanCompact]
  norm_num

private theorem cartanInner5_ad_skew_on_compact {Z : FreudenthalTKK5E8}
    (hZ : Z ∈ tkk5E8CartanCompact) (X Y : FreudenthalTKK5E8) :
    cartanInner5 ⁅Z, X⁆ Y + cartanInner5 X ⁅Z, Y⁆ = 0 := by
  rw [mem_tkk5E8CartanCompact_iff] at hZ
  rw [cartanInner5_apply, cartanInner5_apply, LieEquiv.map_lie, hZ]
  have hinv := B₅_lieInvariant Z X (θ₅ Y)
  linarith

private theorem cartanInner5_ad_self_on_noncompact {Z : FreudenthalTKK5E8}
    (hZ : Z ∈ tkk5E8CartanNoncompact) (X Y : FreudenthalTKK5E8) :
    cartanInner5 ⁅Z, X⁆ Y = cartanInner5 X ⁅Z, Y⁆ := by
  rw [mem_tkk5E8CartanNoncompact_iff] at hZ
  rw [cartanInner5_apply, cartanInner5_apply, LieEquiv.map_lie, hZ, neg_lie, map_neg, neg_neg]
  have hinv := B₅_lieInvariant Z X (θ₅ Y)
  linarith

private theorem trace_sq_nonpos_of_skew_ortho
    (A : Module.End ℝ FreudenthalTKK5E8)
    (hskew : ∀ X Y, cartanInner5 (A X) Y + cartanInner5 X (A Y) = 0) :
    LinearMap.trace ℝ FreudenthalTKK5E8 (A * A) ≤ 0 ∧
      (LinearMap.trace ℝ FreudenthalTKK5E8 (A * A) = 0 → A = 0) := by
  have : FiniteDimensional ℝ FreudenthalTKK5E8 := inferInstance
  have hsymm5 : LinearMap.IsSymm cartanInner5 := ⟨cartanInner5_symm⟩
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (B := cartanInner5) hsymm5
  have hpos : ∀ i, 0 < cartanInner5 (v i) (v i) := fun i =>
    lt_of_le_of_ne (cartanInner5_nonneg (v i))
      (fun h => (v.ne_zero i) ((cartanInner5_eq_zero_iff (v i)).mp h.symm))
  have hrepr : ∀ i (W : FreudenthalTKK5E8),
      v.repr W i = cartanInner5 (v i) W / cartanInner5 (v i) (v i) := by
    intro i W
    have hsum : cartanInner5 (v i) W = ∑ j, v.repr W j * cartanInner5 (v i) (v j) := by
      conv_lhs => rw [← v.sum_repr W]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single i]
    · exact (eq_div_iff (ne_of_gt (hpos i))).mpr rfl
    · intro j _ hji
      rw [hv hji.symm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have htr : LinearMap.trace ℝ FreudenthalTKK5E8 (A * A) =
      ∑ i, -(cartanInner5 (A (v i)) (A (v i)) / cartanInner5 (v i) (v i)) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ v]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.End.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepr i (A (A (v i)))]
    have hsk := hskew (v i) (A (v i))
    have hneg : cartanInner5 (v i) (A (A (v i))) = -cartanInner5 (A (v i)) (A (v i)) := by linarith
    rw [hneg, neg_div]
  rw [htr, Finset.sum_neg_distrib]
  refine ⟨neg_nonpos.mpr (Finset.sum_nonneg fun i _ =>
    div_nonneg (cartanInner5_nonneg _) (hpos i).le), ?_⟩
  intro hz
  rw [neg_eq_zero] at hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (cartanInner5_nonneg _) (hpos i).le).mp hz
  apply v.ext
  intro i
  have hi := hall i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at hi
  have hAi0 : cartanInner5 (A (v i)) (A (v i)) = 0 := hi.resolve_right (ne_of_gt (hpos i))
  exact (cartanInner5_eq_zero_iff _).mp hAi0

private theorem trace_sq_nonneg_of_self_ortho
    (A : Module.End ℝ FreudenthalTKK5E8)
    (hself : ∀ X Y, cartanInner5 (A X) Y = cartanInner5 X (A Y)) :
    0 ≤ LinearMap.trace ℝ FreudenthalTKK5E8 (A * A) ∧
      (LinearMap.trace ℝ FreudenthalTKK5E8 (A * A) = 0 → A = 0) := by
  have : FiniteDimensional ℝ FreudenthalTKK5E8 := inferInstance
  have hsymm5 : LinearMap.IsSymm cartanInner5 := ⟨cartanInner5_symm⟩
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (B := cartanInner5) hsymm5
  have hpos : ∀ i, 0 < cartanInner5 (v i) (v i) := fun i =>
    lt_of_le_of_ne (cartanInner5_nonneg (v i))
      (fun h => (v.ne_zero i) ((cartanInner5_eq_zero_iff (v i)).mp h.symm))
  have hrepr : ∀ i (W : FreudenthalTKK5E8),
      v.repr W i = cartanInner5 (v i) W / cartanInner5 (v i) (v i) := by
    intro i W
    have hsum : cartanInner5 (v i) W = ∑ j, v.repr W j * cartanInner5 (v i) (v j) := by
      conv_lhs => rw [← v.sum_repr W]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single i]
    · exact (eq_div_iff (ne_of_gt (hpos i))).mpr rfl
    · intro j _ hji
      rw [hv hji.symm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have htr : LinearMap.trace ℝ FreudenthalTKK5E8 (A * A) =
      ∑ i, cartanInner5 (A (v i)) (A (v i)) / cartanInner5 (v i) (v i) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ v]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.End.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepr i (A (A (v i))), ← hself (v i) (A (v i))]
  rw [htr]
  refine ⟨Finset.sum_nonneg fun i _ =>
    div_nonneg (cartanInner5_nonneg _) (hpos i).le, ?_⟩
  intro hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (cartanInner5_nonneg _) (hpos i).le).mp hz
  apply v.ext
  intro i
  have hi := hall i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at hi
  have hAi0 : cartanInner5 (A (v i)) (A (v i)) = 0 := hi.resolve_right (ne_of_gt (hpos i))
  exact (cartanInner5_eq_zero_iff _).mp hAi0

private theorem ad_eq_zero_iff (U : FreudenthalTKK5E8) :
    LieAlgebra.ad ℝ FreudenthalTKK5E8 U = 0 ↔ U = 0 := by
  constructor
  · intro h
    have hmem : U ∈ LieAlgebra.center ℝ FreudenthalTKK5E8 := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro V
      have hVU : ⁅U, V⁆ = 0 := LinearMap.ext_iff.mp h V
      rw [← lie_skew V U, hVU, neg_zero]
    rcases freudenthalTKK5E8_isSimple.eq_bot_or_eq_top
        (LieAlgebra.center ℝ FreudenthalTKK5E8) with hbot | htop
    · rw [hbot, LieSubmodule.mem_bot] at hmem; exact hmem
    · exfalso
      have hge : ⁅gradeCenterZ, ePlus2⁆ = 0 := by
        have hm : ePlus2 ∈ LieAlgebra.center ℝ FreudenthalTKK5E8 :=
          htop ▸ (LieSubmodule.mem_top ePlus2)
        exact (LieModule.mem_maxTrivSubmodule ℝ FreudenthalTKK5E8 FreudenthalTKK5E8 _).mp
          hm gradeCenterZ
      have hp2 : (⁅gradeCenterZ, ePlus2⁆).gPlus2 = 2 := by
        change (adZ ePlus2).gPlus2 = 2
        rw [adZ_gPlus2]; simp [ePlus2]
      rw [hge] at hp2
      norm_num at hp2
  · rintro rfl; simp

theorem tkk5_killingForm_cartanCompact_nonpos {X : FreudenthalTKK5E8}
    (hX : X ∈ tkk5E8CartanCompact) :
    killingForm ℝ FreudenthalTKK5E8 X X ≤ 0 := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonpos_of_skew_ortho (LieAlgebra.ad ℝ FreudenthalTKK5E8 X)
    (cartanInner5_ad_skew_on_compact hX)).1

theorem tkk5_killingForm_cartanCompact_eq_zero_iff {X : FreudenthalTKK5E8}
    (hX : X ∈ tkk5E8CartanCompact) :
    killingForm ℝ FreudenthalTKK5E8 X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonpos_of_skew_ortho (LieAlgebra.ad ℝ FreudenthalTKK5E8 X)
      (cartanInner5_ad_skew_on_compact hX)).2 h
    exact (ad_eq_zero_iff X).mp had0
  · rintro rfl; simp

theorem tkk5_killingForm_cartanNoncompact_nonneg {X : FreudenthalTKK5E8}
    (hX : X ∈ tkk5E8CartanNoncompact) :
    0 ≤ killingForm ℝ FreudenthalTKK5E8 X X := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonneg_of_self_ortho (LieAlgebra.ad ℝ FreudenthalTKK5E8 X)
    (cartanInner5_ad_self_on_noncompact hX)).1

theorem tkk5_killingForm_cartanNoncompact_eq_zero_iff {X : FreudenthalTKK5E8}
    (hX : X ∈ tkk5E8CartanNoncompact) :
    killingForm ℝ FreudenthalTKK5E8 X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonneg_of_self_ortho (LieAlgebra.ad ℝ FreudenthalTKK5E8 X)
      (cartanInner5_ad_self_on_noncompact hX)).2 h
    exact (ad_eq_zero_iff X).mp had0
  · rintro rfl; simp

theorem tkk5_killingForm_cartanCompact_noncompact_ortho {X Y : FreudenthalTKK5E8}
    (hX : X ∈ tkk5E8CartanCompact) (hY : Y ∈ tkk5E8CartanNoncompact) :
    killingForm ℝ FreudenthalTKK5E8 X Y = 0 := by
  have heq := LieAlgebra.killingForm_of_equiv_apply θ₅ X Y
  rw [mem_tkk5E8CartanCompact_iff.mp hX, mem_tkk5E8CartanNoncompact_iff.mp hY, map_neg] at heq
  linarith

instance freudenthalTKK5E8_isKilling : LieAlgebra.IsKilling ℝ FreudenthalTKK5E8 := by
  constructor
  rw [eq_bot_iff]
  intro Z hZ
  rw [LieSubmodule.mem_bot]
  have hZker : ∀ W : FreudenthalTKK5E8, killingForm ℝ FreudenthalTKK5E8 W Z = 0 := fun W =>
    (LieIdeal.mem_killingCompl ℝ FreudenthalTKK5E8 ⊤).mp hZ W (LieSubmodule.mem_top W)
  let Zk : FreudenthalTKK5E8 := (1 / 2 : ℝ) • (Z + θ₅ Z)
  let Zp : FreudenthalTKK5E8 := (1 / 2 : ℝ) • (Z - θ₅ Z)
  have hZk : Zk ∈ tkk5E8CartanCompact := by
    rw [mem_tkk5E8CartanCompact_iff]
    dsimp [Zk]; rw [map_smul, map_add, θ₅_involutive, add_comm]
  have hZp : Zp ∈ tkk5E8CartanNoncompact := by
    rw [mem_tkk5E8CartanNoncompact_iff]
    dsimp [Zp]; rw [map_smul, map_sub, θ₅_involutive, ← smul_neg, neg_sub]
  have hsum : Z = Zk + Zp := by dsimp [Zk, Zp]; module
  have hZk0 : Zk = 0 := by
    apply (tkk5_killingForm_cartanCompact_eq_zero_iff hZk).mp
    have h1 := hZker Zk
    rw [hsum, map_add, tkk5_killingForm_cartanCompact_noncompact_ortho hZk hZp, add_zero] at h1
    exact h1
  have hZp0 : Zp = 0 := by
    apply (tkk5_killingForm_cartanNoncompact_eq_zero_iff hZp).mp
    have h1 := hZker Zp
    have hortho : killingForm ℝ FreudenthalTKK5E8 Zp Zk = 0 := by
      rw [LieModule.traceForm_comm]
      exact tkk5_killingForm_cartanCompact_noncompact_ortho hZk hZp
    rw [hsum, map_add, hortho, zero_add] at h1
    exact h1
  rw [hsum, hZk0, hZp0, add_zero]

end Cartan5E8

section Sl2AndSplitE8Comparison

open InfoGeometry.Algebra.MagicSquareTitsBracket

/-- `zeroE7Hom` commutes with the 5-grading element `gradeCenterZ`. -/
theorem zeroE7Hom_comm_gradeCenterZ (X : H3ZornTKKLie) :
    ⁅zeroE7Hom X, gradeCenterZ⁆ = 0 := by
  change bracket5LM (injZeroE7 X) (injZeroCenter 1) = 0
  exact br_zE7_zC X 1

/-- `zeroE7Hom` commutes with `ePlus2`. -/
theorem zeroE7Hom_comm_ePlus2 (X : H3ZornTKKLie) :
    ⁅zeroE7Hom X, ePlus2⁆ = 0 := by
  change bracket5LM (injZeroE7 X) (injPlus2 1) = 0
  exact br_zE7_p2 X 1

/-- `zeroE7Hom` commutes with `eMinus2`. -/
theorem zeroE7Hom_comm_eMinus2 (X : H3ZornTKKLie) :
    ⁅zeroE7Hom X, eMinus2⁆ = 0 := by
  change bracket5LM (injZeroE7 X) (injMinus2 1) = 0
  exact br_zE7_m2 X 1

/-- The distinguished outer `sl₂` triple `(gradeCenterZ, ePlus2, eMinus2)` in `FreudenthalTKK5E8`. -/
theorem freudenthalTKK5E8_sl2Triple : IsSl2Triple gradeCenterZ ePlus2 eMinus2 where
  h_ne_zero := by
    intro h
    have hz := congrArg FreudenthalTKK5E8.gZeroCenter h
    norm_num [gradeCenterZ] at hz
  lie_e_f := by
    change bracket5LM (injPlus2 1) (injMinus2 1) = injZeroCenter 1
    rw [br_p2_m2, mul_one]
  lie_h_e_nsmul := by
    rw [two_nsmul]
    change bracket5LM (injZeroCenter 1) (injPlus2 1) = injPlus2 1 + injPlus2 1
    rw [br_zC_p2, mul_one, two_mul]
    apply FreudenthalTKK5E8.ext <;> simp [injPlus2_eq]
  lie_h_f_nsmul := by
    rw [two_nsmul]
    change bracket5LM (injZeroCenter 1) (injMinus2 1) = -(injMinus2 1 + injMinus2 1)
    rw [br_zC_m2, mul_one]
    apply FreudenthalTKK5E8.ext <;> simp [injMinus2_eq]

/-- The `8D` split Cartan subalgebra `tkk5E8Cartan = zeroE7Hom(h3zornE7Cartan) ⊕ ℝ·gradeCenterZ`
of `FreudenthalTKK5E8`. -/
def tkk5E8Cartan : LieSubalgebra ℝ FreudenthalTKK5E8 where
  carrier := {U | U.gMinus2 = 0 ∧ U.gMinus1 = 0 ∧ U.gZeroE7 ∈ h3zornE7Cartan ∧
    U.gPlus1 = 0 ∧ U.gPlus2 = 0}
  zero_mem' := ⟨rfl, rfl, h3zornE7Cartan.zero_mem, rfl, rfl⟩
  add_mem' {U V} hU hV :=
    ⟨by simp [hU.1, hV.1], by simp [hU.2.1, hV.2.1],
      h3zornE7Cartan.add_mem hU.2.2.1 hV.2.2.1,
      by simp [hU.2.2.2.1, hV.2.2.2.1], by simp [hU.2.2.2.2, hV.2.2.2.2]⟩
  smul_mem' r {U} hU :=
    ⟨by simp [hU.1], by simp [hU.2.1], h3zornE7Cartan.smul_mem r hU.2.2.1,
      by simp [hU.2.2.2.1], by simp [hU.2.2.2.2]⟩
  lie_mem' {U V} hU hV := by
    change (bracket5LM U V).gMinus2 = 0 ∧ (bracket5LM U V).gMinus1 = 0 ∧
      (bracket5LM U V).gZeroE7 ∈ h3zornE7Cartan ∧
      (bracket5LM U V).gPlus1 = 0 ∧ (bracket5LM U V).gPlus2 = 0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [bracket5LM_gMinus2, hU.1, hV.1, hU.2.1, hV.2.1]
    · simp [bracket5LM_gMinus1, hU.1, hV.1, hU.2.1, hV.2.1, hU.2.2.2.1, hV.2.2.2.1]
    · simp only [bracket5LM_gZeroE7, hU.2.1, hV.2.1,
        hU.2.2.2.1, hV.2.2.2.1, K_zero_left, sub_zero, add_zero]
      exact h3zornE7Cartan.lie_mem hU.2.2.1 hV.2.2.1
    · simp [bracket5LM_gPlus1, hU.2.1, hV.2.1, hU.2.2.2.1, hV.2.2.2.1, hU.2.2.2.2, hV.2.2.2.2]
    · simp [bracket5LM_gPlus2, hU.2.2.2.1, hV.2.2.2.1, hU.2.2.2.2, hV.2.2.2.2]

@[simp] theorem mem_tkk5E8Cartan_iff {U : FreudenthalTKK5E8} :
    U ∈ tkk5E8Cartan ↔
      U.gMinus2 = 0 ∧ U.gMinus1 = 0 ∧ U.gZeroE7 ∈ h3zornE7Cartan ∧
        U.gPlus1 = 0 ∧ U.gPlus2 = 0 := Iff.rfl

theorem zeroE7Hom_mem_tkk5E8Cartan {X : H3ZornTKKLie} (hX : X ∈ h3zornE7Cartan) :
    zeroE7Hom X ∈ tkk5E8Cartan :=
  ⟨rfl, rfl, hX, rfl, rfl⟩

theorem gradeCenterZ_mem_tkk5E8Cartan : gradeCenterZ ∈ tkk5E8Cartan :=
  ⟨rfl, rfl, h3zornE7Cartan.zero_mem, rfl, rfl⟩

private theorem zeroE7Hom_eq_injZeroE7 (X : H3ZornTKKLie) :
    zeroE7Hom X = injZeroE7 X := rfl

theorem tkk5E8Cartan_eq_sup :
    tkk5E8Cartan =
      h3zornE7Cartan.map zeroE7Hom ⊔ LieSubalgebra.lieSpan ℝ FreudenthalTKK5E8 {gradeCenterZ} := by
  apply le_antisymm
  · intro U hU
    rcases mem_tkk5E8Cartan_iff.mp hU with ⟨hm2, hm1, he7, hp1, hp2⟩
    have hdec : U = zeroE7Hom U.gZeroE7 + U.gZeroCenter • gradeCenterZ := by
      apply FreudenthalTKK5E8.ext <;>
        simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq,
          hm2, hm1, hp1, hp2]
    rw [hdec]
    refine LieSubalgebra.add_mem _
      (SetLike.le_def.mp le_sup_left ⟨U.gZeroE7, he7, rfl⟩)
      (SetLike.le_def.mp le_sup_right
        (LieSubalgebra.smul_mem _ _ (LieSubalgebra.subset_lieSpan (Set.mem_singleton gradeCenterZ))))
  · refine sup_le ?_ ?_
    · rintro _ ⟨X, hX, rfl⟩; exact zeroE7Hom_mem_tkk5E8Cartan hX
    · rw [LieSubalgebra.lieSpan_le, Set.singleton_subset_iff]
      exact gradeCenterZ_mem_tkk5E8Cartan

private def tkk5E8CartanEquiv : tkk5E8Cartan ≃ₗ[ℝ] h3zornE7Cartan × ℝ where
  toFun U := (⟨U.1.gZeroE7, (mem_tkk5E8Cartan_iff.mp U.2).2.2.1⟩, U.1.gZeroCenter)
  invFun p :=
    ⟨zeroE7Hom p.1.1 + p.2 • gradeCenterZ,
      ⟨by simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq],
       by simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq],
       by simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq, p.1.2],
       by simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq],
       by simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq]⟩⟩
  left_inv U := by
    rcases mem_tkk5E8Cartan_iff.mp U.2 with ⟨hm2, hm1, _, hp1, hp2⟩
    apply Subtype.ext
    apply FreudenthalTKK5E8.ext <;>
      simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq,
        hm2, hm1, hp1, hp2]
  right_inv p := by
    rcases p with ⟨⟨X, hX⟩, c⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq]
    · simp [zeroE7Hom_eq_injZeroE7, injZeroE7_eq, gradeCenterZ, injZeroCenter_eq]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_tkk5E8Cartan : Module.finrank ℝ tkk5E8Cartan = 8 := by
  rw [LinearEquiv.finrank_eq tkk5E8CartanEquiv, Module.finrank_prod,
    finrank_h3zornE7Cartan, Module.finrank_self]

instance tkk5E8Cartan_isLieAbelian : IsLieAbelian tkk5E8Cartan where
  trivial U V := by
    apply Subtype.ext
    rcases mem_tkk5E8Cartan_iff.mp U.2 with ⟨hm2U, hm1U, he7U, hp1U, hp2U⟩
    rcases mem_tkk5E8Cartan_iff.mp V.2 with ⟨hm2V, hm1V, he7V, hp1V, hp2V⟩
    have hE70 : ⁅U.1.gZeroE7, V.1.gZeroE7⁆ = 0 :=
      congrArg Subtype.val ((inferInstance : IsLieAbelian h3zornE7Cartan).trivial
        ⟨U.1.gZeroE7, he7U⟩ ⟨V.1.gZeroE7, he7V⟩)
    change bracket5LM U.1 V.1 = 0
    apply FreudenthalTKK5E8.ext
    · simp [bracket5LM_gMinus2, hm2U, hm2V, hm1U, hm1V]
    · simp [bracket5LM_gMinus1, hm2U, hm2V, hm1U, hm1V, hp1U, hp1V]
    · simp [bracket5LM_gZeroE7, hm1U, hm1V, hp1U, hp1V, hE70]
    · simp [bracket5LM_gZeroCenter, hm2U, hm2V, hm1U, hm1V, hp1U, hp1V, hp2U, hp2V]
    · simp [bracket5LM_gPlus1, hm1U, hm1V, hp1U, hp1V, hp2U, hp2V]
    · simp [bracket5LM_gPlus2, hp1U, hp1V, hp2U, hp2V]

theorem tkk5E8Cartan_self_normalizing :
    tkk5E8Cartan.normalizer = tkk5E8Cartan := by
  apply le_antisymm _ tkk5E8Cartan.le_normalizer
  intro U hU
  have hz_mem : gradeCenterZ ∈ tkk5E8Cartan := by
    change gradeCenterZ.gMinus2 = 0 ∧ gradeCenterZ.gMinus1 = 0 ∧
      gradeCenterZ.gZeroE7 ∈ h3zornE7Cartan ∧ gradeCenterZ.gPlus1 = 0 ∧
      gradeCenterZ.gPlus2 = 0
    refine ⟨rfl, rfl, zero_mem _, rfl, rfl⟩
  have hbrZ : ⁅gradeCenterZ, U⁆ ∈ tkk5E8Cartan := by
    have h1 := (LieSubalgebra.mem_normalizer_iff tkk5E8Cartan U).mp hU gradeCenterZ hz_mem
    have h2 := tkk5E8Cartan.neg_mem h1
    rw [← lie_skew, neg_neg] at h2
    exact h2
  have hbrZ_eq : ⁅gradeCenterZ, U⁆ =
      { gMinus2 := -2 * U.gMinus2
        gMinus1 := (-1 : ℝ) • U.gMinus1
        gZeroE7 := 0
        gZeroCenter := 0
        gPlus1 := (1 : ℝ) • U.gPlus1
        gPlus2 := 2 * U.gPlus2 } := by
    change bracket5LM gradeCenterZ U = _
    apply FreudenthalTKK5E8.ext <;>
      simp [bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
        bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2, gradeCenterZ]
  have hm2 : U.gMinus2 = 0 := by
    have h : ⁅gradeCenterZ, U⁆.gMinus2 = 0 := hbrZ.1
    rw [hbrZ_eq] at h; dsimp at h; linarith
  have hm1 : U.gMinus1 = 0 := by
    have h : ⁅gradeCenterZ, U⁆.gMinus1 = 0 := hbrZ.2.1
    rw [hbrZ_eq] at h; dsimp at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hp1 : U.gPlus1 = 0 := by
    have h : ⁅gradeCenterZ, U⁆.gPlus1 = 0 := hbrZ.2.2.2.1
    rw [hbrZ_eq] at h; dsimp at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hp2 : U.gPlus2 = 0 := by
    have h : ⁅gradeCenterZ, U⁆.gPlus2 = 0 := hbrZ.2.2.2.2
    rw [hbrZ_eq] at h; dsimp at h; linarith
  have h0 : U.gZeroE7 ∈ h3zornE7Cartan := by
    rw [← h3zornE7Cartan_isCartanSubalgebra.self_normalizing, LieSubalgebra.mem_normalizer_iff]
    intro H hH
    have hH_mem : injZeroE7 H ∈ tkk5E8Cartan := by
      change (injZeroE7 H).gMinus2 = 0 ∧ (injZeroE7 H).gMinus1 = 0 ∧
        (injZeroE7 H).gZeroE7 ∈ h3zornE7Cartan ∧ (injZeroE7 H).gPlus1 = 0 ∧
        (injZeroE7 H).gPlus2 = 0
      exact ⟨rfl, rfl, hH, rfl, rfl⟩
    have hbrH := (LieSubalgebra.mem_normalizer_iff tkk5E8Cartan U).mp hU (injZeroE7 H) hH_mem
    have h0' : ⁅U, injZeroE7 H⁆.gZeroE7 ∈ h3zornE7Cartan := hbrH.2.2.1
    have heq : ⁅U, injZeroE7 H⁆.gZeroE7 = ⁅U.gZeroE7, H⁆ := by
      change (bracket5LM U (injZeroE7 H)).gZeroE7 = _
      simp [bracket5LM_gZeroE7, hm1, hp1, injZeroE7]
    rwa [← heq]
  exact ⟨hm2, hm1, h0, hp1, hp2⟩

noncomputable instance tkk5E8Cartan_isCartanSubalgebra :
    tkk5E8Cartan.IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := tkk5E8Cartan_self_normalizing

/-- Both `FreudenthalTKK5E8` and `SplitE8Lie` have dimension `248`. -/
theorem freudenthalTKK5E8_and_splitE8Lie_finrank :
    Module.finrank ℝ FreudenthalTKK5E8 = 248 ∧ Module.finrank ℝ SplitE8Lie = 248 :=
  ⟨finrank_freudenthalTKK5E8, finrank_splitE8Lie⟩

/-- Both `FreudenthalTKK5E8` and `SplitE8Lie` are simple Lie algebras with non-degenerate
Killing forms (`IsSimple ℝ` and `IsKilling ℝ`). -/
theorem freudenthalTKK5E8_and_splitE8Lie_simple_killing :
    LieAlgebra.IsSimple ℝ FreudenthalTKK5E8 ∧ LieAlgebra.IsSimple ℝ SplitE8Lie ∧
      LieAlgebra.IsKilling ℝ FreudenthalTKK5E8 ∧ LieAlgebra.IsKilling ℝ SplitE8Lie :=
  ⟨freudenthalTKK5E8_isSimple, splitE8Lie_isSimple,
    freudenthalTKK5E8_isKilling, splitE8Lie_isKilling⟩

/-- Both `FreudenthalTKK5E8` (`tkk5E8Cartan`) and `SplitE8Lie` (`splitE8Cartan`) possess
`8D` abelian split Cartan subalgebras. -/
theorem freudenthalTKK5E8_and_splitE8Lie_cartan_rank_eight :
    Module.finrank ℝ tkk5E8Cartan = 8 ∧ IsLieAbelian tkk5E8Cartan ∧
      Module.finrank ℝ splitE8Cartan = 8 ∧ IsLieAbelian splitE8Cartan :=
  ⟨finrank_tkk5E8Cartan, tkk5E8Cartan_isLieAbelian,
    finrank_splitE8Cartan, splitE8Cartan_isLieAbelian⟩

/-- Consolidated structural invariants matching the `248D` split real form `E₈(8)` across the
5-graded Freudenthal–Kantor–Koecher–Tits model `FreudenthalTKK5E8` and the Chevalley model
`SplitE8Lie`. -/
theorem freudenthalTKK5E8_split_real_form_invariants :
    Module.finrank ℝ FreudenthalTKK5E8 = 248 ∧
      Module.finrank ℝ SplitE8Lie = 248 ∧
      Module.finrank ℝ tkk5E8CartanCompact = 120 ∧
      Module.finrank ℝ tkk5E8CartanNoncompact = 128 ∧
      (Module.finrank ℝ tkk5E8CartanNoncompact : ℤ) - Module.finrank ℝ tkk5E8CartanCompact = 8 ∧
      IsSl2Triple gradeCenterZ ePlus2 eMinus2 ∧
      Module.finrank ℝ tkk5E8Cartan = 8 ∧
      Module.finrank ℝ splitE8Cartan = 8 ∧
      LieAlgebra.IsSimple ℝ FreudenthalTKK5E8 ∧
      LieAlgebra.IsKilling ℝ FreudenthalTKK5E8 ∧
      LieAlgebra.IsSimple ℝ SplitE8Lie ∧
      LieAlgebra.IsKilling ℝ SplitE8Lie :=
  ⟨finrank_freudenthalTKK5E8, finrank_splitE8Lie,
    finrank_tkk5E8CartanCompact, finrank_tkk5E8CartanNoncompact,
    freudenthalTKK5E8_cartan_signature_eq_pos_8,
    freudenthalTKK5E8_sl2Triple,
    finrank_tkk5E8Cartan, finrank_splitE8Cartan,
    freudenthalTKK5E8_isSimple, freudenthalTKK5E8_isKilling,
    splitE8Lie_isSimple, splitE8Lie_isKilling⟩

end Sl2AndSplitE8Comparison

end InfoGeometry.Algebra
