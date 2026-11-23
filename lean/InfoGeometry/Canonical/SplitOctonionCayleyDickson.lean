/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
import InfoGeometry.Canonical.SplitOctonionClifford33Soldering

/-!
# Split-Octonion Cayley–Dickson `1 + 3 + 1 + 3` Anatomy and Left-Multiplication Operators

This module formalizes the 8-dimensional split-octonion algebra `SplitOctCD` over `ℝ` via the
split Cayley–Dickson doubling `(a, b) * (c, d) = (a * c + star d * b, d * a + b * star c)` on
a dedicated `SplitOctCD` structure over pairs of `Quaternion ℝ`, avoiding any diamond with
Mathlib's componentwise `Prod.instRing`.

Main results:
1. The `1 + 3 + 1 + 3` generating basis `[1, i₁, i₂, i₃, ℓ, s₁, s₂, s₃]` with `sₖ = ℓ * iₖ`,
   quaternionic cyclic multiplication, anticommutation `ℓ * iₖ + iₖ * ℓ = 0`, `ℓ² = 1`, `sₖ² = 1`.
2. Explicit algebra-preserving linear equivalences to `InfoGeometry.Canonical.ZornMatrix ℝ` and
   `InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.ZornSplitOctonion ℝ`, preserving unit,
   multiplication, conjugation, and the `(4, 4)` Krein norm (`detZ` / `zornNormFun` / `zornNorm`).
3. Polarized left-alternative identity `L_x L_y + L_y L_x = L_{xy+yx}` on `8 × 8` real matrices
   `leftMulMat x`, explicit invertible `8 × 8` change-of-basis intertwiner `T` (`det T = -16`) to
   `SplitOctonionClifford33Soldering.zornLeftActMatrix`, and seven pairwise-anticommuting `8 × 8`
   real operators with squares `(-1, -1, -1, +1, +1, +1, +1)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCayleyDickson

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering

open scoped Matrix

/-! ## Section 1: Cayley–Dickson Carrier, Operations, and `NonAssocRing` Structure -/

/-- Split-octonion carrier `ℍ ⊕ ℓℍ` as a dedicated structure over `Quaternion ℝ × Quaternion ℝ`,
structurally isolated from Mathlib's componentwise `Prod.instRing`. -/
@[ext]
structure SplitOctCD where
  fst : Quaternion ℝ
  snd : Quaternion ℝ

/-- Constructive inhabited witness for `SplitOctCD`. -/
instance : Inhabited SplitOctCD := ⟨⟨0, 0⟩⟩

/-- Coordinate equivalence `SplitOctCD ≃ Quaternion ℝ × Quaternion ℝ`. -/
def cdProdEquiv : SplitOctCD ≃ Quaternion ℝ × Quaternion ℝ where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by rcases p with ⟨a, b⟩; rfl

@[instance_reducible] private def cdAddCommGroup : AddCommGroup SplitOctCD :=
  Equiv.addCommGroup cdProdEquiv

/-- Split Cayley–Dickson multiplication:
`(a, b) * (c, d) = (a * c + star d * b, d * a + b * star c)`. -/
def cdMul (x y : SplitOctCD) : SplitOctCD :=
  ⟨x.fst * y.fst + star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩

/-- Multiplicative identity `⟨1, 0⟩` on `SplitOctCD`. -/
def oneCD : SplitOctCD := ⟨1, 0⟩

instance : One SplitOctCD := ⟨oneCD⟩
instance : Mul SplitOctCD := ⟨cdMul⟩

/-- Split Cayley–Dickson conjugation `⟨a, b⟩ ↦ ⟨star a, -b⟩`. -/
def cdConj (x : SplitOctCD) : SplitOctCD := ⟨star x.fst, -x.snd⟩

/-- Split-octonion Krein quadratic norm `N(a, b) = normSq a - normSq b`. -/
def cdNorm (x : SplitOctCD) : ℝ :=
  Quaternion.normSq x.fst - Quaternion.normSq x.snd

theorem mul_def_cd (x y : SplitOctCD) : x * y = cdMul x y := rfl

@[simp] theorem oneCD_def : (1 : SplitOctCD) = ⟨1, 0⟩ := rfl
@[simp] theorem fst_zero : @SplitOctCD.fst (@OfNat.ofNat SplitOctCD 0
    (@Zero.toOfNat0 SplitOctCD cdAddCommGroup.toZero)) = 0 := rfl

section BaseOps

attribute [local instance] cdAddCommGroup

@[simp] theorem fst_zero' : (0 : SplitOctCD).fst = 0 := rfl
@[simp] theorem snd_zero' : (0 : SplitOctCD).snd = 0 := rfl
@[simp] theorem fst_one' : (1 : SplitOctCD).fst = 1 := rfl
@[simp] theorem snd_one' : (1 : SplitOctCD).snd = 0 := rfl
@[simp] theorem fst_add' (x y : SplitOctCD) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add' (x y : SplitOctCD) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_sub' (x y : SplitOctCD) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem snd_sub' (x y : SplitOctCD) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem fst_neg' (x : SplitOctCD) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg' (x : SplitOctCD) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_mul' (x y : SplitOctCD) :
    (x * y).fst = x.fst * y.fst + star y.snd * x.snd := rfl
@[simp] theorem snd_mul' (x y : SplitOctCD) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

private theorem one_cdMul_aux (x : SplitOctCD) : (1 : SplitOctCD) * x = x := by
  ext <;> simp

private theorem cdMul_one_aux (x : SplitOctCD) : x * (1 : SplitOctCD) = x := by
  ext <;> simp

private theorem zero_cdMul_aux (x : SplitOctCD) : (0 : SplitOctCD) * x = 0 := by
  ext <;> simp

private theorem cdMul_zero_aux (x : SplitOctCD) : x * (0 : SplitOctCD) = 0 := by
  ext <;> simp

private theorem cdMul_add_left_aux (x y z : SplitOctCD) :
    (x + y) * z = x * z + y * z := by
  ext <;> simp <;> ring

private theorem cdMul_add_right_aux (x y z : SplitOctCD) :
    x * (y + z) = x * y + x * z := by
  ext <;> simp <;> ring

end BaseOps

/-- Non-associative ring instance on `SplitOctCD` (single canonical `AddCommGroup` root). -/
instance : NonAssocRing SplitOctCD where
  add := cdAddCommGroup.add
  add_assoc := cdAddCommGroup.add_assoc
  zero := cdAddCommGroup.zero
  zero_add := cdAddCommGroup.zero_add
  add_zero := cdAddCommGroup.add_zero
  nsmul := cdAddCommGroup.nsmul
  nsmul_zero := cdAddCommGroup.nsmul_zero
  nsmul_succ := cdAddCommGroup.nsmul_succ
  neg := cdAddCommGroup.neg
  sub := cdAddCommGroup.sub
  sub_eq_add_neg := cdAddCommGroup.sub_eq_add_neg
  zsmul := cdAddCommGroup.zsmul
  zsmul_zero' := cdAddCommGroup.zsmul_zero'
  zsmul_succ' := cdAddCommGroup.zsmul_succ'
  zsmul_neg' := cdAddCommGroup.zsmul_neg'
  neg_add_cancel := cdAddCommGroup.neg_add_cancel
  add_comm := cdAddCommGroup.add_comm
  one := (1 : SplitOctCD)
  mul := cdMul
  left_distrib := cdMul_add_right_aux
  right_distrib := cdMul_add_left_aux
  zero_mul := zero_cdMul_aux
  mul_zero := cdMul_zero_aux
  one_mul := one_cdMul_aux
  mul_one := cdMul_one_aux

/-- Additive equivalence `SplitOctCD ≃+ Quaternion ℝ × Quaternion ℝ`. -/
def cdProdAddEquiv : SplitOctCD ≃+ Quaternion ℝ × Quaternion ℝ where
  toEquiv := cdProdEquiv
  map_add' x y := by cases x; cases y; rfl

/-- Real vector-space structure on `SplitOctCD`. -/
instance : Module ℝ SplitOctCD :=
  AddEquiv.module ℝ cdProdAddEquiv

/-- Scalar commutativity with `ℝ` on `SplitOctCD`. -/
instance : SMulCommClass ℝ ℝ SplitOctCD where
  smul_comm c d x := by
    cases x
    apply SplitOctCD.ext <;> simp [smul_smul, mul_comm]

/-- Scalar tower for `ℝ` on `SplitOctCD`. -/
instance : IsScalarTower ℝ ℝ SplitOctCD where
  smul_assoc c d x := by
    cases x
    apply SplitOctCD.ext <;> simp [smul_smul]

@[simp] theorem fst_zero_cd : (0 : SplitOctCD).fst = 0 := rfl
@[simp] theorem snd_zero_cd : (0 : SplitOctCD).snd = 0 := rfl
@[simp] theorem fst_one_cd : (1 : SplitOctCD).fst = 1 := rfl
@[simp] theorem snd_one_cd : (1 : SplitOctCD).snd = 0 := rfl
@[simp] theorem fst_add (x y : SplitOctCD) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : SplitOctCD) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_sub (x y : SplitOctCD) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem snd_sub (x y : SplitOctCD) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem fst_neg (x : SplitOctCD) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : SplitOctCD) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_smul (c : ℝ) (x : SplitOctCD) : (c • x).fst = c • x.fst := rfl
@[simp] theorem snd_smul (c : ℝ) (x : SplitOctCD) : (c • x).snd = c • x.snd := rfl
@[simp] theorem fst_mul (x y : SplitOctCD) :
    (x * y).fst = x.fst * y.fst + star y.snd * x.snd := rfl
@[simp] theorem snd_mul (x y : SplitOctCD) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

/-- Polarized `(4, 4)` Krein bilinear form associated to `cdNorm`. -/
def cdKreinForm (x y : SplitOctCD) : ℝ :=
  (cdNorm (x + y) - cdNorm x - cdNorm y) / 2

theorem one_cdMul (x : SplitOctCD) : (1 : SplitOctCD) * x = x := one_mul x
theorem cdMul_one (x : SplitOctCD) : x * (1 : SplitOctCD) = x := mul_one x
theorem zero_cdMul (x : SplitOctCD) : (0 : SplitOctCD) * x = 0 := zero_mul x
theorem cdMul_zero (x : SplitOctCD) : x * (0 : SplitOctCD) = 0 := mul_zero x
theorem cdMul_add_left (x y z : SplitOctCD) : (x + y) * z = x * z + y * z := right_distrib x y z
theorem cdMul_add_right (x y z : SplitOctCD) : x * (y + z) = x * y + x * z := left_distrib x y z

theorem cdMul_smul_left (c : ℝ) (x y : SplitOctCD) : (c • x) * y = c • (x * y) := by
  ext <;> simp

theorem cdMul_smul_right (c : ℝ) (x y : SplitOctCD) : x * (c • y) = c • (x * y) := by
  ext <;> simp

@[simp] theorem cdConj_add (x y : SplitOctCD) : cdConj (x + y) = cdConj x + cdConj y := by
  ext <;> simp [cdConj] <;> ring

@[simp] theorem cdConj_smul (c : ℝ) (x : SplitOctCD) : cdConj (c • x) = c • cdConj x := by
  ext <;> simp [cdConj]

theorem cdConj_cdConj (x : SplitOctCD) : cdConj (cdConj x) = x := by
  ext <;> simp [cdConj]

theorem cdConj_mul (x y : SplitOctCD) : cdConj (x * y) = cdConj y * cdConj x := by
  ext <;> simp [cdConj]

theorem mul_cdConj_self (x : SplitOctCD) : x * cdConj x = (cdNorm x) • (1 : SplitOctCD) := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  ext <;> simp [cdConj, cdNorm, Quaternion.normSq_def'] <;> ring

theorem cdConj_mul_self (x : SplitOctCD) : cdConj x * x = (cdNorm x) • (1 : SplitOctCD) := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  ext <;> simp [cdConj, cdNorm, Quaternion.normSq_def'] <;> ring

theorem cdNorm_mul (x y : SplitOctCD) : cdNorm (x * y) = cdNorm x * cdNorm y := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  rcases y with ⟨⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
  simp [cdNorm, Quaternion.normSq_def']
  ring

/-! ## Section 2: The `1 + 3 + 1 + 3` Basis and Real Chart `Fin 8 → ℝ` -/

/-- Standard imaginary quaternion basis vectors `i, j, k : Quaternion ℝ`. -/
def qBasis : Fin 3 → Quaternion ℝ
  | 0 => ⟨0, 1, 0, 0⟩
  | 1 => ⟨0, 0, 1, 0⟩
  | 2 => ⟨0, 0, 0, 1⟩

@[simp] theorem qBasis_star (k : Fin 3) : star (qBasis k) = -qBasis k := by
  fin_cases k <;> ext <;> simp [qBasis]

/-- Three quaternionic complex structures `i₁, i₂, i₃` in `SplitOctCD`. -/
def iCD (k : Fin 3) : SplitOctCD := ⟨qBasis k, 0⟩

/-- The unique parahypercomplex doubling generator `ℓ = ⟨0, 1⟩` in `SplitOctCD`. -/
def ellCD : SplitOctCD := ⟨0, 1⟩

/-- Three hypercomplex generators `sₖ = ℓ * iₖ` in `SplitOctCD`. -/
def sCD (k : Fin 3) : SplitOctCD := ellCD * iCD k

/-- Explicit component formula `sₖ = ⟨0, -qBasis k⟩` arising from `star (qBasis k) = -qBasis k`. -/
theorem sCD_formula (k : Fin 3) : sCD k = ⟨0, -qBasis k⟩ := by
  fin_cases k <;> ext <;> simp [sCD, ellCD, iCD, qBasis]

theorem iCD_sq (k : Fin 3) : iCD k * iCD k = -oneCD := by
  fin_cases k <;> ext <;> simp [iCD, qBasis, oneCD]

theorem iCD_mul_01 : iCD 0 * iCD 1 = iCD 2 := by
  ext <;> simp [iCD, qBasis]

theorem iCD_mul_10 : iCD 1 * iCD 0 = -iCD 2 := by
  ext <;> simp [iCD, qBasis]

theorem iCD_mul_12 : iCD 1 * iCD 2 = iCD 0 := by
  ext <;> simp [iCD, qBasis]

theorem iCD_mul_21 : iCD 2 * iCD 1 = -iCD 0 := by
  ext <;> simp [iCD, qBasis]

theorem iCD_mul_20 : iCD 2 * iCD 0 = iCD 1 := by
  ext <;> simp [iCD, qBasis]

theorem iCD_mul_02 : iCD 0 * iCD 2 = -iCD 1 := by
  ext <;> simp [iCD, qBasis]

theorem iCD_anticomm {j k : Fin 3} (hjk : j ≠ k) :
    iCD j * iCD k + iCD k * iCD j = 0 := by
  fin_cases j <;> fin_cases k <;> dsimp
  · exact absurd rfl hjk
  · rw [iCD_mul_01, iCD_mul_10, add_neg_cancel]
  · rw [iCD_mul_02, iCD_mul_20, neg_add_cancel]
  · rw [iCD_mul_10, iCD_mul_01, neg_add_cancel]
  · exact absurd rfl hjk
  · rw [iCD_mul_12, iCD_mul_21, add_neg_cancel]
  · rw [iCD_mul_20, iCD_mul_02, add_neg_cancel]
  · rw [iCD_mul_21, iCD_mul_12, neg_add_cancel]
  · exact absurd rfl hjk

theorem ellCD_sq : ellCD * ellCD = oneCD := by
  ext <;> simp [ellCD, oneCD]

theorem ellCD_anticomm_iCD (k : Fin 3) : ellCD * iCD k + iCD k * ellCD = 0 := by
  fin_cases k <;> ext <;> simp [ellCD, iCD, qBasis]

theorem sCD_sq (k : Fin 3) : sCD k * sCD k = oneCD := by
  fin_cases k <;> ext <;> simp [sCD, ellCD, iCD, qBasis, oneCD]

/-- Coordinate extraction in the `[1, i₁, i₂, i₃, ℓ, s₁, s₂, s₃]` basis.
Note the negative signs on slots `5, 6, 7` because `sₖ = ⟨0, -qBasis k⟩`. -/
def cdToFin8 (x : SplitOctCD) : Fin 8 → ℝ :=
  ![x.fst.re, x.fst.imI, x.fst.imJ, x.fst.imK,
    x.snd.re, -x.snd.imI, -x.snd.imJ, -x.snd.imK]

/-- Reconstruct a `SplitOctCD` element from its `[1, i₁, i₂, i₃, ℓ, s₁, s₂, s₃]` coordinates. -/
def fin8ToCD (c : Fin 8 → ℝ) : SplitOctCD :=
  ⟨⟨c 0, c 1, c 2, c 3⟩, ⟨c 4, -c 5, -c 6, -c 7⟩⟩

/-- Real linear equivalence `SplitOctCD ≃ₗ[ℝ] (Fin 8 → ℝ)` in the `1 + 3 + 1 + 3` basis. -/
def cdLinearEquivFin8 : SplitOctCD ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := cdToFin8
  invFun := fin8ToCD
  left_inv x := by
    rcases x with ⟨⟨q0, q1, q2, q3⟩, ⟨r0, r1, r2, r3⟩⟩
    ext <;> simp [cdToFin8, fin8ToCD]
  right_inv c := by
    funext i
    fin_cases i <;> simp [cdToFin8, fin8ToCD]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [cdToFin8, add_comm]
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [cdToFin8]

@[simp] theorem cdLinearEquivFin8_apply (x : SplitOctCD) :
    cdLinearEquivFin8 x = cdToFin8 x := rfl

@[simp] theorem cdLinearEquivFin8_symm_apply (c : Fin 8 → ℝ) :
    cdLinearEquivFin8.symm c = fin8ToCD c := rfl

@[simp] theorem fin8ToCD_cdToFin8 (x : SplitOctCD) :
    fin8ToCD (cdToFin8 x) = x := by
  exact cdLinearEquivFin8.symm_apply_apply x

@[simp] theorem cdToFin8_fin8ToCD (c : Fin 8 → ℝ) :
    cdToFin8 (fin8ToCD c) = c := by
  exact cdLinearEquivFin8.apply_symm_apply c

/-- Ordered `1 + 3 + 1 + 3` vector-space basis `[1, i₁, i₂, i₃, ℓ, s₁, s₂, s₃]` of `SplitOctCD`. -/
def basisCD : Module.Basis (Fin 8) ℝ SplitOctCD :=
  Module.Basis.ofEquivFun cdLinearEquivFin8

@[simp] theorem basisCD_repr_apply (x : SplitOctCD) (i : Fin 8) :
    basisCD.repr x i = cdToFin8 x i := by
  simp [basisCD]

theorem basisCD_zero : basisCD 0 = oneCD := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, oneCD]

theorem basisCD_one : basisCD 1 = iCD 0 := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, iCD, qBasis]

theorem basisCD_two : basisCD 2 = iCD 1 := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, iCD, qBasis]

theorem basisCD_three : basisCD 3 = iCD 2 := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, iCD, qBasis]

theorem basisCD_four : basisCD 4 = ellCD := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, ellCD]

theorem basisCD_five : basisCD 5 = sCD 0 := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, sCD_formula, qBasis]

theorem basisCD_six : basisCD 6 = sCD 1 := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, sCD_formula, qBasis]

theorem basisCD_seven : basisCD 7 = sCD 2 := by
  apply cdLinearEquivFin8.injective
  funext j
  fin_cases j <;> simp [basisCD, cdToFin8, fin8ToCD, sCD_formula, qBasis]

/-- Exact `(4, 4)` Krein signature of `cdNorm` in the `1 + 3 + 1 + 3` coordinates. -/
theorem cdNorm_signature_44 (c : Fin 8 → ℝ) :
    cdNorm (fin8ToCD c) =
      c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 -
        (c 4 ^ 2 + c 5 ^ 2 + c 6 ^ 2 + c 7 ^ 2) := by
  unfold cdNorm fin8ToCD
  rw [Quaternion.normSq_def', Quaternion.normSq_def']
  dsimp
  ring

/-- The polarized Krein bilinear form on `basisCD` is diagonal with `[1, 1, 1, 1, -1, -1, -1, -1]`. -/
theorem cdKreinForm_basisCD (i j : Fin 8) :
    cdKreinForm (basisCD i) (basisCD j) =
      if i = j then (![1, 1, 1, 1, -1, -1, -1, -1] : Fin 8 → ℝ) i else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cdKreinForm, basisCD_zero, basisCD_one, basisCD_two, basisCD_three,
      basisCD_four, basisCD_five, basisCD_six, basisCD_seven, oneCD, iCD, ellCD,
      sCD_formula, qBasis, cdNorm, Quaternion.normSq_def'] <;>
    norm_num

/-! ## Section 3: Algebra Isomorphisms to `ZornMatrix ℝ` and `ZornSplitOctonion ℝ` -/

/-- Exact sign-aligned `ℝ`-linear algebra isomorphism `SplitOctCD ≃ₗ[ℝ] ZornMatrix ℝ`. -/
def splitOctCDEquivZornMatrix : SplitOctCD ≃ₗ[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ where
  toFun x :=
    { a := x.fst.re + x.snd.re
      b := x.fst.re - x.snd.re
      x := ![x.snd.imI - x.fst.imI, x.snd.imJ - x.fst.imJ, x.snd.imK - x.fst.imK]
      y := ![x.fst.imI + x.snd.imI, x.fst.imJ + x.snd.imJ, x.fst.imK + x.snd.imK] }
  invFun z :=
    ⟨ ⟨(z.a + z.b) / 2, (z.y 0 - z.x 0) / 2, (z.y 1 - z.x 1) / 2, (z.y 2 - z.x 2) / 2⟩,
      ⟨(z.a - z.b) / 2, (z.x 0 + z.y 0) / 2, (z.x 1 + z.y 1) / 2, (z.x 2 + z.y 2) / 2⟩ ⟩
  left_inv x := by
    rcases x with ⟨⟨q0, q1, q2, q3⟩, ⟨r0, r1, r2, r3⟩⟩
    ext <;> dsimp <;> ring
  right_inv z := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · dsimp; ring
    · dsimp; ring
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring
  map_add' x y := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · dsimp; ring
    · dsimp; ring
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [smul_eq_mul]
      ring
    · simp [smul_eq_mul]
      ring
    · funext i
      fin_cases i <;> simp [smul_eq_mul] <;> ring
    · funext i
      fin_cases i <;> simp [smul_eq_mul] <;> ring

@[simp] theorem splitOctCDEquivZornMatrix_apply (x : SplitOctCD) :
    splitOctCDEquivZornMatrix x =
      { a := x.fst.re + x.snd.re
        b := x.fst.re - x.snd.re
        x := ![x.snd.imI - x.fst.imI, x.snd.imJ - x.fst.imJ, x.snd.imK - x.fst.imK]
        y := ![x.fst.imI + x.snd.imI, x.fst.imJ + x.snd.imJ, x.fst.imK + x.snd.imK] } := rfl

@[simp] theorem splitOctCDEquivZornMatrix_symm_apply (z : InfoGeometry.Canonical.ZornMatrix ℝ) :
    splitOctCDEquivZornMatrix.symm z =
      ⟨ ⟨(z.a + z.b) / 2, (z.y 0 - z.x 0) / 2, (z.y 1 - z.x 1) / 2, (z.y 2 - z.x 2) / 2⟩,
        ⟨(z.a - z.b) / 2, (z.x 0 + z.y 0) / 2, (z.x 1 + z.y 1) / 2, (z.x 2 + z.y 2) / 2⟩ ⟩ := rfl

theorem splitOctCDEquivZornMatrix_one :
    splitOctCDEquivZornMatrix (1 : SplitOctCD) = (1 : InfoGeometry.Canonical.ZornMatrix ℝ) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp
  · simp
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp

theorem splitOctCDEquivZornMatrix_mul (x y : SplitOctCD) :
    splitOctCDEquivZornMatrix (x * y) =
      splitOctCDEquivZornMatrix x * splitOctCDEquivZornMatrix y := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  rcases y with ⟨⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot]
    ring
  · simp [InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot]
    ring
  · funext i
    fin_cases i <;>
      simp [InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.cross] <;>
      ring
  · funext i
    fin_cases i <;>
      simp [InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.cross] <;>
      ring

theorem splitOctCDEquivZornMatrix_conj (x : SplitOctCD) :
    splitOctCDEquivZornMatrix (cdConj x) =
      InfoGeometry.Canonical.ZornClifford.zornConj (splitOctCDEquivZornMatrix x) := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [cdConj, InfoGeometry.Canonical.ZornClifford.zornConj]
    ring
  · simp [cdConj, InfoGeometry.Canonical.ZornClifford.zornConj]
  · funext i
    fin_cases i <;> simp [cdConj, InfoGeometry.Canonical.ZornClifford.zornConj] <;> ring
  · funext i
    fin_cases i <;> simp [cdConj, InfoGeometry.Canonical.ZornClifford.zornConj] <;> ring

theorem splitOctCDEquivZornMatrix_norm (x : SplitOctCD) :
    InfoGeometry.Canonical.ZornClifford.zornNormFun (splitOctCDEquivZornMatrix x) =
      cdNorm x := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  simp [InfoGeometry.Canonical.ZornClifford.zornNormFun,
    InfoGeometry.Canonical.ZornMatrix.dot, cdNorm, Quaternion.normSq_def']
  ring

theorem splitOctCDEquivZornMatrix_detZ (x : SplitOctCD) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (splitOctCDEquivZornMatrix x) = cdNorm x := by
  change (splitOctCDEquivZornMatrix x).a * (splitOctCDEquivZornMatrix x).b -
    InfoGeometry.Canonical.ZornMatrix.dot
      (splitOctCDEquivZornMatrix x).x (splitOctCDEquivZornMatrix x).y = cdNorm x
  exact splitOctCDEquivZornMatrix_norm x

/-- Equivalence `SplitOctCD ≃ ZornSplitOctonion ℝ` matching `splitOctCDEquivZornMatrix`
component-for-component under `(a, b, x, y) ↔ (a, u, v, b)`. -/
def splitOctCDEquivZornSplitOctonion : SplitOctCD ≃ ZornSplitOctonion ℝ where
  toFun x :=
    let z := splitOctCDEquivZornMatrix x
    ⟨z.a, z.x, z.y, z.b⟩
  invFun w :=
    splitOctCDEquivZornMatrix.symm { a := w.a, b := w.b, x := w.u, y := w.v }
  left_inv x := by
    rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
    ext <;> dsimp <;> ring
  right_inv w := by
    rcases w with ⟨a, u, v, b⟩
    ext i
    · dsimp; ring
    · fin_cases i <;> dsimp <;> ring
    · fin_cases i <;> dsimp <;> ring
    · dsimp; ring

@[simp] theorem splitOctCDEquivZornSplitOctonion_apply (x : SplitOctCD) :
    splitOctCDEquivZornSplitOctonion x =
      ⟨(splitOctCDEquivZornMatrix x).a, (splitOctCDEquivZornMatrix x).x,
        (splitOctCDEquivZornMatrix x).y, (splitOctCDEquivZornMatrix x).b⟩ := rfl

@[simp] theorem splitOctCDEquivZornSplitOctonion_symm_apply (w : ZornSplitOctonion ℝ) :
    splitOctCDEquivZornSplitOctonion.symm w =
      splitOctCDEquivZornMatrix.symm { a := w.a, b := w.b, x := w.u, y := w.v } := rfl

theorem splitOctCDEquivZornSplitOctonion_zero :
    splitOctCDEquivZornSplitOctonion (0 : SplitOctCD) =
      (⟨0, fun _ => 0, fun _ => 0, 0⟩ : ZornSplitOctonion ℝ) := by
  apply ZornSplitOctonion.ext
  · simp
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp
  · simp

theorem splitOctCDEquivZornSplitOctonion_one :
    splitOctCDEquivZornSplitOctonion (1 : SplitOctCD) = (zornOne : ZornSplitOctonion ℝ) := by
  apply ZornSplitOctonion.ext
  · simp [zornOne]
  · funext i; fin_cases i <;> simp [zornOne]
  · funext i; fin_cases i <;> simp [zornOne]
  · simp [zornOne]

theorem splitOctCDEquivZornSplitOctonion_add (x y : SplitOctCD) :
    splitOctCDEquivZornSplitOctonion (x + y) =
      zornAdd (splitOctCDEquivZornSplitOctonion x) (splitOctCDEquivZornSplitOctonion y) := by
  apply ZornSplitOctonion.ext
  · simp [zornAdd]
    ring
  · funext i; fin_cases i <;> simp [zornAdd] <;> ring
  · funext i; fin_cases i <;> simp [zornAdd] <;> ring
  · simp [zornAdd]
    ring

theorem splitOctCDEquivZornSplitOctonion_smul (c : ℝ) (x : SplitOctCD) :
    splitOctCDEquivZornSplitOctonion (c • x) =
      zornSmul c (splitOctCDEquivZornSplitOctonion x) := by
  apply ZornSplitOctonion.ext
  · simp [zornSmul]
  · funext i; fin_cases i <;> simp [zornSmul]
  · funext i; fin_cases i <;> simp [zornSmul]
  · simp [zornSmul]

theorem splitOctCDEquivZornSplitOctonion_mul (x y : SplitOctCD) :
    splitOctCDEquivZornSplitOctonion (x * y) =
      zornMul (splitOctCDEquivZornSplitOctonion x) (splitOctCDEquivZornSplitOctonion y) := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  rcases y with ⟨⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
  ext i
  · simp [zornMul, vec3Dot]
    ring
  · fin_cases i <;> simp [zornMul, vec3Cross] <;> ring
  · fin_cases i <;> simp [zornMul, vec3Cross] <;> ring
  · simp [zornMul, vec3Dot]
    ring

theorem splitOctCDEquivZornSplitOctonion_norm (x : SplitOctCD) :
    zornNorm (splitOctCDEquivZornSplitOctonion x) = cdNorm x := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  simp [zornNorm, vec3Dot, cdNorm, Quaternion.normSq_def']
  ring

/-! ## Section 4: Left-Multiplication Operators, Polarized Left-Alternative Law, and `T` Bridge -/

/-- Left multiplication by `x` as an `ℝ`-linear endomorphism of `SplitOctCD`. -/
def leftMulEnd (x : SplitOctCD) : Module.End ℝ SplitOctCD where
  toFun z := x * z
  map_add' := cdMul_add_right x
  map_smul' c z := cdMul_smul_right c x z

/-- Left multiplication transported to `Fin 8 → ℝ` in the `[1, i₁, i₂, i₃, ℓ, s₁, s₂, s₃]` chart. -/
def leftMulFin8 (x : SplitOctCD) : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) :=
  (cdLinearEquivFin8.toLinearMap.comp (leftMulEnd x)).comp
    cdLinearEquivFin8.symm.toLinearMap

/-- Explicit `8 × 8` real matrix of left multiplication by `x` in `basisCD`. -/
def leftMulMat (x : SplitOctCD) : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) (leftMulFin8 x)

theorem leftMulEnd_add (x y : SplitOctCD) :
    leftMulEnd (x + y) = leftMulEnd x + leftMulEnd y := by
  apply LinearMap.ext
  intro z
  exact cdMul_add_left x y z

theorem leftMulEnd_smul (c : ℝ) (x : SplitOctCD) :
    leftMulEnd (c • x) = c • leftMulEnd x := by
  apply LinearMap.ext
  intro z
  exact cdMul_smul_left c x z

theorem leftMulEnd_zero : leftMulEnd (0 : SplitOctCD) = 0 := by
  apply LinearMap.ext
  intro z
  exact zero_cdMul z

theorem leftMulEnd_one : leftMulEnd (1 : SplitOctCD) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  exact one_cdMul z

theorem leftMulEnd_neg (x : SplitOctCD) : leftMulEnd (-x) = -leftMulEnd x := by
  apply LinearMap.ext
  intro z
  ext <;> simp [leftMulEnd]

theorem leftMulFin8_add (x y : SplitOctCD) :
    leftMulFin8 (x + y) = leftMulFin8 x + leftMulFin8 y := by
  apply LinearMap.ext
  intro v
  simp [leftMulFin8, leftMulEnd_add]

theorem leftMulFin8_smul (c : ℝ) (x : SplitOctCD) :
    leftMulFin8 (c • x) = c • leftMulFin8 x := by
  apply LinearMap.ext
  intro v
  simp [leftMulFin8, leftMulEnd_smul]

theorem leftMulFin8_zero : leftMulFin8 (0 : SplitOctCD) = 0 := by
  apply LinearMap.ext
  intro v
  simp [leftMulFin8, leftMulEnd_zero]

theorem leftMulFin8_one : leftMulFin8 (1 : SplitOctCD) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  change cdToFin8 ((1 : SplitOctCD) * fin8ToCD v) = v
  rw [one_cdMul]
  exact cdToFin8_fin8ToCD v

theorem leftMulFin8_neg (x : SplitOctCD) : leftMulFin8 (-x) = -leftMulFin8 x := by
  apply LinearMap.ext
  intro v
  simp [leftMulFin8, leftMulEnd_neg]

theorem leftMulMat_add (x y : SplitOctCD) :
    leftMulMat (x + y) = leftMulMat x + leftMulMat y := by
  unfold leftMulMat
  rw [leftMulFin8_add, map_add]

theorem leftMulMat_smul (c : ℝ) (x : SplitOctCD) :
    leftMulMat (c • x) = c • leftMulMat x := by
  unfold leftMulMat
  rw [leftMulFin8_smul, map_smul]

theorem leftMulMat_zero : leftMulMat (0 : SplitOctCD) = 0 := by
  unfold leftMulMat
  rw [leftMulFin8_zero, map_zero]

theorem leftMulMat_one : leftMulMat (1 : SplitOctCD) = 1 := by
  unfold leftMulMat
  rw [leftMulFin8_one, LinearMap.toMatrix_id]

theorem leftMulMat_neg (x : SplitOctCD) : leftMulMat (-x) = -leftMulMat x := by
  unfold leftMulMat
  rw [leftMulFin8_neg, map_neg]

/-- Left-alternative law on `SplitOctCD`: `x * (x * z) = (x * x) * z`. -/
theorem cdMul_left_alternative (x z : SplitOctCD) : x * (x * z) = (x * x) * z := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  rcases z with ⟨⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
  ext <;> simp <;> ring

/-- Polarized left-alternative identity on `SplitOctCD`:
`x * (y * z) + y * (x * z) = (x * y + y * x) * z`. -/
theorem cdMul_anticommutator (x y z : SplitOctCD) :
    x * (y * z) + y * (x * z) = (x * y + y * x) * z := by
  rcases x with ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩
  rcases y with ⟨⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
  rcases z with ⟨⟨e0, e1, e2, e3⟩, ⟨f0, f1, f2, f3⟩⟩
  ext <;> simp <;> ring

theorem leftMulEnd_anticommutator (x y : SplitOctCD) :
    leftMulEnd x * leftMulEnd y + leftMulEnd y * leftMulEnd x =
      leftMulEnd (x * y + y * x) := by
  apply LinearMap.ext
  intro z
  exact cdMul_anticommutator x y z

theorem leftMulEnd_sq (x : SplitOctCD) :
    leftMulEnd x * leftMulEnd x = leftMulEnd (x * x) := by
  apply LinearMap.ext
  intro z
  exact cdMul_left_alternative x z

theorem leftMulFin8_anticommutator (x y : SplitOctCD) :
    leftMulFin8 x * leftMulFin8 y + leftMulFin8 y * leftMulFin8 x =
      leftMulFin8 (x * y + y * x) := by
  apply LinearMap.ext
  intro v
  dsimp [leftMulFin8, leftMulEnd, Module.End.mul_apply]
  simp only [fin8ToCD_cdToFin8]
  change cdLinearEquivFin8 (x * (y * fin8ToCD v)) +
      cdLinearEquivFin8 (y * (x * fin8ToCD v)) =
    cdLinearEquivFin8 ((x * y + y * x) * fin8ToCD v)
  rw [← cdLinearEquivFin8.map_add]
  exact congrArg cdLinearEquivFin8 (cdMul_anticommutator x y (fin8ToCD v))

theorem leftMulFin8_sq (x : SplitOctCD) :
    leftMulFin8 x * leftMulFin8 x = leftMulFin8 (x * x) := by
  apply LinearMap.ext
  intro v
  dsimp [leftMulFin8, leftMulEnd, Module.End.mul_apply]
  simp only [fin8ToCD_cdToFin8]
  change cdLinearEquivFin8 (x * (x * fin8ToCD v)) =
    cdLinearEquivFin8 ((x * x) * fin8ToCD v)
  exact congrArg cdLinearEquivFin8 (cdMul_left_alternative x (fin8ToCD v))

/-- Polarized left-alternative law on `8 × 8` real matrices:
`L_x L_y + L_y L_x = L_{xy+yx}`. -/
theorem leftMulMat_anticommutator (x y : SplitOctCD) :
    leftMulMat x * leftMulMat y + leftMulMat y * leftMulMat x =
      leftMulMat (x * y + y * x) := by
  unfold leftMulMat
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, ← map_add,
    leftMulFin8_anticommutator]

/-- Left-alternative squaring law on `8 × 8` real matrices: `L_x^2 = L_{x^2}`. -/
theorem leftMulMat_sq (x : SplitOctCD) :
    leftMulMat x * leftMulMat x = leftMulMat (x * x) := by
  unfold leftMulMat
  rw [← LinearMap.toMatrix_mul, leftMulFin8_sq]

/-- Linear intertwiner mapping `[1, i₁, i₂, i₃, ℓ, s₁, s₂, s₃]` coordinates `Fin 8 → ℝ`
to the Zorn Fock chart `Fin 8 → ℝ` of `SplitOctonionClifford33Soldering`. -/
def cdToZornFin8 : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun v := zornToFin8 (splitOctCDEquivZornSplitOctonion (fin8ToCD v))
  map_add' v w := by
    have ha : fin8ToCD (v + w) = fin8ToCD v + fin8ToCD w := cdLinearEquivFin8.symm.map_add v w
    rw [ha, splitOctCDEquivZornSplitOctonion_add, zornToFin8_zornAdd]
    rfl
  map_smul' c v := by
    have hs : fin8ToCD (c • v) = c • fin8ToCD v := cdLinearEquivFin8.symm.map_smul c v
    rw [hs, splitOctCDEquivZornSplitOctonion_smul, zornToFin8_zornSmul]
    rfl

/-- Inverse linear intertwiner from the Zorn Fock chart to `1 + 3 + 1 + 3` coordinates. -/
def zornToCDFin8 : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun ψ := cdToFin8 (splitOctCDEquivZornSplitOctonion.symm (fin8ToZorn ψ))
  map_add' ψ φ := by
    have ha : splitOctCDEquivZornSplitOctonion.symm (zornAdd (fin8ToZorn ψ) (fin8ToZorn φ)) =
        splitOctCDEquivZornSplitOctonion.symm (fin8ToZorn ψ) +
          splitOctCDEquivZornSplitOctonion.symm (fin8ToZorn φ) := by
      apply splitOctCDEquivZornSplitOctonion.injective
      rw [splitOctCDEquivZornSplitOctonion_add]
      apply ZornSplitOctonion.ext
      · simp [zornAdd]
        ring
      · funext i; fin_cases i <;> simp [zornAdd] <;> ring
      · funext i; fin_cases i <;> simp [zornAdd] <;> ring
      · simp [zornAdd]
        ring
    rw [fin8ToZorn_add, ha]
    exact cdLinearEquivFin8.map_add _ _
  map_smul' c ψ := by
    have hs : splitOctCDEquivZornSplitOctonion.symm (zornSmul c (fin8ToZorn ψ)) =
        c • splitOctCDEquivZornSplitOctonion.symm (fin8ToZorn ψ) := by
      apply splitOctCDEquivZornSplitOctonion.injective
      rw [splitOctCDEquivZornSplitOctonion_smul]
      apply ZornSplitOctonion.ext
      · simp [zornSmul]
        ring
      · funext i; fin_cases i <;> simp [zornSmul] <;> ring
      · funext i; fin_cases i <;> simp [zornSmul] <;> ring
      · simp [zornSmul]
        ring
    rw [fin8ToZorn_smul, hs]
    exact cdLinearEquivFin8.map_smul _ _

theorem cdToZornFin8_comp_zornToCDFin8 :
    cdToZornFin8.comp zornToCDFin8 = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext i
  fin_cases i <;>
    simp [cdToZornFin8, zornToCDFin8, zornToFin8, fin8ToZorn] <;> ring

theorem zornToCDFin8_comp_cdToZornFin8 :
    zornToCDFin8.comp cdToZornFin8 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  change cdLinearEquivFin8 (splitOctCDEquivZornSplitOctonion.symm
    (fin8ToZorn (zornToFin8 (splitOctCDEquivZornSplitOctonion
      (cdLinearEquivFin8.symm v))))) = v
  rw [fin8ToZorn_right_inv]
  simp [cdToFin8, fin8ToCD]
  funext i
  fin_cases i <;> simp <;> ring

/-- Explicit `8 × 8` change-of-basis matrix `T` from `[1, i₁, i₂, i₃, ℓ, s₁, s₂, s₃]`
to the Zorn Fock chart `zornToFin8`. -/
def cdToZornMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1,  0,  0,  0,  1,  0,  0,  0;
     0,  0,  0, -1,  0,  0,  0, -1;
     0,  0, -1,  0,  0,  0, -1,  0;
     0,  1,  0,  0,  0, -1,  0,  0;
     0, -1,  0,  0,  0, -1,  0,  0;
     0,  0, -1,  0,  0,  0,  1,  0;
     0,  0,  0,  1,  0,  0,  0, -1;
     1,  0,  0,  0, -1,  0,  0,  0]

/-- Explicit inverse `8 × 8` change-of-basis matrix `P = T⁻¹ = (1/2) Tᵀ`. -/
def zornToCDMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  (1 / 2 : ℝ) • cdToZornMatrixᵀ

theorem cdToZornMatrix_def :
    cdToZornMatrix =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) cdToZornFin8 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cdToZornMatrix, cdToZornFin8, zornToFin8,
      fin8ToCD, LinearMap.toMatrix_apply, Pi.basisFun_apply,
      Pi.basisFun_repr, Pi.single_apply]

theorem zornToCDMatrix_def :
    zornToCDMatrix =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) zornToCDFin8 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zornToCDMatrix, cdToZornMatrix, zornToCDFin8, cdToFin8,
      fin8ToZorn, LinearMap.toMatrix_apply, Pi.basisFun_apply,
      Pi.basisFun_repr, Pi.single_apply]

theorem zornToCDMatrix_mul_cdToZornMatrix :
    zornToCDMatrix * cdToZornMatrix = (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [zornToCDMatrix_def, cdToZornMatrix_def, ← LinearMap.toMatrix_mul]
  change LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (zornToCDFin8.comp cdToZornFin8) = 1
  rw [zornToCDFin8_comp_cdToZornFin8, LinearMap.toMatrix_id]

theorem cdToZornMatrix_mul_zornToCDMatrix :
    cdToZornMatrix * zornToCDMatrix = (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [cdToZornMatrix_def, zornToCDMatrix_def, ← LinearMap.toMatrix_mul]
  change LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8))
    (cdToZornFin8.comp zornToCDFin8) = 1
  rw [cdToZornFin8_comp_zornToCDFin8, LinearMap.toMatrix_id]

private def detRowPerm : Equiv.Perm (Fin 8) where
  toFun
    | 0 => 0
    | 1 => 3
    | 2 => 2
    | 3 => 1
    | 4 => 7
    | 5 => 4
    | 6 => 5
    | 7 => 6
  invFun
    | 0 => 0
    | 1 => 3
    | 2 => 2
    | 3 => 1
    | 4 => 5
    | 5 => 6
    | 6 => 7
    | 7 => 4
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem detRowPerm_sign : Equiv.Perm.sign detRowPerm = 1 := by
  have h : detRowPerm = Equiv.swap (1 : Fin 8) 3 *
      (Equiv.swap (4 : Fin 8) 7 * Equiv.swap 7 6 * Equiv.swap 6 5) := by
    ext i
    fin_cases i <;> rfl
  rw [h, map_mul, map_mul, map_mul]
  have h13 : (1 : Fin 8) ≠ 3 := by decide
  have h47 : (4 : Fin 8) ≠ 7 := by decide
  have h76 : (7 : Fin 8) ≠ 6 := by decide
  have h65 : (6 : Fin 8) ≠ 5 := by decide
  simp [Equiv.Perm.sign_swap h13, Equiv.Perm.sign_swap h47,
    Equiv.Perm.sign_swap h76, Equiv.Perm.sign_swap h65]

private def detElimL : Matrix (Fin 8) (Fin 8) ℝ :=
  !![ 1, 0,  0, 0, 0, 0, 0, 0;
      0, 1,  0, 0, 0, 0, 0, 0;
      0, 0,  1, 0, 0, 0, 0, 0;
      0, 0,  0, 1, 0, 0, 0, 0;
     -1, 0,  0, 0, 1, 0, 0, 0;
      0, 1,  0, 0, 0, 1, 0, 0;
      0, 0, -1, 0, 0, 0, 1, 0;
      0, 0,  0, 1, 0, 0, 0, 1]

private def detUpperU : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 0,  0,  0,  1,  0,  0,  0;
     0, 1,  0,  0,  0, -1,  0,  0;
     0, 0, -1,  0,  0,  0, -1,  0;
     0, 0,  0, -1,  0,  0,  0, -1;
     0, 0,  0,  0, -2,  0,  0,  0;
     0, 0,  0,  0,  0, -2,  0,  0;
     0, 0,  0,  0,  0,  0,  2,  0;
     0, 0,  0,  0,  0,  0,  0, -2]

/-- Exact determinant `det T = -16` of the `8 × 8` Cayley–Dickson-to-Zorn intertwiner. -/
theorem cdToZornMatrix_det : Matrix.det cdToZornMatrix = -16 := by
  have hperm : Matrix.det (cdToZornMatrix.submatrix detRowPerm id) = Matrix.det cdToZornMatrix := by
    rw [Matrix.det_permute, detRowPerm_sign]
    simp
  have hLU : detElimL * cdToZornMatrix.submatrix detRowPerm id = detUpperU := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [detElimL, cdToZornMatrix, detUpperU, detRowPerm,
        Matrix.mul_apply, Fin.sum_univ_succ]
  have hL_tri : detElimL.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    fin_cases i <;> fin_cases j <;> simp_all [detElimL]
  have hU_tri : detUpperU.IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    fin_cases i <;> fin_cases j <;> simp_all [detUpperU]
  have hL_det : Matrix.det detElimL = 1 := by
    rw [Matrix.det_of_isLowerTriangular detElimL hL_tri]
    norm_num [detElimL, Fin.prod_univ_succ]
  have hU_det : Matrix.det detUpperU = -16 := by
    rw [Matrix.det_of_isUpperTriangular hU_tri]
    norm_num [detUpperU, Fin.prod_univ_succ]
  have hmul := congrArg Matrix.det hLU
  rw [Matrix.det_mul, hL_det, one_mul, hperm, hU_det] at hmul
  exact hmul

/-- Intertwining identity `T * L_x = zornLeftActMatrix (Φ x) * T` linking `leftMulMat`
with `SplitOctonionClifford33Soldering.zornLeftActMatrix`. -/
theorem leftMulMat_intertwines_zornLeftActMatrix (x : SplitOctCD) :
    cdToZornMatrix * leftMulMat x =
      zornLeftActMatrix (splitOctCDEquivZornSplitOctonion x) * cdToZornMatrix := by
  rw [cdToZornMatrix_def]
  unfold leftMulMat zornLeftActMatrix
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  apply LinearMap.ext
  intro v
  change cdToZornFin8 (leftMulFin8 x v) =
    zornLeftActFin8 (splitOctCDEquivZornSplitOctonion x) (cdToZornFin8 v)
  funext i
  fin_cases i <;>
    simp [cdToZornFin8, leftMulFin8, leftMulEnd, zornLeftActFin8,
      fin8ToCD_cdToFin8, zornToFin8, fin8ToZorn, zornMul, vec3Dot, vec3Cross] <;> ring

/-- Conjugation formula `L_x = P * zornLeftActMatrix (Φ x) * T`. -/
theorem leftMulMat_conj_zornLeftActMatrix (x : SplitOctCD) :
    leftMulMat x =
      zornToCDMatrix * zornLeftActMatrix (splitOctCDEquivZornSplitOctonion x) * cdToZornMatrix := by
  have h := congrArg (fun M => zornToCDMatrix * M) (leftMulMat_intertwines_zornLeftActMatrix x)
  simpa [← Matrix.mul_assoc, zornToCDMatrix_mul_cdToZornMatrix] using h

/-- Direct `zornLeftActMatrix` polarized left-alternative anticommutator transported from
`leftMulMat_anticommutator` via the invertible intertwiner `T` / `P`. -/
theorem zornLeftActMatrix_anticommutator_cd (x y : SplitOctCD) :
    zornLeftActMatrix (splitOctCDEquivZornSplitOctonion x) *
        zornLeftActMatrix (splitOctCDEquivZornSplitOctonion y) +
      zornLeftActMatrix (splitOctCDEquivZornSplitOctonion y) *
        zornLeftActMatrix (splitOctCDEquivZornSplitOctonion x) =
      zornLeftActMatrix (splitOctCDEquivZornSplitOctonion (x * y + y * x)) := by
  have hxy : zornLeftActMatrix (splitOctCDEquivZornSplitOctonion x) =
      cdToZornMatrix * leftMulMat x * zornToCDMatrix := by
    have h := congrArg (fun M => M * zornToCDMatrix) (leftMulMat_intertwines_zornLeftActMatrix x)
    simpa [Matrix.mul_assoc, cdToZornMatrix_mul_zornToCDMatrix] using h.symm
  have hyx : zornLeftActMatrix (splitOctCDEquivZornSplitOctonion y) =
      cdToZornMatrix * leftMulMat y * zornToCDMatrix := by
    have h := congrArg (fun M => M * zornToCDMatrix) (leftMulMat_intertwines_zornLeftActMatrix y)
    simpa [Matrix.mul_assoc, cdToZornMatrix_mul_zornToCDMatrix] using h.symm
  have hsum : zornLeftActMatrix (splitOctCDEquivZornSplitOctonion (x * y + y * x)) =
      cdToZornMatrix * leftMulMat (x * y + y * x) * zornToCDMatrix := by
    have h := congrArg (fun M => M * zornToCDMatrix)
      (leftMulMat_intertwines_zornLeftActMatrix (x * y + y * x))
    simpa [Matrix.mul_assoc, cdToZornMatrix_mul_zornToCDMatrix] using h.symm
  rw [hxy, hyx, hsum, ← leftMulMat_anticommutator x y]
  have hprod1 :
      (cdToZornMatrix * leftMulMat x * zornToCDMatrix) *
          (cdToZornMatrix * leftMulMat y * zornToCDMatrix) =
        cdToZornMatrix * (leftMulMat x * leftMulMat y) * zornToCDMatrix := by
    calc
      (cdToZornMatrix * leftMulMat x * zornToCDMatrix) *
          (cdToZornMatrix * leftMulMat y * zornToCDMatrix)
          = cdToZornMatrix * leftMulMat x * (zornToCDMatrix * cdToZornMatrix) *
              leftMulMat y * zornToCDMatrix := by simp [Matrix.mul_assoc]
      _ = cdToZornMatrix * (leftMulMat x * leftMulMat y) * zornToCDMatrix := by
          rw [zornToCDMatrix_mul_cdToZornMatrix]; simp [Matrix.mul_assoc]
  have hprod2 :
      (cdToZornMatrix * leftMulMat y * zornToCDMatrix) *
          (cdToZornMatrix * leftMulMat x * zornToCDMatrix) =
        cdToZornMatrix * (leftMulMat y * leftMulMat x) * zornToCDMatrix := by
    calc
      (cdToZornMatrix * leftMulMat y * zornToCDMatrix) *
          (cdToZornMatrix * leftMulMat x * zornToCDMatrix)
          = cdToZornMatrix * leftMulMat y * (zornToCDMatrix * cdToZornMatrix) *
              leftMulMat x * zornToCDMatrix := by simp [Matrix.mul_assoc]
      _ = cdToZornMatrix * (leftMulMat y * leftMulMat x) * zornToCDMatrix := by
          rw [zornToCDMatrix_mul_cdToZornMatrix]; simp [Matrix.mul_assoc]
  rw [hprod1, hprod2, ← Matrix.add_mul, ← Matrix.mul_add]

/-! ## Section 5: Seven Anticommuting `8 × 8` Operators with Squares `(-1)^3 (+1)^4` -/

/-- The seven generators `[i₁, i₂, i₃, ℓ, s₁, s₂, s₃]` of `SplitOctCD`. -/
def sevenAnticommGen : Fin 7 → SplitOctCD
  | 0 => iCD 0
  | 1 => iCD 1
  | 2 => iCD 2
  | 3 => ellCD
  | 4 => sCD 0
  | 5 => sCD 1
  | 6 => sCD 2

/-- Signature `(-1, -1, -1, +1, +1, +1, +1)` of the squares of the seven generators. -/
def sevenAnticommSig : Fin 7 → ℝ
  | 0 => -1
  | 1 => -1
  | 2 => -1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1

theorem sevenAnticommGen_sq (a : Fin 7) :
    sevenAnticommGen a * sevenAnticommGen a = sevenAnticommSig a • (1 : SplitOctCD) := by
  fin_cases a <;>
    simp [sevenAnticommGen, sevenAnticommSig, iCD_sq, ellCD_sq, sCD_sq,
      oneCD, oneCD_def]

theorem sevenAnticommGen_anticomm {a b : Fin 7} (hab : a ≠ b) :
    sevenAnticommGen a * sevenAnticommGen b + sevenAnticommGen b * sevenAnticommGen a = 0 := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact absurd rfl hab
    | (ext <;> simp [sevenAnticommGen, iCD, ellCD, sCD_formula, qBasis])

/-- The seven `8 × 8` real left-multiplication matrices
`{L_{i₁}, L_{i₂}, L_{i₃}, L_ℓ, L_{s₁}, L_{s₂}, L_{s₃}}`. -/
def sevenAnticommOps (a : Fin 7) : Matrix (Fin 8) (Fin 8) ℝ :=
  leftMulMat (sevenAnticommGen a)

/-- All 21 distinct pairs among the seven `8 × 8` operators anticommute: `L_a L_b + L_b L_a = 0`. -/
theorem sevenAnticommOps_anticomm {a b : Fin 7} (hab : a ≠ b) :
    sevenAnticommOps a * sevenAnticommOps b +
      sevenAnticommOps b * sevenAnticommOps a = 0 := by
  unfold sevenAnticommOps
  rw [leftMulMat_anticommutator, sevenAnticommGen_anticomm hab, leftMulMat_zero]

/-- Squares of the seven `8 × 8` operators: `(-I₈, -I₈, -I₈, +I₈, +I₈, +I₈, +I₈)`. -/
theorem sevenAnticommOps_sq (a : Fin 7) :
    sevenAnticommOps a * sevenAnticommOps a =
      sevenAnticommSig a • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  unfold sevenAnticommOps
  rw [leftMulMat_sq, sevenAnticommGen_sq, leftMulMat_smul, leftMulMat_one]

/-! ## Section 6: Non-Commutativity and Non-Associativity Witnesses (Trap T16) -/

/-- Closed non-commutativity witness for `Quaternion ℝ`. -/
theorem quaternion_noncommutative : ∃ p q : Quaternion ℝ, p * q ≠ q * p := by
  refine ⟨qBasis 0, qBasis 1, ?_⟩
  intro h
  have hk := congrArg (fun r : Quaternion ℝ => r.imK) h
  norm_num [qBasis] at hk

/-- Closed non-commutativity witness for `SplitOctCD`. -/
theorem splitOctCD_noncommutative : ∃ x y : SplitOctCD, x * y ≠ y * x := by
  refine ⟨iCD 0, iCD 1, ?_⟩
  intro h
  have hk := congrArg (fun r : SplitOctCD => r.fst.imK) h
  norm_num [iCD, qBasis] at hk

/-- Explicit non-associativity witness on `SplitOctCD`: `(i₁ * i₂) * ℓ ≠ i₁ * (i₂ * ℓ)`. -/
theorem splitOctCD_nonassociative :
    (iCD 0 * iCD 1) * ellCD ≠ iCD 0 * (iCD 1 * ellCD) := by
  intro h
  have hk := congrArg (fun r : SplitOctCD => r.snd.imK) h
  norm_num [iCD, ellCD, qBasis] at hk

/-- Closed non-commutativity witness for `Module.End ℝ SplitOctCD`. -/
theorem leftMulEnd_noncommutative : ∃ A B : Module.End ℝ SplitOctCD, A * B ≠ B * A := by
  refine ⟨leftMulEnd (iCD 0), leftMulEnd (iCD 1), ?_⟩
  intro h
  have h1 := congrArg (fun f : Module.End ℝ SplitOctCD => (f (1 : SplitOctCD)).fst.imK) h
  norm_num [leftMulEnd, Module.End.mul_apply, iCD, qBasis] at h1

/-- Closed non-commutativity witness for `(Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)`. -/
theorem leftMulFin8_noncommutative :
    ∃ A B : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ), A * B ≠ B * A := by
  refine ⟨leftMulFin8 (iCD 0), leftMulFin8 (iCD 1), ?_⟩
  intro h
  have h1 := congrArg
    (fun f : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) => (f (Pi.single 0 1)) 3) h
  simp [leftMulFin8, leftMulEnd, Module.End.mul_apply, cdToFin8,
    fin8ToCD, iCD, qBasis] at h1
  norm_num at h1

/-- Nullary `8 × 8` matrix for `L_{i₁}`. -/
def leftMulI1Mat : Matrix (Fin 8) (Fin 8) ℝ := leftMulMat (iCD 0)

/-- Nullary `8 × 8` matrix for `L_{i₂}`. -/
def leftMulI2Mat : Matrix (Fin 8) (Fin 8) ℝ := leftMulMat (iCD 1)

/-- Closed bare-identifier non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem leftMulMat_noncommutative :
    leftMulI1Mat * leftMulI2Mat ≠ leftMulI2Mat * leftMulI1Mat := by
  intro h
  have h' : leftMulFin8 (iCD 0) * leftMulFin8 (iCD 1) =
      leftMulFin8 (iCD 1) * leftMulFin8 (iCD 0) := by
    let T := LinearMap.toMatrix (Pi.basisFun ℝ (Fin 8))
      (Pi.basisFun ℝ (Fin 8))
    have hm : T (leftMulFin8 (iCD 0) * leftMulFin8 (iCD 1)) =
        T (leftMulFin8 (iCD 1) * leftMulFin8 (iCD 0)) := by
      rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]
      simpa [T, leftMulI1Mat, leftMulI2Mat, leftMulMat] using h
    exact T.injective hm
  have hv := congrArg (fun f => f (cdToFin8 (1 : SplitOctCD))) h'
  norm_num [leftMulFin8, leftMulEnd, cdToFin8, fin8ToCD, iCD, qBasis] at hv

/-- Existential non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℝ`. -/
theorem matrix8_noncommutative : ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A :=
  ⟨leftMulI1Mat, leftMulI2Mat, leftMulMat_noncommutative⟩

/-- Nullary `ZornMatrix ℝ` element corresponding to `i₁`. -/
def zornI1 : InfoGeometry.Canonical.ZornMatrix ℝ := splitOctCDEquivZornMatrix (iCD 0)

/-- Nullary `ZornMatrix ℝ` element corresponding to `i₂`. -/
def zornI2 : InfoGeometry.Canonical.ZornMatrix ℝ := splitOctCDEquivZornMatrix (iCD 1)

/-- Closed non-commutativity witness for `InfoGeometry.Canonical.ZornMatrix ℝ`. -/
theorem zornMatrix_noncommutative : zornI1 * zornI2 ≠ zornI2 * zornI1 := by
  intro h
  rw [zornI1, zornI2, ← splitOctCDEquivZornMatrix_mul, ← splitOctCDEquivZornMatrix_mul] at h
  have hij := splitOctCDEquivZornMatrix.injective h
  rw [iCD_mul_01, iCD_mul_10] at hij
  have hk := congrArg (fun r : SplitOctCD => r.fst.imK) hij
  norm_num [iCD, qBasis] at hk

end InfoGeometry.Canonical.SplitOctonionCayleyDickson
